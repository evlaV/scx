// Copyright (c) Facebook, Inc. and its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::time::Duration;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use anyhow::anyhow;
use anyhow::bail;
use anyhow::Result;

use crate::dateutil;
use crate::util;

const MISSING_SAMPLE_WARN_DURATION_S: u64 = 60;

/// Convert from date to `SystemTime`
pub fn system_time_from_date(date: &str) -> Result<SystemTime> {
    Ok(UNIX_EPOCH
    + Duration::from_secs(
        dateutil::HgTime::parse(date)
            .ok_or_else(|| {
                anyhow!(
                    "Unrecognized timestamp format\n\
                Input: {}.\n\
                Examples:\n\t\
                Keywords: now, today, yesterday\n\t\
                Relative: \"{{humantime}} ago\", e.g. 2 days 3 hr 15m 10sec ago\n\t\
                Relative short: Mixed {{time_digit}}{{time_unit_char}}. E.g. 10m, 3d2H, 5h30s, 10m5h\n\t\
                Absolute: \"Jan 01 23:59\", \"01/01/1970 11:59PM\", \"1970-01-01 23:59:59\"\n\t\
                Unix Epoch: 1589808367",
                    &date
                )
            })?
            .unixtime,
    ))
}

/// Convert from date and an optional days adjuster to `SystemTime`. Days
/// adjuster is of form y[y...] to `SystemTime`. Each "y" will deduct 1 day
/// from the resulting time.
pub fn system_time_from_date_and_adjuster(
    date: &str,
    days_adjuster: Option<&str>,
) -> Result<SystemTime> {
    let mut time = system_time_from_date(date)?;
    if let Some(days) = days_adjuster {
        if days.is_empty() || days.find(|c: char| c != 'y').is_some() {
            bail!("Unrecognized days adjuster format: {}", days);
        }
        let time_to_deduct = Duration::from_secs(days.chars().count() as u64 * 86400);
        time -= time_to_deduct;
    }
    Ok(time)
}

/// Convert from date range and an optional days adjuster to a start and end
/// `SystemTime`. Days adjuster is of form y[y...]. Each "y" will deduct 1 day
/// from the resulting time.
pub fn system_time_range_from_date_and_adjuster(
    start_date: &str,
    end_date: Option<&str>,
    duration_str: Option<&str>,
    days_adjuster: Option<&str>,
) -> Result<(SystemTime, SystemTime)> {
    let start = system_time_from_date_and_adjuster(start_date, days_adjuster)?;
    let end = match (end_date, duration_str) {
        (Some(_), Some(_)) => {
            bail!("--end and --duration are incompatible options")
        }
        (Some(end_date), None) => system_time_from_date_and_adjuster(end_date, days_adjuster)?,
        (None, Some(duration_str)) => duration_str
            .parse::<humantime::Duration>()
            .ok()
            .map(|duration: humantime::Duration| start + Into::<Duration>::into(duration))
            .unwrap(),
        _ => SystemTime::now(),
    };

    Ok((start, end))
}

/// Check that initial sample time is within `MISSING_SAMPLE_WARN_DURATION_S`
/// seconds of the requested start time.
pub fn check_initial_sample_time_with_requested_time(
    initial_sample_time: SystemTime,
    time_begin: SystemTime,
) {
    if initial_sample_time > time_begin + Duration::from_secs(MISSING_SAMPLE_WARN_DURATION_S) {
        eprintln!(
            "Warning: Initial sample found at {} which is over {} seconds \
            after the requested start time of {}",
            util::systemtime_to_datetime(initial_sample_time),
            MISSING_SAMPLE_WARN_DURATION_S,
            util::systemtime_to_datetime(time_begin),
        );
    };
}

/// Check that initial sample time is within `MISSING_SAMPLE_WARN_DURATION_S`
/// seconds of the requested start time, and is not after the requested end time.
pub fn check_initial_sample_time_in_time_range(
    initial_sample_time: SystemTime,
    time_begin: SystemTime,
    time_end: SystemTime,
) -> Result<()> {
    if initial_sample_time > time_end {
        bail!(
            "No samples found in desired time range.\n\
            Earliest sample found after {} is at {} which is after the \
            requested end time of {}",
            util::systemtime_to_datetime(time_begin),
            util::systemtime_to_datetime(initial_sample_time),
            util::systemtime_to_datetime(time_end),
        );
    }
    check_initial_sample_time_with_requested_time(initial_sample_time, time_begin);
    Ok(())
}

/// Check that final sample time is within `MISSING_SAMPLE_WARN_DURATION_S`
/// seconds of the requested end time.
pub fn check_final_sample_time_with_requested_time(
    final_sample_time: SystemTime,
    time_end: SystemTime,
) {
    if final_sample_time < time_end - Duration::from_secs(MISSING_SAMPLE_WARN_DURATION_S) {
        eprintln!(
            "Warning: Final sample processed was for {} which is over {} \
            seconds before the requested end time of {}",
            util::systemtime_to_datetime(final_sample_time),
            MISSING_SAMPLE_WARN_DURATION_S,
            util::systemtime_to_datetime(time_end),
        );
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_system_time_from_date_fail() {
        if system_time_from_date("invalid").is_ok() {
            panic!("Expected to fail but didn't")
        }
    }

    #[test]
    fn test_system_time_from_date_and_adjuster() {
        assert_eq!(
            system_time_from_date_and_adjuster("2006-02-01 13:00:30 UTC", None).unwrap(),
            t("2006-02-01 13:00:30 UTC")
        );
        assert_eq!(
            system_time_from_date_and_adjuster("2006-02-01 13:00:30 UTC", Some("y")).unwrap(),
            t("2006-01-31 13:00:30 UTC")
        );
        assert_eq!(
            system_time_from_date_and_adjuster("2006-02-01 13:00:30 UTC", Some("yy")).unwrap(),
            t("2006-01-30 13:00:30 UTC")
        );
        assert_eq!(
            system_time_from_date_and_adjuster("2006-02-01 13:00:30 UTC", Some("yyy")).unwrap(),
            t("2006-01-29 13:00:30 UTC")
        );
    }

    #[test]
    fn test_system_time_from_date_and_adjuster_fail() {
        if system_time_from_date_and_adjuster("2006-02-01 13:00:30 UTC", Some("invalid")).is_ok() {
            panic!("Expected fo fail as adjuster is invalid")
        }
    }

    #[test]
    fn test_system_time_range_from_date_and_adjuster() {
        assert_eq!(
            system_time_range_from_date_and_adjuster(
                "2006-02-01 13:00:30 UTC",
                Some("2006-02-01 15:00:30 UTC"),
                None,
                Some("y"),
            )
            .unwrap(),
            (t("2006-01-31 13:00:30 UTC"), t("2006-01-31 15:00:30 UTC"))
        );
        assert_eq!(
            system_time_range_from_date_and_adjuster(
                "2006-02-01 13:00:30 UTC",
                None,
                Some("10min"),
                Some("y"),
            )
            .unwrap(),
            (t("2006-01-31 13:00:30 UTC"), t("2006-01-31 13:10:30 UTC"))
        );
    }

    /// Convert date to `SystemTime`
    fn t(h: &str) -> SystemTime {
        system_time_from_date(h).unwrap()
    }
}
