use core::time::Duration;
use std::{thread, time::SystemTime};

/// `TimeInterval` enables you to wait for regular `intervals`
/// no matter how long your task already took.
///
/// A `tick()` always waits at least until `last_interval_start + interval`.
///
/// Depending on your wanted `overrun_behavior` it can react differently
/// to interval overrun situations.
///
/// Example:
///
/// ```
/// use std::time::{Duration, SystemTime};
/// use rhythmic;
///
/// let interval = Duration::from_millis(10);
/// let mut time_interval = rhythmic::TimeInterval::new(interval);
/// // first tick() returns immediately
/// time_interval.tick();
/// let pre = SystemTime::now();
/// // second tick() returns after the interval
/// time_interval.tick();
/// let post = SystemTime::now();
/// assert_eq!(post.duration_since(pre).unwrap().as_millis(), interval.as_millis());
/// ```
#[derive(Debug)]
pub struct TimeInterval {
    /// the interval that `tick()` waits for
    interval: Duration,
    /// the base time for the next iteration. next tick() should wait until
    /// `last_interval_start + interval`
    last_interval_start: Option<SystemTime>,
    /// how long was the last sleep duration
    last_sleep_duration: Option<Duration>,
    /// the overrun behavior
    overrun_behavior: OverrunBehavior,
}

/// The behavior that should be used in case of an interval overrun
#[derive(Debug, Default)]
pub enum OverrunBehavior {
    #[default]
    /// wait for the next regular interval start to keep work starting evenly spaced
    AwaitNextInterval,
    /// wait for the specified interval and adjust the regular run time accordingly.
    /// This keeps work separated by at least the interval
    WaitInterval,
    /// don't wait for the next regular interval but return immediately and keep the previous spacing
    ImmediateReturn,
}

impl TimeInterval {
    /// create a new time interval with the default behavior
    #[must_use]
    pub fn new(interval: Duration) -> Self {
        Self {
            interval,
            last_interval_start: None,
            last_sleep_duration: None,
            overrun_behavior: OverrunBehavior::default(),
        }
    }

    /// configure a new `interval`
    #[must_use]
    pub fn with_interval(mut self, interval: Duration) -> Self {
        self.interval = interval;
        self
    }

    /// configure an `overrun_behavior`
    #[must_use]
    pub fn with_behavior(mut self, overrun_behavior: OverrunBehavior) -> Self {
        self.overrun_behavior = overrun_behavior;
        self
    }

    /// The given `value` is rounded to the next smaller intervall start on a microsecond resolution
    ///
    /// `Duration(result_us) = value_us // interval_us * interval_us`
    ///
    /// Example:
    /// ```ignore
    /// use std::time::Duration;
    /// use rhythmic::TimeInterval;
    /// let value = Duration::from_secs(123);
    /// let interval = Duration::from_secs(10);
    /// assert_eq!(TimeInterval::round_to_interval_start(value, interval), Duration::from_secs(120));
    /// ```
    fn round_to_interval_start(value: Duration, interval: Duration) -> Duration {
        let value_us = value.as_micros();
        let interval_us = interval.as_micros();
        let interval_start = value_us / interval_us * interval_us;
        Duration::from_micros(
            interval_start
                .try_into()
                .expect("duration in us is too big"),
        )
    }

    /// calculate the biggest time that fulfills
    /// `previous_interval_start = interval_start + n * interval <= now` for some `n`.
    ///
    /// This should only be called if `interval_start` < `now`
    ///
    /// Example:
    /// ```ignore
    /// use std::time::{Duration, SystemTime};
    /// use rhythmic::TimeInterval;
    /// let interval_start = SystemTime::UNIX_EPOCH;
    /// let interval = Duration::from_secs(2);
    /// let now = interval_start + Duration::from_secs(5);
    /// assert_eq!(TimeInterval::previous_interval_start(interval_start, now, interval),
    ///            SystemTime::UNIX_EPOCH + Duration::from_secs(4));
    /// ```
    fn previous_interval_start(
        interval_start: SystemTime,
        now: SystemTime,
        interval: Duration,
    ) -> SystemTime {
        let duration_since_interval_start = now
            .duration_since(interval_start)
            .expect("interval_start <= now");

        // due to the way this is calculated this is guaranteed to be >= now
        // (earlier) next_interval_start + (duration_since_interval_start // interval * interval)
        // should be the last possible previous interval start
        let aligned_duration_since_interval_start =
            Self::round_to_interval_start(duration_since_interval_start, interval);
        let previous_interval_start = interval_start + aligned_duration_since_interval_start;
        debug_assert!(previous_interval_start <= now);
        previous_interval_start
    }

    /// Calculate how much time is left in this tick and when the next `last_interval_start`
    /// should be according to the overrun behavior. This always returns a
    ///   - time: when this tick should have returned, used as base for follow-up calls
    ///   - duration: how long should we sleep to reach the time (if the time is already
    ///               in the past, a overrun behavior is applied)
    /// Example:
    /// ```ignore
    /// use std::time::{Duration, SystemTime};
    /// use rhythmic::TimeInterval;
    /// let mut now = SystemTime::UNIX_EPOCH;
    /// let interval = Duration::from_secs(2);
    /// let mut time_interval = TimeInterval::new(interval);
    /// // this does not modify any interval state
    /// let (time_a, duration_a) = time_interval.tick_time(now);
    /// // run the "outer function again to set the correct state
    /// time_interval.tick_with_current_time(now);
    /// assert_eq!(time_a, now);
    /// assert_eq!(duration_a, Duration::ZERO);
    /// // only run this "inner" function - this does not set state
    /// let (time_b, duration_b) = time_interval.tick_time(now);
    /// assert_eq!(time_b, now + interval);
    /// assert_eq!(duration_b, interval);
    /// ```
    pub fn tick_time(&self, now: SystemTime) -> (SystemTime, Duration) {
        let Some(last_interval_start) = self.last_interval_start else {
            // first run, this is the start of the regular intervals, don't sleep.
            return (now, Duration::ZERO);
        };
        // This is a follow up tick() call
        // calculate the next regular `last_interval_start`
        let next_interval_start = last_interval_start + self.interval;
        // how long until the `next_interval_start`
        match next_interval_start.duration_since(now) {
            // `next_interval_start` >= `now`, use the duration to the next start as `sleep_time`
            Ok(sleep_time) => (next_interval_start, sleep_time),
            Err(_err) => {
                // `next_interval_start` < `now` - apply configured `overrun_behavior`
                let last_missed_interval_start =
                    Self::previous_interval_start(next_interval_start, now, self.interval);
                match self.overrun_behavior {
                    // try to align the next run with the previous regular intervals
                    OverrunBehavior::AwaitNextInterval => {
                        let next_regular_interval_start =
                            last_missed_interval_start + self.interval;
                        // use the last missed interval start and how long to sleep
                        // to the next interval start
                        (
                            next_regular_interval_start,
                            next_regular_interval_start
                                .duration_since(now)
                                .expect("now < next_regular_interval_start"),
                        )
                    }
                    // wait for the interval, don't align to the previous intervals but start new intervals
                    OverrunBehavior::WaitInterval => (now + self.interval, self.interval),
                    // no sleep for immediate return behavior but keep the interval alignment
                    OverrunBehavior::ImmediateReturn => {
                        (last_missed_interval_start, Duration::ZERO)
                    }
                }
            }
        }
    }

    /// sleep for the duration between `now` and `self.next_interval_start + self.interval` based on the
    /// given `self.overrun_behavior`
    /// Example:
    /// ```ignore
    /// use std::time::{Duration, SystemTime};
    /// use rhythmic::TimeInterval;
    /// let mut now = SystemTime::UNIX_EPOCH;
    /// let interval = Duration::from_secs(2);
    /// let mut time_interval = TimeInterval::new(interval);
    /// time_interval.tick_with_current_time(now);
    /// println!("some work starting at <now>");
    /// time_interval.tick_with_current_time(now);
    /// println!("some work starting at <now+interval> as the function sleeps to the next interval");
    /// assert_eq!(time_interval.last_interval_start.unwrap(), now+interval);
    /// ```
    pub fn tick_with_current_time(&mut self, now: SystemTime) {
        let (next_last_interval_start, sleep_time) = self.tick_time(now);
        debug_assert!(next_last_interval_start <= now + self.interval);
        debug_assert!(sleep_time <= self.interval);
        thread::sleep(sleep_time);
        self.last_interval_start = Some(next_last_interval_start);
        self.last_sleep_duration = Some(sleep_time);
    }

    /// wait for the next tick
    pub fn tick(&mut self) {
        self.tick_with_current_time(SystemTime::now());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // the tests use the internal tick_with_current_time() function with a given
    // START_TIME to be able to precisely control the internal structure according
    // to the specified behavior. A regular user should always use this with
    // `time_interval.tick()` equivalent to time_interval.tick(SystemTime::now)

    /// a constant known start time for tests
    const START_TIME: SystemTime = SystemTime::UNIX_EPOCH;

    #[test]
    fn test_first_immediate_tick() {
        let test_interval = Duration::from_secs(1);
        let mut time_interval = TimeInterval::new(test_interval);
        assert_eq!(time_interval.interval, test_interval);
        assert_eq!(time_interval.last_interval_start, None);
        time_interval.tick_with_current_time(START_TIME);
        // first tick returns immediately, `last_interval_start` is the current time
        assert_eq!(time_interval.last_interval_start, Some(START_TIME));
        assert_eq!(time_interval.last_sleep_duration, Some(Duration::ZERO));
    }

    #[test]
    fn test_regular_second_tick() {
        let test_interval = Duration::from_millis(10);
        let mut time_interval = TimeInterval::new(test_interval);
        // init - first tick returns immediately
        time_interval.tick_with_current_time(START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(START_TIME));
        time_interval.tick_with_current_time(START_TIME);
        // a regular second tick should have taken `test_interval` time
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + test_interval)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(test_interval));
    }

    #[test]
    fn test_await_next_interval_behavior() {
        let test_interval = Duration::from_millis(10);
        let long_work_interval = test_interval.mul_f32(1.1);
        let mut time_interval = TimeInterval::new(test_interval);
        // init - first tick returns immediately
        time_interval.tick_with_current_time(START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(START_TIME));
        // do some long work (a bit over one (*1.1) test interval)
        time_interval.tick_with_current_time(START_TIME + long_work_interval);
        // regular second tick was missed, so it sleeps until the next regular tick
        // which is less than a interval (0.9) but `next_interval_start` is
        // aligned to the regular run interval
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + test_interval * 2)
        );
        assert_eq!(
            time_interval.last_sleep_duration,
            Some(test_interval.mul_f32(0.9))
        );
        // test regular next tick - this should sleep for 1*test_interval time
        time_interval.tick_with_current_time(START_TIME + test_interval * 2);
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + test_interval * 3)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(test_interval));
    }

    #[test]
    fn test_wait_interval_behavior() {
        let test_interval = Duration::from_millis(10);
        let long_work_interval = test_interval.mul_f32(1.1);
        let mut time_interval =
            TimeInterval::new(test_interval).with_behavior(OverrunBehavior::WaitInterval);
        // init - first tick returns immediately
        time_interval.tick_with_current_time(START_TIME);
        // do some long work (a bit over one (*1.1) test interval)
        time_interval.tick_with_current_time(START_TIME + long_work_interval);
        // regular second tick was missed, but we expect `test_interval` time to be waited
        // the `last_interval_start` is adjusted to the new interval start
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + test_interval + long_work_interval)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(test_interval));
        // test regular next tick - this should sleep for 1*test_interval time
        time_interval.tick_with_current_time(START_TIME + long_work_interval + test_interval);
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + long_work_interval + test_interval * 2)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(test_interval));
    }

    #[test]
    fn test_immediate_return_behavior() {
        let test_interval = Duration::from_millis(10);
        let mut time_interval =
            TimeInterval::new(test_interval).with_behavior(OverrunBehavior::ImmediateReturn);
        // init - first tick returns immediately - see first_tick test
        time_interval.tick_with_current_time(START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(START_TIME));
        // test overrun behavior - ImmediateReturn
        // do some long work (a bit over one (*1.1) test interval)
        time_interval.tick_with_current_time(START_TIME + test_interval.mul_f32(1.1));
        // regular second tick was missed, we expect no time to be waited to recover work
        // but the last_interval_start is set as we would have returned on the last interval start
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + test_interval)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(Duration::ZERO));
        // test regular next tick - this should sleep for 0.9*test_interval time
        time_interval.tick_with_current_time(START_TIME + test_interval.mul_f32(1.1));
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + test_interval * 2)
        );
        assert_eq!(
            time_interval.last_sleep_duration,
            Some(test_interval.mul_f32(0.9))
        );
    }

    #[test]
    fn test_configure_new_interval() {
        let test_interval = Duration::from_millis(10);
        let new_test_interval = test_interval * 2;
        let mut time_interval = TimeInterval::new(test_interval);
        time_interval = time_interval.with_interval(new_test_interval);
        // tick should have used the new interval
        time_interval.tick_with_current_time(START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(START_TIME));
        time_interval.tick_with_current_time(START_TIME);
        assert_eq!(time_interval.last_sleep_duration, Some(new_test_interval));
        assert_eq!(
            time_interval.last_interval_start,
            Some(START_TIME + new_test_interval)
        );
    }

    #[test]
    fn test_previous_interval_start() {
        let test_interval = Duration::from_millis(10);
        // query the previous_interval_start after some missed intervals
        // if we are exactly on the start, the previous_interval_start should return this start
        let previous_interval_start_exact = TimeInterval::previous_interval_start(
            START_TIME,
            START_TIME + test_interval,
            test_interval,
        );
        assert_eq!(previous_interval_start_exact, START_TIME + test_interval);

        // if later than the interval start, give the previous one
        let previous_interval_start_later = TimeInterval::previous_interval_start(
            START_TIME,
            START_TIME + test_interval.mul_f32(1.1),
            test_interval,
        );
        assert_eq!(previous_interval_start_later, START_TIME + test_interval);
    }
}
