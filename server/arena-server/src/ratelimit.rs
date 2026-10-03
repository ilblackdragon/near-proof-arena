//! In-memory per-principal token-bucket rate limiter.

use std::collections::HashMap;
use std::sync::Mutex;
use std::time::Instant;

pub struct RateLimiter {
    per_minute: f64,
    burst: f64,
    buckets: Mutex<HashMap<String, (f64, Instant)>>,
}

impl RateLimiter {
    pub fn new(per_minute: u32, burst: u32) -> Self {
        Self {
            per_minute: per_minute as f64,
            burst: burst.max(1) as f64,
            buckets: Mutex::new(HashMap::new()),
        }
    }

    /// Take one token for `key`. `Err(seconds)` = retry after.
    pub fn check(&self, key: &str) -> Result<(), u64> {
        if self.per_minute <= 0.0 {
            return Ok(());
        }
        let now = Instant::now();
        let rate = self.per_minute / 60.0;
        let mut m = self.buckets.lock().unwrap_or_else(|e| e.into_inner());
        if m.len() > 100_000 {
            // bound memory: drop full buckets
            let burst = self.burst;
            m.retain(|_, (t, at)| *t + now.duration_since(*at).as_secs_f64() * rate < burst);
        }
        let (tokens, at) = m.entry(key.to_string()).or_insert((self.burst, now));
        *tokens = (*tokens + now.duration_since(*at).as_secs_f64() * rate).min(self.burst);
        *at = now;
        if *tokens >= 1.0 {
            *tokens -= 1.0;
            Ok(())
        } else {
            Err(((1.0 - *tokens) / rate).ceil().max(1.0) as u64)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bursts_then_limits() {
        let r = RateLimiter::new(60, 3);
        assert!(r.check("a").is_ok());
        assert!(r.check("a").is_ok());
        assert!(r.check("a").is_ok());
        assert!(r.check("a").is_err());
        assert!(r.check("b").is_ok());
        assert!(RateLimiter::new(0, 1).check("x").is_ok());
    }
}
