//! Cross-language vectors from the bench lane
//! (`benchmarks/testvectors/score.json`, docs/BENCHMARK_SPEC.md §8.5).
//! Every integer output must match exactly.

use arena_measure::score::{self, ClassInput, ClassRuns};
use arena_measure::stats::{self, ScheduleShape, SplitMix64};
use serde_json::Value;

fn vectors() -> Value {
    let p = concat!(env!("CARGO_MANIFEST_DIR"), "/../../benchmarks/testvectors/score.json");
    let v: Value = serde_json::from_slice(&std::fs::read(p).expect("benchmarks/testvectors/score.json")).unwrap();
    assert_eq!(v["schema"], "arena-bench-testvectors-v1");
    v
}

fn u(v: &Value) -> u64 {
    v.as_u64().unwrap_or_else(|| panic!("not a u64: {v}"))
}
fn us(v: &Value) -> Vec<u64> {
    v.as_array().unwrap().iter().map(u).collect()
}
fn s(v: &Value) -> String {
    v.as_str().unwrap().to_string()
}

#[test]
fn splitmix64() {
    let v = vectors();
    for case in v["splitmix64"].as_array().unwrap() {
        let mut r = SplitMix64::new(u(&case["seed"]));
        let got: Vec<u64> = (0..case["outputs"].as_array().unwrap().len()).map(|_| r.next_u64()).collect();
        assert_eq!(got, us(&case["outputs"]), "seed {}", case["seed"]);
    }
}

#[test]
fn median_mad() {
    let v = vectors();
    for case in v["median_mad"].as_array().unwrap() {
        let xs = us(&case["input"]);
        assert_eq!(stats::median_u64(&xs), Some(u(&case["median"])), "{xs:?}");
        assert_eq!(stats::mad_u64(&xs), Some(u(&case["mad"])), "{xs:?}");
    }
}

#[test]
fn derive_seed() {
    let v = vectors();
    for case in v["derive_seed"].as_array().unwrap() {
        let parts: Vec<String> = case["parts"].as_array().unwrap().iter().map(s).collect();
        let refs: Vec<&str> = parts.iter().map(|p| p.as_str()).collect();
        assert_eq!(stats::derive_seed(&s(&case["purpose"]), &refs).unwrap(), u(&case["seed"]));
    }
}

#[test]
fn score_vectors() {
    let v = vectors();
    let tol: f64 = v["score_f64_rel_tolerance"].as_str().unwrap().parse().unwrap();
    let mut n = 0;
    for case in v["score"].as_array().unwrap() {
        let classes: Vec<ClassInput> = case["classes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| ClassInput {
                class_id: s(&c["class_id"]),
                weight_ppm: u(&c["weight_ppm"]) as u32,
                baseline_ns: u(&c["baseline_ns"]),
                median_ns: u(&c["median_ns"]),
            })
            .collect();
        let got = score::score(&classes);
        let name = &case["name"];
        match case["expect"].get("error") {
            Some(e) => assert_eq!(got.map(|r| r.score_milli).map_err(|e| e.code()), Err(e.as_str().unwrap()), "{name}"),
            None => {
                let r = got.unwrap_or_else(|e| panic!("{name}: {e}"));
                assert_eq!(r.score_milli, u(&case["expect"]["score_milli"]), "{name}");
                let f: f64 = case["expect"]["score_f64"].as_str().unwrap().parse().unwrap();
                assert!(((r.score_f64 - f) / f).abs() <= tol, "{name}: {} vs {f}", r.score_f64);
            }
        }
        n += 1;
    }
    assert!(n >= 10);
}

#[test]
fn bootstrap_vectors() {
    let v = vectors();
    for case in v["bootstrap"].as_array().unwrap() {
        let classes: Vec<ClassRuns> = case["classes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| ClassRuns {
                class_id: s(&c["class_id"]),
                weight_ppm: u(&c["weight_ppm"]) as u32,
                baseline_ns: u(&c["baseline_ns"]),
                runs_ns: us(&c["runs_ns"]),
            })
            .collect();
        let got = score::bootstrap_ci(&classes, u(&case["seed"]), u(&case["iterations"]) as u32);
        let name = &case["name"];
        let ex = &case["expect"];
        match ex.get("error") {
            Some(e) => assert_eq!(got.map_err(|e| e.code()).err(), Some(e.as_str().unwrap()), "{name}"),
            None => {
                let r = got.unwrap();
                assert_eq!(
                    (r.score_milli, r.lo_milli, r.hi_milli, r.half_width_milli),
                    (u(&ex["score_milli"]), u(&ex["lo_milli"]), u(&ex["hi_milli"]), u(&ex["half_width_milli"])),
                    "{name}"
                );
            }
        }
    }
}

#[test]
fn schedule_vectors() {
    let v = vectors();
    for case in v["schedule"].as_array().unwrap() {
        let ids: Vec<String> = case["class_ids"].as_array().unwrap().iter().map(s).collect();
        let shape = ScheduleShape {
            cold_runs: u(&case["cold_runs"]) as u32,
            warmup_runs: u(&case["warmup_runs"]) as u32,
            measured_runs: u(&case["measured_runs"]) as u32,
            fresh_confirm_runs: u(&case["fresh_confirm_runs"]) as u32,
            calibration_runs: u(&case["calibration_runs"]) as u32,
        };
        let got: Vec<(String, String, u64)> = stats::build_schedule(&ids, u(&case["seed"]), shape)
            .unwrap()
            .into_iter()
            .map(|r| (r.phase.as_str().to_string(), r.class_id, r.round as u64))
            .collect();
        let want: Vec<(String, String, u64)> = case["expect"]
            .as_array()
            .unwrap()
            .iter()
            .map(|e| (s(&e[0]), s(&e[1]), u(&e[2])))
            .collect();
        assert_eq!(got, want);
    }
}

#[test]
fn outlier_vectors() {
    let v = vectors();
    for case in v["outliers"].as_array().unwrap() {
        let r = stats::flag_outliers(&us(&case["runs_ns"]), u(&case["k"]) as u32).unwrap();
        let ex = &case["expect"];
        assert_eq!(r.median_ns, u(&ex["median_ns"]));
        assert_eq!(r.mad_ns, u(&ex["mad_ns"]));
        let want: Vec<usize> = us(&ex["flagged_indices"]).into_iter().map(|x| x as usize).collect();
        assert_eq!(r.flagged_indices, want);
    }
}

#[test]
fn drift_vectors() {
    let v = vectors();
    for case in v["drift_ppm"].as_array().unwrap() {
        assert_eq!(stats::drift_ppm(u(&case["a"]), u(&case["b"])), u(&case["ppm"]), "{case}");
    }
}
