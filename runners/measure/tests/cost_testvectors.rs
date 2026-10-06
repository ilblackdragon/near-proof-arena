//! Cross-language cost_v1 vectors (`benchmarks/testvectors/cost.json`,
//! docs/BENCHMARK_SPEC.md §14). Every output is an integer and must match.

use arena_measure::cost::{self, Components, CostClassRuns, Prices};
use serde_json::Value;

fn vectors() -> Value {
    let p = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/testvectors/cost.json"
    );
    let v: Value = serde_json::from_slice(&std::fs::read(p).expect("cost.json")).unwrap();
    assert_eq!(v["schema"], "arena-bench-cost-testvectors-v1");
    v
}

fn u(v: &Value) -> u64 {
    v.as_u64().unwrap_or_else(|| panic!("not a u64: {v}"))
}
fn us(v: &Value) -> Vec<u64> {
    v.as_array().unwrap().iter().map(u).collect()
}
fn prices(v: &Value) -> Prices {
    Prices {
        validators_per_chunk: u(&v["validators_per_chunk"]) as u32,
        prover_vcpus: u(&v["prover_vcpus"]) as u32,
        verifier_vcpus: u(&v["verifier_vcpus"]) as u32,
        cpu_fusd_per_vcpu_second: u(&v["cpu_fusd_per_vcpu_second"]),
        bandwidth_fusd_per_byte: u(&v["bandwidth_fusd_per_byte"]),
        storage_fusd_per_byte: u(&v["storage_fusd_per_byte"]),
        prepare_amortization_requests: u(&v["prepare_amortization_requests"]),
    }
}
fn comps(v: &Value) -> Components {
    Components {
        prove_ns: u(&v["prove_ns"]),
        verify_ns: u(&v["verify_ns"]),
        proof_bytes: u(&v["proof_bytes"]),
    }
}
fn classes(v: &Value) -> Vec<CostClassRuns> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|c| CostClassRuns {
            class_id: c["class_id"].as_str().unwrap().into(),
            weight_ppm: u(&c["weight_ppm"]) as u32,
            batch_size: u(&c["batch_size"]) as u32,
            baseline: comps(&c["baseline"]),
            prove_runs_ns: us(&c["prove_runs_ns"]),
            verify_runs_ns: us(&c["verify_runs_ns"]),
            proof_bytes_runs: us(&c["proof_bytes_runs"]),
        })
        .collect()
}
fn breakdown_matches(b: &cost::Breakdown, ex: &Value, name: &Value) {
    assert_eq!(
        [
            b.prove_fusd,
            b.prepare_fusd,
            b.verify_fusd,
            b.bandwidth_fusd,
            b.storage_fusd,
            b.total_fusd
        ],
        [
            u(&ex["prove_fusd"]),
            u(&ex["prepare_fusd"]),
            u(&ex["verify_fusd"]),
            u(&ex["bandwidth_fusd"]),
            u(&ex["storage_fusd"]),
            u(&ex["total_fusd"])
        ],
        "{name}"
    );
}

#[test]
fn batch_cost_vectors() {
    let v = vectors();
    let cases = v["batch_cost"].as_array().unwrap();
    assert!(cases.len() >= 8);
    for case in cases {
        let got = cost::batch_cost(
            &prices(&case["prices"]),
            comps(&case["components"]),
            u(&case["prepare_ns"]),
            u(&case["batch_size"]) as u32,
        );
        match case["expect"].get("error") {
            Some(e) => assert_eq!(
                got.unwrap_err().code(),
                e.as_str().unwrap(),
                "{}",
                case["name"]
            ),
            None => breakdown_matches(&got.unwrap(), &case["expect"], &case["name"]),
        }
    }
}

#[test]
fn cost_score_vectors() {
    let v = vectors();
    for case in v["cost_score"].as_array().unwrap() {
        let got = cost::cost_score(
            &prices(&case["prices"]),
            &classes(&case["classes"]),
            u(&case["prepare_ns"]),
            u(&case["baseline_prepare_ns"]),
        );
        let name = &case["name"];
        match case["expect"].get("error") {
            Some(e) => assert_eq!(got.unwrap_err().code(), e.as_str().unwrap(), "{name}"),
            None => {
                let r = got.unwrap();
                assert_eq!(r.score_milli, u(&case["expect"]["score_milli"]), "{name}");
                for (c, ex) in r
                    .classes
                    .iter()
                    .zip(case["expect"]["classes"].as_array().unwrap())
                {
                    assert_eq!(c.class_id, ex["class_id"].as_str().unwrap());
                    assert_eq!(
                        c.baseline_total_fusd,
                        u(&ex["baseline_total_fusd"]),
                        "{name}"
                    );
                    breakdown_matches(&c.cost, ex, name);
                }
            }
        }
    }
}

#[test]
fn cost_bootstrap_vectors() {
    let v = vectors();
    for case in v["cost_bootstrap"].as_array().unwrap() {
        let r = cost::cost_bootstrap(
            &prices(&case["prices"]),
            &classes(&case["classes"]),
            u(&case["prepare_ns"]),
            u(&case["baseline_prepare_ns"]),
            u(&case["seed"]),
            u(&case["iterations"]) as u32,
        )
        .unwrap();
        let ex = &case["expect"];
        assert_eq!(
            (r.score_milli, r.lo_milli, r.hi_milli, r.half_width_milli),
            (
                u(&ex["score_milli"]),
                u(&ex["lo_milli"]),
                u(&ex["hi_milli"]),
                u(&ex["half_width_milli"])
            ),
            "{}",
            case["name"]
        );
    }
}
