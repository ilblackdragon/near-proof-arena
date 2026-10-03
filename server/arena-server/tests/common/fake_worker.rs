//! In-process FAKE worker used only by tests to drive the pipeline end to end.
//! It performs no real checks: every result it produces is `tier_cap = demo`,
//! sandbox `test-fake`, and every gate carries `DEMO_ONLY`.

use arena_jobs::client::WorkerClient;
use arena_jobs::*;
use arena_types::*;
use std::collections::HashSet;

#[derive(Clone, Debug, Default)]
pub struct Behavior {
    pub fail_gate: Option<ObligationId>,
    pub unknown_gate: Option<ObligationId>,
    /// Always report a retryable infra failure for this kind.
    pub infra_fail: Option<JobKind>,
    /// Report a gate this job kind does not own (protocol error).
    pub bogus_gate_on: Option<JobKind>,
    /// Summary text override (sanitization tests).
    pub summary: Option<String>,
}

pub struct FakeWorker {
    pub client: WorkerClient,
    pub behavior: Behavior,
    /// Tag that determines the "verifier" digests (same tag => same verified surface).
    pub verifier_tag: String,
    /// Prover speed-up relative to the challenge baseline (2 => score 200).
    pub speedup: u64,
}

pub fn d(s: &str) -> Digest {
    Digest::of_bytes(s.as_bytes())
}

impl FakeWorker {
    pub fn new(base: &str, token: &str) -> Self {
        Self {
            client: WorkerClient::new(base, token).unwrap(),
            behavior: Behavior::default(),
            verifier_tag: "v1".into(),
            speedup: 2,
        }
    }

    fn gate(&self, g: ObligationId) -> GateResult {
        let status = if self.behavior.fail_gate == Some(g) {
            GateStatus::Fail
        } else if self.behavior.unknown_gate == Some(g) {
            GateStatus::Unknown
        } else if g == ObligationId::FormalZk {
            GateStatus::NotApplicable
        } else {
            GateStatus::Pass
        };
        GateResult {
            gate: g,
            mandatory: true,
            status,
            reason_codes: vec![ReasonCode::DemoOnly],
            summary: self.behavior.summary.clone().unwrap_or_else(|| {
                "[DEMO] simulated by the in-process test worker; no real check was performed".into()
            }),
            evidence: vec![],
            started_at: None,
            finished_at: None,
            // workers cannot claim reuse; the server must ignore this
            reused_from: Some("sub_forged".into()),
        }
    }

    pub async fn result_for(&self, job: &LeasedJob) -> JobResult {
        let ctx = job.spec.ctx();
        let chal = job.spec.challenge();
        let mut gates: Vec<GateResult> = job
            .kind
            .owned_gates()
            .iter()
            .map(|g| self.gate(*g))
            .collect();
        if self.behavior.bogus_gate_on == Some(job.kind) {
            gates.push(self.gate(ObligationId::Benchmark));
        }
        let log = format!("[DEMO] {} log for {}", job.kind, ctx.submission_id);
        let log_digest = Digest::of_bytes(log.as_bytes());
        self.client
            .put_artifact(&log_digest, log.clone().into_bytes())
            .await
            .unwrap();
        let mut r = JobResult {
            gates,
            artifacts: vec![EvidenceRef {
                label: format!("{} log", job.kind),
                digest: log_digest,
                public: true,
            }],
            benchmark: None,
            evidence_graph: None,
            manifest: None,
            build: None,
            execution: ExecutionInfo {
                sandbox_backend: "test-fake".into(),
                tier_cap: challenge::Tier::Demo,
                worker_version: "fake-0".into(),
            },
            log_excerpt: Some(log),
        };
        match &job.spec {
            JobSpec::Validate(_) => {
                r.manifest = Some(CandidateManifest {
                    schema: "arena-candidate-v1".into(),
                    name: "fake-prover".into(),
                    agent: "alice".into(),
                    challenge: ctx.challenge_id.clone(),
                    parent: None,
                    backend_family: "demo".into(),
                    security_profile_request: chal.security_profile.id.clone(),
                    hardware: candidate::HardwareRequest {
                        gpu: false,
                        min_ram_gb: 1,
                    },
                    build: candidate::BuildSection {
                        recipe: "build-recipe/build.sh".into(),
                        outputs: vec!["out/prove".into()],
                    },
                    entry: candidate::EntrySection {
                        prepare: "out/prepare".into(),
                        prove: "out/prove".into(),
                        verify: "out/verify".into(),
                        verify_route: None,
                        verifier_bytecode: None,
                    },
                    formal: Some(candidate::FormalSection {
                        lean_project: "formal".into(),
                        certificate: "Candidate.certificate".into(),
                        verifier_model: None,
                        verifier_model_module: None,
                    }),
                })
            }
            JobSpec::Build(_) => {
                let t = &self.verifier_tag;
                r.build = Some(BuildOutputs {
                    prepare: d(&format!("prepare:{t}")),
                    prove: d(&format!("prove:{}", ctx.package_digest)),
                    verify: d(&format!("verify:{t}")),
                    bundle: d(&format!("bundle:{}", ctx.package_digest)),
                    public_artifacts: d(&format!("public:{t}")),
                    formal_tree: d(&format!("formal:{t}")),
                    certificate_decl: "Candidate.certificate".into(),
                    toolchain_image: Some("demo-build-image".into()),
                    build_ns: Some(1234),
                    bundle_archive: None,
                    public_archive: None,
                })
            }
            JobSpec::FormalCheck(_) => {
                use evidence::*;
                r.evidence_graph = Some(EvidenceGraph {
                    nodes: vec![
                        EvidenceNode {
                            id: "thm".into(),
                            kind: NodeKind::Theorem,
                            label: "[DEMO] admission".into(),
                            digest: None,
                        },
                        EvidenceNode {
                            id: "spec".into(),
                            kind: NodeKind::FormalSemantics,
                            label: "spec".into(),
                            digest: None,
                        },
                        EvidenceNode {
                            id: "kernel".into(),
                            kind: NodeKind::TcbComponent,
                            label: "[DEMO] kernel".into(),
                            digest: None,
                        },
                    ],
                    edges: vec![EvidenceEdge {
                        from: "thm".into(),
                        to: "spec".into(),
                        kind: "refines".into(),
                        status: EdgeStatus::Missing,
                        evidence: vec![],
                        note: "DEMO: not checked".into(),
                    }],
                })
            }
            JobSpec::Benchmark(_) => {
                let classes = chal
                    .workload_suite
                    .classes
                    .iter()
                    .map(|c| {
                        let base = chal
                            .workload_suite
                            .baseline_ns
                            .iter()
                            .find(|(k, _)| *k == c.id)
                            .unwrap()
                            .1;
                        let med = base / self.speedup;
                        ClassMeasurement {
                            class_id: c.id.clone(),
                            weight_ppm: c.weight_ppm,
                            runs_ns: vec![med; 5],
                            median_ns: med,
                            mad_ns: 0,
                            cold_ns: None,
                            baseline_ns: 0,
                            verify_median_ns: 1000,
                            proof_bytes_max: 2048,
                            peak_rss_bytes: 1 << 20,
                        }
                    })
                    .collect();
                r.benchmark = Some(BenchmarkResult {
                    hardware_profile: chal.hardware_profile.id.clone(),
                    suite_revision: chal.workload_suite.revision.clone(),
                    classes,
                    score_milli: Some(u64::MAX / 4), // forged; server recomputes
                    score_ci_milli: Some(500),
                    prepare_ns: 1,
                    public_artifact_bytes: 1,
                    measured_by: "[DEMO] fake worker".into(),
                })
            }
            _ => {}
        }
        r
    }

    /// Lease one job (optionally of given kinds) without completing it.
    pub async fn lease(&self, kinds: &[JobKind], lease_seconds: Option<u32>) -> Option<LeasedJob> {
        self.client
            .lease(&LeaseRequest {
                kinds: kinds.to_vec(),
                lease_seconds,
            })
            .await
            .unwrap()
    }

    /// Process one job according to the behavior. Returns its kind, or None if idle.
    pub async fn step(&self) -> Option<JobKind> {
        let job = self.lease(&[], None).await?;
        if self.behavior.infra_fail == Some(job.kind) {
            self.client
                .fail(
                    &job.job_id,
                    &FailRequest {
                        lease_id: job.lease_id.clone(),
                        error: "simulated infra failure".into(),
                        retryable: true,
                    },
                )
                .await
                .unwrap();
            return Some(job.kind);
        }
        let result = self.result_for(&job).await;
        let res = self
            .client
            .complete(
                &job.job_id,
                &CompleteRequest {
                    lease_id: job.lease_id.clone(),
                    result,
                },
            )
            .await;
        if let Err(e) = res {
            assert_eq!(e.status(), Some(422), "unexpected complete error: {e}");
        }
        Some(job.kind)
    }

    /// Run until the queue is empty; returns the kinds processed in order.
    pub async fn drain(&self) -> Vec<JobKind> {
        let mut out = Vec::new();
        while let Some(k) = self.step().await {
            out.push(k);
            assert!(out.len() < 200, "runaway pipeline");
        }
        out
    }
}

pub fn kinds_set(v: &[JobKind]) -> HashSet<JobKind> {
    v.iter().copied().collect()
}
