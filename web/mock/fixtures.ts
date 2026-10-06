/**
 * DEMO FIXTURES for the development mock API and the test-suite.
 *
 * Every record here is fabricated and labelled "DEMO FIXTURE"; agents are
 * `demo-fixture-*`. This module is imported only by `mock/dev-server.ts`
 * (Vite dev server, ARENA_MOCK=1) and by tests — never by `src/`, so it is
 * never part of a production bundle (enforced by scripts/check-dist.mjs).
 */
import { createHash } from 'node:crypto';
import { canonicalJson } from '../src/lib/jcs';
import { isOfficiallyRankable } from '../src/lib/board';
import type {
  BoardEntry,
  ChallengeDefinition,
  ChallengeRecord,
  EvidenceGraph,
  GateResult,
  ObligationId,
  SubmissionDetail,
} from '../src/api/types';

export const DEMO_MARKER = 'DEMO FIXTURE';

export const sha = (s: string) => `sha256:${createHash('sha256').update(s).digest('hex')}`;
const fd = (seed: string) => sha(`demo-fixture:${seed}`);

export function challengeRecord(definition: ChallengeDefinition): ChallengeRecord {
  const digest = sha(canonicalJson(definition));
  return {
    id: `chl_${digest.slice(7, 39)}`,
    digest,
    definition,
    tier: definition.tier,
    open: true,
    signature: '00'.repeat(64),
    governance_key: 'demo-fixture-governance-key',
    registered_at: '2026-09-01T00:00:00Z',
    registered_by: 'demo-fixture-admin',
  };
}

export const ALL_OBLIGATIONS: ObligationId[] = [
  'PKG_WELLFORMED',
  'BUILD_REPRODUCIBLE',
  'ARTIFACT_BINDING',
  'FORMAL_SEMANTIC_SOUNDNESS',
  'FORMAL_SEMANTIC_COMPLETENESS',
  'FORMAL_CRYPTO_SOUNDNESS',
  'FORMAL_IMPL_CONNECTION',
  'FORMAL_ZK',
  'AXIOM_AUDIT',
  'CONFORMANCE_DIFFERENTIAL',
  'ADVERSARIAL_PROOFS',
  'PROVER_RELIABILITY',
  'RESOURCE_LIMITS',
  'BENCHMARK',
];

export function makeDefinition(o: {
  name: string;
  tier: ChallengeDefinition['tier'];
  kind?: ChallengeDefinition['semantic_scope']['kind'];
  excludes?: string[];
  restrictions?: { id: string; text: string }[];
  baseline?: string | null;
}): ChallengeDefinition {
  return {
    schema: 'arena-challenge-v1',
    name: o.name,
    season: 'demo-fixture-season',
    tier: o.tier,
    nearcore: {
      repo: 'https://github.com/near/nearcore',
      tag: '2.13.4',
      commit: '0000000000000000000000000000000000demo00',
    },
    protocol_version: 80,
    chain_id: 'demo-fixture-chain',
    runtime_config_digest: fd('runtime-config'),
    semantic_scope: {
      name: `${o.name} scope`,
      kind: o.kind ?? 'subset',
      granularity: 'single_action_receipt_transition',
      restrictions: o.restrictions ?? [
        { id: 'single_action', text: 'Receipts contain exactly one Transfer action.' },
        { id: 'no_contracts', text: 'No Wasm contract execution.' },
      ],
      excludes: o.excludes ?? ['block_finality', 'data_availability', 'receipt_inclusion'],
      formal_spec: {
        relation_module: 'NearSpec.TransferV1',
        relation_decl: 'NearSpec.TransferV1.NearRelation',
        tree_digest: fd('spec-tree'),
        lean_toolchain: 'leanprover/lean4:v4.20.0',
      },
      spec_doc_digest: fd('spec-doc'),
    },
    claim_encoding: {
      format: 'near-arena-claim-v1',
      spec_digest: fd('claim-spec'),
      max_request_bytes: 1 << 20,
      max_witness_bytes: 64 << 20,
      max_claim_bytes: 4096,
    },
    security_profile: {
      id: 'validity-classical-128',
      privacy: 'validity_only',
      adversary: 'classical',
      target_bits: 128,
      model: 'random_oracle',
      setup_model: 'transparent',
      allowed_assumptions: ['sha256_collision_resistant'],
      max_prover_queries_log2: 64,
      max_hash_queries_log2: 64,
      max_aggregation_depth: 0,
      deployment_proofs_log2: 40,
    },
    toolchain_policy: {
      lean_toolchain: 'leanprover/lean4:v4.20.0',
      checker_image: fd('checker-image'),
      axiom_allowlist: ['propext', 'Classical.choice', 'Quot.sound'],
      allowed_packages: [['mathlib', '0000000000000000000000000000000000000000']],
      recheckers: ['lean4checker'],
    },
    required_obligations: ALL_OBLIGATIONS,
    not_applicable_gates: ['FORMAL_ZK'],
    hardware_profile: {
      id: 'demo-cpu-32',
      cpu_model: 'DEMO FIXTURE CPU',
      vcpus: 32,
      ram_bytes: 128 * 1024 ** 3,
      gpu: null,
    },
    workload_suite: {
      revision: 'demo-r1',
      classes: [
        { id: 'transfer-small', description: 'Single transfer receipts', weight_ppm: 600_000, batch_size: 64, generator: fd('gen-small') },
        { id: 'transfer-batch', description: 'Batches of 1024 transfers', weight_ppm: 400_000, batch_size: 1024, generator: fd('gen-batch') },
      ],
      public_fixtures: fd('public-fixtures'),
      heldout_commitment: fd('heldout'),
      baseline_submission: o.baseline ?? null,
      baseline_ns: [
        ['transfer-small', 40_000_000],
        ['transfer-batch', 900_000_000],
      ],
    },
    measurement: {
      warmup_runs: 2,
      measured_runs: 9,
      aggregation: 'median',
      outlier_mad_k: 5,
      cold_runs: 1,
      concurrency: 1,
      per_run_timeout_ms: 600_000,
    },
    resource_limits: {
      max_proof_bytes: 1 << 20,
      max_verify_ms: 2000,
      max_prove_ms: 600_000,
      max_ram_bytes: 64 * 1024 ** 3,
      max_vram_bytes: 0,
      max_public_artifact_bytes: 256 << 20,
      max_prepare_ms: 600_000,
      max_build_ms: 1_800_000,
    },
    supersedes: null,
    created_at: '2026-09-01T00:00:00Z',
  };
}

export function gates(
  status: Partial<Record<ObligationId, GateResult['status']>>,
  extra: Partial<Record<ObligationId, Partial<GateResult>>> = {},
): GateResult[] {
  return ALL_OBLIGATIONS.filter((g) => g in status).map((g) => ({
    gate: g,
    mandatory: g !== 'FORMAL_ZK',
    status: status[g]!,
    reason_codes: [],
    summary: `${DEMO_MARKER}: ${g.toLowerCase()} ${status[g] === 'PASS' ? 'ok' : status[g]!.toLowerCase()}`,
    evidence: [{ label: `${g.toLowerCase()}-evidence`, digest: fd(`ev-${g}`), public: true }],
    started_at: '2026-09-02T10:00:00Z',
    finished_at: '2026-09-02T10:05:00Z',
    reused_from: null,
    ...extra[g],
  }));
}

export const allPass = () =>
  Object.fromEntries(ALL_OBLIGATIONS.map((g) => [g, g === 'FORMAL_ZK' ? 'NOT_APPLICABLE' : 'PASS'])) as Record<
    ObligationId,
    GateResult['status']
  >;

export function evidenceGraph(opts: { missing?: boolean } = {}): EvidenceGraph {
  return {
    nodes: [
      { id: 'nc', kind: 'nearcore_source', label: 'nearcore 2.13.4 runtime', digest: fd('nc') },
      { id: 'spec', kind: 'formal_semantics', label: 'NearSpec.TransferV1', digest: fd('spec') },
      { id: 'thm', kind: 'theorem', label: 'Candidate.certificate', digest: fd('thm') },
      { id: 'bsem', kind: 'backend_semantics', label: 'Backend verifier model', digest: null },
      { id: 'asm', kind: 'assumption', label: 'sha256_collision_resistant', digest: null },
      { id: 'verify', kind: 'artifact', label: 'out/verify', digest: fd('verify-bin') },
      { id: 'prove', kind: 'artifact', label: 'out/prove', digest: fd('prove-bin') },
      { id: 'kernel', kind: 'tcb_component', label: 'Lean 4 kernel', digest: null },
      { id: 'sandbox', kind: 'tcb_component', label: 'microVM sandbox', digest: fd('sandbox') },
      { id: 'conf', kind: 'test_suite', label: 'conformance suite demo-r1', digest: fd('conf') },
      { id: 'bench', kind: 'measurement', label: 'benchmark demo-r1', digest: fd('bench') },
    ],
    edges: [
      { from: 'nc', to: 'spec', kind: 'tested_against', status: 'tested', evidence: [fd('diff')], note: 'Differential testing only; Lean spec is not proven equal to nearcore Rust.' },
      { from: 'thm', to: 'spec', kind: 'refines', status: 'checked', evidence: [fd('thm-check')], note: 'Kernel-checked soundness + completeness' },
      { from: 'thm', to: 'asm', kind: 'assumes', status: 'trusted', evidence: [], note: 'Governed assumption' },
      { from: 'bsem', to: 'thm', kind: 'refines', status: 'checked', evidence: [fd('bsem')], note: '' },
      opts.missing
        ? { from: 'verify', to: 'bsem', kind: 'implements', status: 'missing', evidence: [], note: 'No FORMAL_IMPL_CONNECTION evidence.' }
        : { from: 'verify', to: 'bsem', kind: 'implements', status: 'checked', evidence: [fd('impl')], note: '' },
      { from: 'thm', to: 'kernel', kind: 'checked_by', status: 'trusted', evidence: [], note: '' },
      { from: 'prove', to: 'conf', kind: 'tested_against', status: 'tested', evidence: [fd('conf-run')], note: '' },
      { from: 'prove', to: 'bench', kind: 'measured_by', status: 'checked', evidence: [fd('bench-run')], note: '' },
      { from: 'verify', to: 'sandbox', kind: 'runs_in', status: 'trusted', evidence: [], note: '' },
    ],
  };
}

export function benchmark(scoreMilli: number | null, factor = 1) {
  return {
    hardware_profile: 'demo-cpu-32',
    suite_revision: 'demo-r1',
    classes: [
      { class_id: 'transfer-small', weight_ppm: 600_000, runs_ns: Array(9).fill(Math.round(40_000_000 / factor)), median_ns: Math.round(40_000_000 / factor), mad_ns: 400_000, cold_ns: 90_000_000, baseline_ns: 40_000_000, verify_median_ns: 2_100_000, proof_bytes_max: 180_000, peak_rss_bytes: 2_400_000_000 },
      { class_id: 'transfer-batch', weight_ppm: 400_000, runs_ns: Array(9).fill(Math.round(900_000_000 / factor)), median_ns: Math.round(900_000_000 / factor), mad_ns: 7_000_000, cold_ns: null, baseline_ns: 900_000_000, verify_median_ns: 3_900_000, proof_bytes_max: 410_000, peak_rss_bytes: 9_800_000_000 },
    ],
    score_milli: scoreMilli,
    score_ci_milli: scoreMilli === null ? null : Math.round(scoreMilli * 0.012),
    prepare_ns: 12_000_000_000,
    public_artifact_bytes: 48_000_000,
    measured_by: 'demo-fixture-runner',
  };
}

export function makeSub(o: Partial<SubmissionDetail> & { id: string; challenge_id: string }): SubmissionDetail {
  return {
    agent: 'demo-fixture-agent',
    candidate_name: `${DEMO_MARKER} prover`,
    backend_family: 'reexec-merkle',
    parent: null,
    tier: 'formal',
    package_digest: fd(`pkg-${o.id}`),
    stage: 'DECIDED',
    decision: 'ADMITTED',
    accepted: true,
    score_milli: null,
    change_class: 'NO_PARENT',
    gates: gates(allPass()),
    reason_codes: [],
    benchmark: null,
    evidence_graph: evidenceGraph(),
    revoked: null,
    created_at: '2026-09-02T09:00:00Z',
    updated_at: '2026-09-02T11:00:00Z',
    ...o,
  };
}

export function toEntry(s: SubmissionDetail, def: ChallengeDefinition, rank: number | null = null): BoardEntry {
  const cls = s.benchmark?.classes ?? [];
  const max = (f: (c: (typeof cls)[number]) => number) => (cls.length ? Math.max(...cls.map(f)) : null);
  return {
    rank,
    challenge_id: s.challenge_id,
    protocol_version: def.protocol_version,
    superseded_by: null,
    submission_id: s.id,
    agent: s.agent,
    candidate_name: s.candidate_name,
    backend_family: s.backend_family,
    tier: s.tier,
    decision: s.decision ?? null,
    accepted: s.accepted ?? null,
    score_milli: s.accepted ? (s.score_milli ?? null) : null,
    score_ci_milli: s.benchmark?.score_ci_milli ?? null,
    prove_median_ns: cls[0]?.median_ns ?? null,
    verify_median_ns: cls[0]?.verify_median_ns ?? null,
    proof_bytes: max((c) => c.proof_bytes_max),
    peak_rss_bytes: max((c) => c.peak_rss_bytes),
    hardware_profile: def.hardware_profile.id,
    scope: def.semantic_scope.name,
    security_profile: def.security_profile.id,
    submitted_at: s.created_at,
    revoked: !!s.revoked,
    cost: s.benchmark?.cost ?? null,
  };
}

export interface Dataset {
  challenges: ChallengeRecord[];
  submissions: SubmissionDetail[];
  /** Optional explicit leaderboards; otherwise derived from submissions. */
  leaderboards?: Record<string, BoardEntry[]>;
}

export function leaderboardFor(ds: Dataset, id: string): BoardEntry[] | null {
  if (ds.leaderboards?.[id]) return ds.leaderboards[id];
  const c = ds.challenges.find((x) => x.id === id);
  if (!c) return null;
  // Mirrors the server: ranked entries first (rank 1..n), then everything else with rank null.
  const all = ds.submissions.filter((s) => s.challenge_id === id).map((s) => toEntry(s, c.definition));
  const ranked = all
    .filter((e) => isOfficiallyRankable(e, c.definition))
    .sort((a, b) => (b.score_milli ?? 0) - (a.score_milli ?? 0))
    .map((e, i) => ({ ...e, rank: i + 1 }));
  const out = [...ranked, ...all.filter((e) => !isOfficiallyRankable(e, c.definition))];
  return out.map((e) => ({ ...e, superseded_by: c.superseded_by ?? null }));
}

/** The dataset served by `pnpm dev:mock`. */
export function demoDataset(): Dataset {
  const empty = challengeRecord(
    makeDefinition({ name: `${DEMO_MARKER} — transfer-v1 (formal tier, nothing admitted)`, tier: 'formal' }),
  );
  const ranked = challengeRecord(
    makeDefinition({
      name: `${DEMO_MARKER} — chunk-transition (formal tier, sample ranking)`,
      tier: 'formal',
      kind: 'full_chunk_transition',
      excludes: ['block_finality', 'data_availability'],
      restrictions: [],
      baseline: 'sub_demo_ref',
    }),
  );
  const demo = challengeRecord(makeDefinition({ name: `${DEMO_MARKER} — plumbing (demo tier)`, tier: 'demo' }));
  const R = ranked.id;
  const E = empty.id;
  const formalReused = Object.fromEntries(
    ALL_OBLIGATIONS.filter((g) => g.startsWith('FORMAL') || g === 'AXIOM_AUDIT').map((g) => [g, { reused_from: 'sub_demo_alpha' }]),
  );
  const submissions: SubmissionDetail[] = [
    makeSub({ id: 'sub_demo_ref', challenge_id: R, candidate_name: `${DEMO_MARKER} reference re-execution`, agent: 'demo-fixture-arena', score_milli: 100_000, benchmark: benchmark(100_000) }),
    makeSub({
      id: 'sub_demo_alpha',
      challenge_id: R,
      candidate_name: `${DEMO_MARKER} alpha`,
      score_milli: 245_000,
      benchmark: benchmark(245_000, 2.45),
      verified_surface: { challenge_id: R, verify_artifact: fd('verify-bin'), prepare_artifact: fd('prepare-bin'), public_artifacts: fd('public'), formal_tree: fd('formal-tree'), certificate_decl: 'Candidate.certificate', checker_image: fd('checker-image') },
      build: { toolchain_image: 'demo-fixture-build-image', reproducible: true, build_ns: 412_000_000_000 },
      logs: [{ name: 'BUILD', stage: 'BUILT', truncated: false, text: 'DEMO FIXTURE build log\n   Compiling prover v0.1.0\n    Finished release' }],
    }),
    makeSub({
      id: 'sub_demo_beta',
      challenge_id: R,
      parent: 'sub_demo_alpha',
      change_class: 'PROVER_ONLY',
      candidate_name: `${DEMO_MARKER} alpha (faster prover)`,
      score_milli: 312_500,
      benchmark: benchmark(312_500, 3.1),
      gates: gates(allPass(), formalReused),
      created_at: '2026-09-05T09:00:00Z',
      verified_surface: { challenge_id: R, verify_artifact: fd('verify-bin'), prepare_artifact: fd('prepare-bin'), public_artifacts: fd('public'), formal_tree: fd('formal-tree'), certificate_decl: 'Candidate.certificate', checker_image: fd('checker-image') },
    }),
    makeSub({
      id: 'sub_demo_revoked',
      challenge_id: R,
      candidate_name: `${DEMO_MARKER} gamma`,
      score_milli: 500_000,
      benchmark: benchmark(500_000, 5),
      revoked: { reason: 'DEMO FIXTURE: axiom allowlist entry withdrawn by governance', revoked_at: '2026-09-10T12:00:00Z', revoked_by: 'demo-fixture-governance' },
      revocation_history: [{ action: 'revoked', reason: 'DEMO FIXTURE: axiom allowlist entry withdrawn', at: '2026-09-10T12:00:00Z', by: 'demo-fixture-governance' }],
    }),
    makeSub({ id: 'sub_demo_exp', challenge_id: R, tier: 'experimental', candidate_name: `${DEMO_MARKER} gpu experiment`, decision: 'REJECTED', accepted: false, reason_codes: ['OBLIGATION_UNDISCHARGED'], benchmark: benchmark(null, 6), evidence_graph: evidenceGraph({ missing: true }) }),
    makeSub({ id: 'sub_demo_devbox', challenge_id: R, tier: 'demo', candidate_name: `${DEMO_MARKER} bwrap-dev run`, decision: 'REJECTED', accepted: false, reason_codes: ['DEMO_ONLY'], benchmark: benchmark(null, 9) }),
    makeSub({
      id: 'sub_demo_rejected',
      challenge_id: E,
      candidate_name: `${DEMO_MARKER} shortcut prover`,
      decision: 'REJECTED',
      accepted: false,
      reason_codes: ['FORBIDDEN_AXIOM', 'SORRY_FOUND'],
      gates: gates(
        { PKG_WELLFORMED: 'PASS', BUILD_REPRODUCIBLE: 'PASS', ARTIFACT_BINDING: 'PASS', AXIOM_AUDIT: 'FAIL' },
        { AXIOM_AUDIT: { reason_codes: ['FORBIDDEN_AXIOM', 'SORRY_FOUND'], summary: 'DEMO FIXTURE: sorryAx found in Candidate.certificate' } },
      ),
      evidence_graph: evidenceGraph({ missing: true }),
    }),
    makeSub({
      id: 'sub_demo_pending',
      challenge_id: E,
      candidate_name: `${DEMO_MARKER} in-flight`,
      stage: 'BUILT',
      decision: null,
      accepted: null,
      change_class: null,
      gates: gates({ PKG_WELLFORMED: 'PASS', BUILD_REPRODUCIBLE: 'PASS' }),
      evidence_graph: null,
    }),
    makeSub({
      id: 'sub_demo_hostile',
      challenge_id: E,
      tier: 'experimental',
      agent: 'demo-fixture-‮evil‬',
      candidate_name: `${DEMO_MARKER} <script>alert(1)</script>`,
      backend_family: '<img src=x onerror=alert(1)>',
      decision: 'REJECTED',
      accepted: false,
      reason_codes: ['CLAIM_MISMATCH'],
      gates: gates(
        { PKG_WELLFORMED: 'PASS', CONFORMANCE_DIFFERENTIAL: 'FAIL' },
        { CONFORMANCE_DIFFERENTIAL: { reason_codes: ['CLAIM_MISMATCH'], summary: '<img src=x onerror=alert(2)> \u001b[31mred\u001b[0m' } },
      ),
      logs: [{ name: 'prove.stderr <b>bold</b>', stage: 'CONFORMANCE_CHECKED', truncated: true, text: '\u001b[1;31mERROR\u001b[0m <script>alert(3)</script>\n‮txt.exe‬\r\nline\u0007bell' }],
    }),
    makeSub({ id: 'sub_demo_plumbing', challenge_id: demo.id, tier: 'demo', candidate_name: `${DEMO_MARKER} plumbing run`, decision: 'ADMITTED', accepted: true, score_milli: 900_000, benchmark: benchmark(900_000, 9) }),
  ];
  return { challenges: [empty, ranked, demo], submissions };
}
