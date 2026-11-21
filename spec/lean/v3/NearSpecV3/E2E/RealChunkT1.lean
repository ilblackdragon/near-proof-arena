import NearSpecV3.E2E.Templates
import NearSpecV3.E2E.StmtEnc
import NearSpecV3.E2E.T1Run

/-!
# E2E-M11h: non-vacuity of the T1 segment system on T1 itself (on demand)

T1 = `d3c8/d3/02-h10196-s3` (plan §4.1). `t1_accepts` (`E2E/T1Run.lean`) is T1's accepting `CM`
run, kernel-checked in two pieces (`INTAKE` against an oracle-printed literal intake by kernel
`Eq.refl`; the other twelve steps by `decide +kernel`; 27.1 GB peak, under the 34 GB cap that the
monolithic `decide` of the checker exceeds). Through the proved factorisation `cm_iff`:

* `t1_rel : Tier.rel .allFeatures t1Claim t1Wit` (the relation itself, from the run).

* `cm_run_t1`: `CM` has an accepting run on T1 from `init` to `done H o` with `headerOk H o`
  (segmented, non-genesis path: `segment_no_genesis_t1`), with a finite clock.
* `t1Stmt`: T1's public statement (the claim's public parts and section C), with
  `assemble_t1 : assemble t1Stmt.ci t1SecB t1Stmt.secC = claim bytes` (the claim re-encodes to its
  own bytes: kernel-checked) and `t1_wf` (`Claim.wf`).
* `t1_final_pub`: the run's last configuration passes `FinalOutPub t1Stmt` — the comparison with
  the header outputs of T1's **public** `chunk_inner`.
* **`t1_e2e_stmt : E2EStmt t1Stmt`**.
* **`t1_honest_chain`**: for any view `V` and lane AIRs `A` satisfying the per-template
  completeness obligations, T1's run is a valid chain of the T1 system (`Templates.lean`) whose
  root boundaries pass the reference wrap checks: the honest-side premises of `e2e_sound_t1` hold
  on T1's actual run. `t1_chain_shape`: the chain starts with `INIT` and its meanings compose
  (`cm_decomp`) to T1's run; the boundary at every cut is the digest of a well-formed record that
  decodes back (`cut_roundtrip`).

Build: `HEAVY_MEM=34G /data/illia/nearproof-deps/bin/heavy lake build NearSpecV3.E2E.RealChunkT1`
(the kernel evaluation in `T1Run` dominates).
-/

namespace NearSpecV3.E2E.T1
open NearSpec NearSpecV3 NearSpecV3.Examples NearSpecV3.Successor NearSpecV3.E2E
open NearSpecV3.E2E.Bnd

/-- T1's claim and witness bytes. -/
abbrev t1Claim : Bytes := claimD3_02_h10196_s3
abbrev t1Wit : Bytes := witnessD3_02_h10196_s3

/-- `CM` accepts T1. -/
theorem cm_accepts_t1 : CMAccepts t1Claim t1Wit := by
  obtain ⟨cf, h, ha⟩ := t1_accepts
  exact ⟨cf, steps_iff_stepsN.2 ⟨13, h⟩, ha⟩

/-- **T1 satisfies the `allFeatures` relation** (from the kernel-checked run, through `cm_iff`). -/
theorem t1_rel : Tier.rel .allFeatures t1Claim t1Wit := (cm_iff _ _).2 cm_accepts_t1

set_option maxRecDepth 200000 in
/-- T1 takes the segmented path (`INTAKE` → engine steps → `FINAL`). -/
theorem segment_no_genesis_t1 : segmentHasGenesis t1Claim = false := by decide +kernel

/-- **An accepting run of T1** with a finite global clock, ending in `done H o`, `headerOk`. -/
theorem cm_run_t1 :
    ∃ n H o, StepsN n (.init t1Claim t1Wit) (.done H o) ∧ headerOk H o = true := by
  obtain ⟨cf, hs, ha⟩ := cm_accepts_t1
  obtain ⟨n, hn⟩ := steps_iff_stepsN.1 hs
  cases cf with
  | done H o => exact ⟨n, H, o, hn, ha⟩
  | doneG =>
    have := steps_init_doneG hs
    rw [segment_no_genesis_t1] at this
    cases this
  | _ => simp [Conf.accepting] at ha

/-! ## T1's public statement -/

/-- The fallback of `t1C` (never taken: `t1C_encode`). -/
def emptyClaim : Claim := ⟨0, [], [], [], [], 0, 0, [], [], [], [], none⟩

/-- T1's decoded claim. -/
def t1C : Claim :=
  match decodeClaimE t1Claim with
  | .ok c => c
  | .error _ => emptyClaim

/-- T1's public statement: section A (`chunk_inner` and the trusted header values) and section C. -/
def t1Stmt : PublicStmt := ⟨pubOf t1C, secCOf t1C⟩

/-- T1's private section B. -/
def t1SecB : List BlockRec := t1C.blocks

theorem assembleClaim_t1 : assembleClaim t1Stmt.ci t1SecB t1Stmt.secC = t1C := assembleClaim_pub t1C

set_option maxRecDepth 200000 in
/-- T1's claim bytes are the canonical encoding of its decoded claim. -/
theorem t1C_encode : t1C.encode = t1Claim := by decide +kernel

set_option maxRecDepth 200000 in
/-- T1's claim is well-formed (`Claim.wf`: lengths and digest widths). -/
theorem t1_wf : t1C.wf = true := by decide +kernel

/-- **T1's bytes are the assembly of its public statement and section B.** -/
theorem assemble_t1 : assemble t1Stmt.ci t1SecB t1Stmt.secC = t1Claim := by
  rw [assemble, assembleClaim_t1, t1C_encode]

/-- **T1's accepting run passes the public final check** (`FinalOutPub`: the header outputs of
the public `chunk_inner`). -/
theorem t1_final_pub : ∃ H o, Steps (.init t1Claim t1Wit) (.done H o) ∧
    FinalOutPub t1Stmt (.done H o) := by
  obtain ⟨n, H, o, hn, hok⟩ := cm_run_t1
  have hs : Steps (.init t1Claim t1Wit) (.done H o) := steps_iff_stepsN.2 ⟨n, hn⟩
  refine ⟨H, o, hs, ?_, hok⟩
  have hs' : Steps (.init (assemble t1Stmt.ci t1SecB t1Stmt.secC) t1Wit) (.done H o) := by
    rw [assemble_t1]; exact hs
  exact final_header_public t1Stmt t1SecB t1Wit (by rw [assembleClaim_t1]; exact t1_wf) hs'

/-- **The E2E statement holds for T1.** -/
theorem t1_e2e_stmt : E2EStmt t1Stmt := by
  obtain ⟨H, o, hs, hf⟩ := t1_final_pub
  refine (e2e_stmt_iff_cm t1Stmt).2 ⟨t1SecB, t1Wit, .done H o, ?_, finalOutPub_accepting _ _ hf⟩
  rw [assemble_t1]; exact hs

/-! ## T1's canonical statement bytes -/

/-- T1's statement is well-formed. -/
theorem t1Stmt_wf : t1Stmt.wf = true :=
  assemble_wf t1Stmt t1SecB (by rw [assembleClaim_t1]; exact t1_wf)

set_option maxRecDepth 200000 in
/-- **T1's canonical statement bytes `S`** (`StmtEnc.lean`): 1,007 B (lane I's I-1 working
encoding, 1,003 B, plus the four zero bytes of the empty block vector). -/
theorem t1_S_len : t1Stmt.encode.length = 1007 := by decide +kernel

set_option maxRecDepth 200000 in
/-- **T1's `claimDigest`** = `bdigest S` (42-B truncated SHA-384), kernel-evaluated:
`bb5aad11ba6ba32d…9f2f01`. -/
theorem t1_claimDigest : claimDigest t1Stmt = [187, 90, 173, 17, 186, 107, 163, 45, 145, 115, 159, 19, 162, 219, 213, 68, 242, 66, 13, 119, 11, 205, 44, 63, 222, 157, 220, 14, 28, 2, 113, 12, 174, 226, 142, 94, 158, 78, 41, 159, 47, 1] := by decide +kernel

/-! ## T1's run as a chain of the T1 system -/

/-- **T1's run factors into template segments** starting with `INIT` at T1's own bytes and ending
at an accepting `done` with the public header. -/
theorem t1_chain_shape : ∃ H o L, FinalOutPub t1Stmt (.done H o) ∧
    MChain (.base (.init t1Claim t1Wit)) L (.base (.done H o)) ∧
    ∃ c1 rest, L = (.init, .base (.init t1Claim t1Wit), c1) :: rest := by
  obtain ⟨H, o, hs, hf⟩ := t1_final_pub
  obtain ⟨L, hL⟩ := cm_decomp hs
  refine ⟨H, o, L, hf, hL, ?_⟩
  cases L with
  | nil => cases hL
  | cons e rest =>
    obtain ⟨h1, hm, _⟩ := hL
    obtain ⟨k, x, x'⟩ := e
    simp only at h1 hm
    subst h1
    cases k with
    | init => exact ⟨x', rest, rfl⟩
    | state => cases hm
    | rt => cases hm
    | wasm => cases hm
    | final => cases hm with | run hfs _ => exact absurd hfs id

/-- **Non-vacuity on T1.** For any view and any lane AIRs meeting the per-template completeness
obligations, T1's actual run is a valid chain of the T1 system whose root boundaries pass the
wrap checks for T1's public statement: the honest side of `e2e_sound_t1` holds on T1. -/
theorem t1_honest_chain (V : ViewImpl) (A : Airs) (hc : ∀ k, TmplComplete V A k) :
    ∃ ch : SegChain (sys V A).toSeg, ch.Valid ∧ (t1Wrap V A).InitOK t1Stmt ch.b0 ∧
      (t1Wrap V A).FinalOK t1Stmt ch.bN := by
  obtain ⟨H, o, hs, hf⟩ := t1_final_pub
  have hs' : Steps (.init (assemble t1Stmt.ci t1SecB t1Stmt.secC) t1Wit) (.done H o) := by
    rw [assemble_t1]; exact hs
  exact honest_chain V A hc t1Stmt t1SecB t1Wit _ hs' hf

#print axioms t1_rel
#print axioms cm_run_t1
#print axioms assemble_t1
#print axioms t1_S_len
#print axioms t1_claimDigest
#print axioms t1_e2e_stmt
#print axioms t1_chain_shape
#print axioms t1_honest_chain

end NearSpecV3.E2E.T1
