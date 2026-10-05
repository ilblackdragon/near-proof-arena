import ZkFormal.Prover.Statements
import ZkFormal.Assembly.Guard
import ZkFormal.Stark.Laws
import ZkFormal.Stark.SchedOk

/-!
# ZkFormal.Prover.Compose — `ProverComplete` and the prover budgets for np-udr-stark

The candidate's honest prover `npProver S A traceOf` (a `TreeProver`): from a claim
`c` and witness `w` it takes the backend trace `traceOf c w`, picks (by choice — the
model is never executed) a well-formed perfectly complete honest IOP prover for it
(`NpIopCompleteStmt`), and BCS-compiles it with `proveTree`.  If no such IOP prover
exists (the witness is not valid) it uses the empty header, which every AIR with a
table rejects, so the proof is empty and no oracle query is made.

* `np_proverComplete`: `ProverComplete` for the guarded deployed verifier, for every
  hash function, from the generic BCS layer (`BcsCompleteStmt`, `SizeStmt`) and the
  np IOP layer (`NpIopCompleteStmt`).
* `np_prover_unit`, `np_prover_chunk`: the budgets `NPu = 2^32`, `NPq = numChunks`.
-/

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Assembly

/-- The deployed np IOP verifier. -/
abbrev Vd (A : Air) : IopSpec Fp Fp8 := Iop.verifier Fp Fp8 A Params.default

/-- Good honest IOP provers for a trace. -/
def NpGood (A : Air) (cb : Bytes) (tr : Trace Fp) (pr : IopProver Fp Fp8) : Prop :=
  pr.hdr = trHdr A tr ∧ ProverWf (Vd A) pr cb ∧ IopComplete (Vd A) pr cb

open Classical in
/-- The honest IOP prover chosen for a trace (empty header if none exists). -/
noncomputable def npIop (A : Air) (cb : Bytes) (tr : Trace Fp) : IopProver Fp Fp8 :=
  if h : ∃ pr, NpGood A cb tr pr then Classical.choose h else ⟨[], fun _ => []⟩

/-- **The candidate's honest prover** for challenge `S`, AIR `A`, and the backend
trace map `traceOf`. -/
noncomputable def npProver (S : ChallengeSpec) (A : Air) (traceOf : S.Claim → S.Witness → Trace Fp) :
    TreeProver S :=
  ⟨fun pub c w => proveTree (Vd A) (npIop A (S.encodeClaim c) (traceOf c w)) pub (S.encodeClaim c)⟩

/-- **The deployed verifier model**: claim guard, then L4's compiled verifier. -/
def npVerifier (S : ChallengeSpec) (A : Air) : TreeVerifier :=
  guardTree (claimOk S) (verifier Fp Fp8 A Params.default)

theorem headerOk_nil (A : Air) (hA : A.tables ≠ []) : headerOk A Params.default [] = false := by
  cases h : A.tables with
  | nil => exact absurd h hA
  | cons T Ts => simp [headerOk, h]

theorem npIop_spec (A : Air) (cb : Bytes) (tr : Trace Fp) :
    NpGood A cb tr (npIop A cb tr) ∨ (npIop A cb tr).hdr = [] := by
  unfold npIop
  split
  · rename_i h; exact Or.inl (Classical.choose_spec h)
  · exact Or.inr rfl

theorem proveTree_bad (V : IopSpec Fp Fp8) (pr : IopProver Fp Fp8) (pub cb : Bytes)
    (h : V.headerOk pr.hdr = false) : proveTree V pr pub cb = .pure [] := by
  simp [proveTree, h]

/-- Unit budget of the honest prover. -/
theorem np_prover_unit (hQ : ProverQStmt) (hNQ : NpProverQStmt) (S : ChallengeSpec) (A : Air)
    (hA : A.tables ≠ []) (traceOf : S.Claim → S.Witness → Trace Fp) (pub : Bytes) (c : S.Claim)
    (w : S.Witness) : OracleComp.QueryBound unitWeight ((npProver S A traceOf).tree pub c w) (2 ^ 32) := by
  show OracleComp.QueryBound unitWeight (proveTree (Vd A) _ pub _) _
  rcases npIop_spec A (S.encodeClaim c) (traceOf c w) with ⟨_, hwf, _⟩ | hnil
  · exact (hQ Fp Fp8 (Vd A) _ pub _ hwf).mono (hNQ A _ hwf.hdrOk)
  · rw [proveTree_bad (Vd A) _ pub _ (by rw [hnil]; exact headerOk_nil A hA)]
    exact .pure _ _

/-- Chunk-query budget of the honest prover. -/
theorem np_prover_chunk (hC : ProverChunkStmt) (S : ChallengeSpec) (A : Air)
    (traceOf : S.Claim → S.Witness → Trace Fp) (pub : Bytes) (c : S.Claim) (w : S.Witness) :
    OracleComp.QueryBound (qWeight Bcs.chunkDec) ((npProver S A traceOf).tree pub c w)
      Params.default.numChunks :=
  hC Fp Fp8 (Vd A) _ pub _

/-- **`ProverComplete`** of the honest prover against the guarded deployed verifier,
for every hash function. -/
theorem np_proverComplete (hB : BcsCompleteStmt) (hSz : SizeStmt) (hN : NpIopCompleteStmt)
    (S : ChallengeSpec) (A : Air) (traceOf : S.Claim → S.Witness → Trace Fp)
    (hcomp : ∀ c w, S.Domain c → S.Rel c w →
      Holds A (Udr.pubOf Fp (S.encodeClaim c)) (traceOf c w) ∧
      headerOk A Params.default (trHdr A (traceOf c w)) = true)
    (maxB : Nat) (hsize : ∀ hdr, headerOk A Params.default hdr = true →
      sizeBound (Vd A) hdr ≤ maxB) (hmax : maxB ≤ Params.default.maxProofBytes) (pub : Bytes) :
    ProverComplete S (npVerifier S A).toVerifier (npProver S A traceOf).toProver pub maxB := by
  intro H c w hd hr
  obtain ⟨hh, hok⟩ := hcomp c w hd hr
  obtain ⟨pr, hpr⟩ := hN A (S.encodeClaim c) (traceOf c w) hh hok
  have hgood : NpGood A (S.encodeClaim c) (traceOf c w) (npIop A (S.encodeClaim c) (traceOf c w)) := by
    unfold npIop
    rw [dif_pos ⟨pr, hpr⟩]
    exact Classical.choose_spec (⟨pr, hpr⟩ : ∃ pr, NpGood A (S.encodeClaim c) (traceOf c w) pr)
  obtain ⟨_, hwf, hcpl⟩ := hgood
  have hlen : (runH (pureH H) (proveTree (Vd A) (npIop A (S.encodeClaim c) (traceOf c w)) pub
      (S.encodeClaim c)) ()).1.length ≤ maxB :=
    Nat.le_trans (hSz Fp Fp8 (Vd A) _ pub _ H hwf) (hsize _ hwf.hdrOk)
  refine ⟨hlen, ?_⟩
  show (runH (pureH H) (if claimOk S (S.encodeClaim c) then _ else _) ()).1 = true
  rw [if_pos (claimOk_encode S c)]
  exact hB Fp Fp8 (Vd A) _ pub _ H (schedOk A Params.default) hwf hcpl (Nat.le_trans hlen hmax)

end ZkFormal.Prover
