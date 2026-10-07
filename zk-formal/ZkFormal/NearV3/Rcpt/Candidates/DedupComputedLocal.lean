import ZkFormal.NearV3.Rcpt.Candidates.DedupTable
import ZkFormal.Near.Render.Proof.NodeEv

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupTable
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- Away from skipped headers, the patched polynomials have exactly the original
source-table validity predicate. This includes segment and padding rows. -/
theorem patched_of_not_dup (C D : Nat → Int) (fst lst trn : Int) (pub : Nat → Int)
    (hd : C SrcpV3.dup = 0)
    (h : ∀ ex ∈ SrcpV3.constraints, ev C D fst lst trn pub ex = 0) :
    ∀ ex ∈ SrcpV3.constraints.mapIdx patch, ev C D fst lst trn pub ex = 0 := by
  simp [SrcpV3.dup] at hd
  simpa [List.forall_mem_append, patch, computedRoot, endRow,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k,
    Dsl.smul, Dsl.sum, Dsl.mid, SrcpV3.dup, hd] using h

/-- The only extra conditions on a computed root are authenticated repetition
metadata and its empty-list length; no extra depth or row-domain bound is introduced. -/
theorem computed_constraints (C D : Nat → Int) (fst lst trn : Int) (pub : Nat → Int)
    (hd : C SrcpV3.dup = 0)
    (hb : C repeated * (C repeated - 1) = 0)
    (hr : C repeated * (1 - C SrcpV3.rt) = 0)
    (hL : C SrcpV3.rt * C repeated * (C SrcpV3.L - 12) = 0)
    (h : ∀ ex ∈ SrcpV3.constraints, ev C D fst lst trn pub ex = 0) :
    ∀ ex ∈ constraints, ev C D fst lst trn pub ex = 0 := by
  rw [constraints, List.forall_mem_append]
  refine ⟨patched_of_not_dup C D fst lst trn pub hd h, ?_⟩
  simpa [additions, ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not,
    Dsl.c, Dsl.n, Dsl.k, hd, Int.sub_eq_add_neg] using And.intro hb (And.intro hr hL)

end ZkFormal.NearV3.Rcpt.Candidates.DedupTable
