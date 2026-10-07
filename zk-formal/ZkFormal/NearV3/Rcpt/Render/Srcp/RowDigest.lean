import ZkFormal.NearV3.Rcpt.Render.Srcp.DigestFields

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

/-- All active digest lookups use well-formed block counters; padding has no loads. -/
theorem row_digest {bs : List SrcpB} (h : SrcpWf bs) (r : Nat)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n ∈ digestIndices) :
    ev (fun x => (cell bs r x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  by_cases hr : r < R bs
  · have hm : (recs bs).getD r default ∈ recs bs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
      exact List.getElem_mem _
    have hh := mem_recs hm
    have hB : bs.getD ((recs bs).getD r default).1 default ∈ bs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh.1]
      exact List.getElem_mem _
    simp only [cell, hr, ite_true, rowFrame]
    exact digest_polynomials _ _ _ _ hh.2 (item_predecessor h _ hB) D P fst lst trn n hn
  · have hp : R bs ≤ r := by omega
    simp only [digestIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn | hn | hn | hn | hn <;> subst n
    all_goals simp [padding_cell hp, SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c,
      Dsl.not, Dsl.mid, Dsl.smul, Dsl.k,
      SrcpV3.rt, SrcpV3.cId, SrcpV3.cLen, SrcpV3.qe, SrcpV3.le, SrcpV3.wf,
      SrcpV3.lf, SrcpV3.aw, SrcpV3.j, SrcpV3.L, SrcpV3.q, SrcpV3.pl, SrcpV3.sz]

theorem digest_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (n : Nat) (hn : n ∈ digestIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => ((tr.cell tt ((r + 1) % tr.height tt) x).toNat : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [← ofNat_int, Fp.ofNat_toNat]
  · exact row_digest h r _ _ _ _ _ n hn

end ZkFormal.NearV3.Render.SrcpGen
