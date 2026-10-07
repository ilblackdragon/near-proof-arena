import ZkFormal.NearV3.Rcpt.Extract.V.ListBlocks

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Complete list blocks, with no gaps, ending at the first padding row. -/
inductive ListChain (tr : Trace Fp) (tt : Nat) : Nat → List ListBlock → Nat → Prop where
  | last {B : ListBlock} : ListBlockWf tr tt B → tr.cell tt B.stop act=0 →
      ListChain tr tt B.start [B] B.stop
  | cons {B : ListBlock} {bs : List ListBlock} {e : Nat} : ListBlockWf tr tt B →
      ListChain tr tt B.stop bs e → ListChain tr tt B.start (B::bs) e

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem ListChain.nonempty {s bs e} (h : ListChain tr tt s bs e) : bs≠[] := by
  cases h <;> simp

theorem ListChain.blocks {s bs e} (h : ListChain tr tt s bs e) :
    ∀ B∈bs, ListBlockWf tr tt B := by
  induction h with
  | last hw _ => simpa using hw
  | cons hw _ ih => intro B hb; rcases List.mem_cons.mp hb with rfl|hb; exact hw; exact ih B hb

theorem ListChain.end_padding {s bs e} (h : ListChain tr tt s bs e) :
    e<tr.height tt ∧ tr.cell tt e act=0 := by
  induction h with
  | last hw hp => exact ⟨hw.bound.2,hp⟩
  | cons _ _ ih => exact ih

theorem ListChain.rows {s bs e} (h : ListChain tr tt s bs e) :
    e=s+(bs.map ListBlock.rows).sum := by
  induction h with
  | last hw _ => simpa using hw.stop_eq
  | cons hw _ ih => have hh := hw.stop_eq; simp only [List.map_cons,List.sum_cons]; omega

theorem list_chain_from (hL : TableLocal RcptV3.table tr tt pub) (fuel s : Nat)
    (hf : tr.height tt-s≤fuel) (hs : s<tr.height tt)
    (hc : tr.cell tt s sCL=1) (hfs : tr.cell tt s fs=1) (hi : tr.cell tt s idx=0) :
    ∃ bs e, ListChain tr tt s bs e := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨rs,hw⟩ := list_block_from hL hs hc hfs hi
    rcases hw.boundary.2 with hp | ⟨hn,hnf,hni⟩
    · exact ⟨[⟨s,rs⟩],_,.last hw hp⟩
    · have hb := hw.bound
      obtain ⟨bs,e,ht⟩ := ih _ (by simp only at hb; omega) hb.2 hn hnf hni
      exact ⟨⟨s,rs⟩::bs,e,.cons hw ht⟩

/-- Local constraints force complete list/header decomposition from physical row zero. -/
theorem extract_lists (hL : TableLocal RcptV3.table tr tt pub) :
    ∃ bs e, ListChain tr tt 0 bs e := by
  have hH := height_ge hL
  have hh := row0 hL (by omega)
  exact list_chain_from hL (tr.height tt) 0 (by omega) (by omega) hh.1 hh.2.1 hh.2.2.1

/-- No active receipt rows can resume after the extracted final list. -/
theorem ListChain.padding (hL : TableLocal RcptV3.table tr tt pub)
    {s bs e} (h : ListChain tr tt s bs e) {r : Nat} (her : e≤r) (hr : r<tr.height tt) :
    tr.cell tt r act=0 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le her
  induction d with
  | zero => simpa using h.end_padding.2
  | succ d ih =>
    have hp := pad hL (r := e+d) (by omega) (ih (by omega) (by omega))
    simpa only [Nat.add_succ] using hp

end ZkFormal.NearV3.RcptV3Proof
