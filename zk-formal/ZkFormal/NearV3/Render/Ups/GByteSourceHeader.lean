import ZkFormal.NearV3.Render.Ups.SourceHeaderReads

/-! Header read constraints from the ordinary serialized source node. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteSourceHeader : List Expr := (UpsV3.cBytes.drop 54).take 1 ++ (UpsV3.cBytes.drop 56).take 3

def HeaderNeeded (I : UpsInst) (Q : UpsPartI) : Prop :=
  Q.kind=4 ∨ Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true

def HeaderInput (I : UpsInst) (Q : UpsPartI) :=
  HeaderNeeded I Q → {e : SourceLayout Q // SourceHeader I Q e}

theorem byte_source_header_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (hi : HeaderInput I Q) (hb : SourceBytes Q) (hf : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteSourceHeader, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    mul3 (.add kM (c xcp)) (c sTAG) (sub hiE (.add (smul 2 (c qtl)) (c UpsV3.podd))),
    .mul (mul3 (c sHPL) (c fs) kM) (sub (c plen) (Dsl.sum [Dsl.k 45, smul 4 (c qtl), c UpsV3.phk])),
    mul3 (c sBM) (c fs) (.mul (c xcp) (sub (c plen) (Dsl.sum [Dsl.k 45, smul 4 (c qtl), c UpsV3.phk]))),
    mul3 (c kRBV) (c sTAG) (sub (c rb) (Dsl.k 1))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl <;> apply cast0
  · by_cases hs : (fieldAt Q.shape p).1=0
    · by_cases hm : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true
      · obtain ⟨src,h⟩ := hi (Or.inr hm)
        have heq : ev C D fst lst trn P hiE = ev C D fst lst trn P (.add (smul 2 (c qtl)) (c UpsV3.podd)) := by
          rw [read_hi hb (Or.inl hs) hC]
          ups_ev [hC]
          cellsimp
          rw [hs,header_tag_position _ _ _ hm]
          simpa only [Lean.Omega.Int.natCast_ofNat] using h.flag_high hm
        change _ * (ev C D fst lst trn P hiE + -ev C D fst lst trn P (.add (smul 2 (c qtl)) (c UpsV3.podd)))=0
        exact gate_sub_eq heq
      · simp only [not_or] at hm
        ups_ev [hC]; cellsimp; simp [ind,xcpV,hm.1,hm.2.1,hm.2.2]
    · ups_ev [hC]; cellsimp; simp [ind,hs]
  · ups_ev [hC]; cellsimp
    by_cases hs : (fieldAt Q.shape p).1=1
    · by_cases hz : (fieldAt Q.shape p).2.1=0
      · by_cases hm : Q.kind=6 ∨ Q.kind=7
        · obtain ⟨src,h⟩ := hi (Or.inr (by rcases hm with h | h; exact Or.inl h; exact Or.inr (Or.inl h)))
          have heq := h.length (by rcases hm with h|h; exact Or.inl h; exact Or.inr (Or.inl h))
          simp [heq,Int.add_assoc,Int.add_right_neg]
        · simp only [not_or] at hm
          simp [ind,hm.1,hm.2]
      · simp [ind,hz]
    · simp [ind,hs]
  · ups_ev [hC]; cellsimp
    by_cases hs : (fieldAt Q.shape p).1=6
    · by_cases hm : XcpB I Q=true
      · obtain ⟨src,h⟩ := hi (Or.inr (Or.inr (Or.inr hm)))
        have heq := h.length (Or.inr (Or.inr hm))
        simp [heq,Int.add_assoc,Int.add_right_neg]
      · simp [xcpV,ind,hm]
    · simp [ind,hs]
  · ups_ev [hC]; cellsimp
    by_cases hs : (fieldAt Q.shape p).1=0
    · by_cases hm : Q.kind=4
      · obtain ⟨src,h⟩ := hi (Or.inl hm)
        have heq : rbV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p=1 := by
          rw [hs]; exact h.value_tag _ _ hf hs hm
        simpa only [Lean.Omega.Int.natCast_ofNat] using gate_sub_eq (g := ind (Q.kind=4)*ind ((fieldAt Q.shape p).1=0)) heq
      · simp [ind,hm]
    · simp [ind,hs]

theorem cByteSourceHeader_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hi : ∀ I ∈ insts, ∀ k, k < nQ I → HeaderInput I (part I k))
    (hb : ∀ I ∈ insts, ∀ k, k < nQ I → SourceBytes (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteSourceHeader := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := by
      rcases List.mem_append.1 he with h | h <;>
        exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteSourceHeader.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact byte_source_header_q (hi _ (inst_mem hi') k hk) (hb _ (inst_mem hi') k hk)
      (hf _ (inst_mem hi') k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render
