import ZkFormal.NearV3.Extract.Node.Segs

/-!
# ZkFormal.Near.Extract.NodeWalk — the field sequence of a node, by type
-/

namespace ZkFormal.NearV3.NodeProof3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}

/-- Context: a node segment and its fields. -/
structure NodeCtx (tr : Trace Fp) (s ℓ : Nat) (fl : List (Nat × Nat)) : Prop where
  seg : IsSeg (one tr act) (one tr nf) (one tr nl) s ℓ
  bound : s + ℓ ≤ tr.height T_NODE
  fields : Fields tr s ℓ fl

variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

/-- At the last row of field `i`: `fe`, same state as the field start. -/
theorem fieldEndRow {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length) :
    tr.cell T_NODE (s + fl[i].1 + fl[i].2 - 1) fe = 1 ∧
    (∀ x ∈ states, tr.cell T_NODE (s + fl[i].1 + fl[i].2 - 1) x = tr.cell T_NODE (s + fl[i].1) x) ∧
    tr.cell T_NODE (s + fl[i].1 + fl[i].2 - 1) idx = ((fl[i].2 - 1 : Nat) : Fp) := by
  obtain ⟨hF, -⟩ := hC.fields.field _ (List.getElem_mem hi)
  have e : s + fl[i].1 + fl[i].2 - 1 = s + fl[i].1 + (fl[i].2 - 1) := by have := hF.pos; omega
  rw [e]
  exact ⟨(hF.fe _ (by have := hF.pos; omega)).2 (by have := hF.pos; omega), hF.st _ (by have := hF.pos; omega),
    hF.idx _ (by have := hF.pos; omega)⟩

/-- A field that is not the last is followed by the next field, whose state the
succession rules give. -/
theorem notLast {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length)
    (hm : tr.cell T_NODE (s + fl[i].1) sMEM = 0) : i + 1 < fl.length := by
  rcases Nat.lt_or_ge (i + 1) fl.length with h | h
  · exact h
  · exfalso
    have hl : i = fl.length - 1 := by omega
    have hend := hC.fields.last (by omega)
    obtain ⟨he, hst, -⟩ := fieldEndRow hL hC hi
    -- the last row of the last field is the node end, which is a MEM row
    have hnl : tr.cell T_NODE (s + ℓ - 1) nl = 1 := by have := hC.seg.2.2.1; rwa [one_iff] at this
    have := ((rowFacts hL (by have := hC.bound; have := hC.seg.1; omega)).2.2.2.2.1 hnl).2.2.1
    subst hl
    rw [show s + fl[fl.length - 1].1 + fl[fl.length - 1].2 - 1 = s + ℓ - 1 by omega] at hst
    rw [hst sMEM (by simp [states]), hm] at this
    exact fp_zero_ne_one this

theorem nextStart {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i + 1 < fl.length) :
    s + fl[i + 1].1 = s + fl[i].1 + fl[i].2 - 1 + 1 := by
  rw [hC.fields.next hi]; have := (hC.fields.field _ (List.getElem_mem (by omega : i < fl.length))).1.pos; omega

/-- The successor rules at the end of field `i`, stated about the next field's start. -/
theorem nextState {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i + 1 < fl.length) :
    let K := fun x => tr.cell T_NODE (s + fl[i].1) x
    let N := fun x => tr.cell T_NODE (s + fl[i + 1].1) x
    (K sTAG = 1 → N sHPL = K tl + K te ∧ N sBM = K tb1 ∧ N sVLEN = K tb2) ∧
    (K sHPL = 1 → N sHPF = 1) ∧
    (K sHPF = 1 → N sKEY = 1 - K nokey ∧ N sVLEN = K nokey * K tl ∧ N sCH = K nokey * K te) ∧
    (K sKEY = 1 → N sVLEN = K tl ∧ N sCH = K te) ∧
    (K sVLEN = 1 → N sVH = 1) ∧
    (K sVH = 1 → N sMEM = K tl ∧ N sBM = K tb2) ∧
    (K sBM = 1 → N sMEM = K nochild ∧ N sCH = 1 - K nochild) ∧
    (K sCH = 1 → N sCH + N sMEM = 1 ∧ N sMEM = K lastw) := by
  intro K N
  have hi' : i < fl.length := by omega
  obtain ⟨he, hst, -⟩ := fieldEndRow hL hC hi'
  have hF := (hC.fields.field _ (List.getElem_mem hi')).1
  have hF1 := (hC.fields.field _ (List.getElem_mem hi))
  have hb : s + fl[i].1 + fl[i].2 - 1 + 1 < tr.height T_NODE := by
    have e1 := hC.fields.next hi; have e2 := hF1.2; have e3 := hC.bound; have e4 := hF1.1.pos
    have e5 := hF.pos
    omega
  have S := succ hL hb he
  rw [← nextStart hL hC hi] at S
  -- node constants at the end row equal those at the field start (same node)
  have hcst : ∀ x ∈ nodeConst, tr.cell T_NODE (s + fl[i].1 + fl[i].2 - 1) x = tr.cell T_NODE (s + fl[i].1) x := by
    intro x hx
    have key : ∀ d, d < fl[i].2 → tr.cell T_NODE (s + fl[i].1 + d) x = tr.cell T_NODE (s + fl[i].1) x := by
      intro d; induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        have hnl : tr.cell T_NODE (s + fl[i].1 + d) nl = 0 :=
          zero_of hL (by have := hC.bound; omega) (by simp [boolCols])
            (hC.seg.2.2.2.2.2 (s + fl[i].1 + d) (by omega) (by
              have := hC.fields.next hi; have := hF1.2; have := hF1.1.pos; omega))
        have := (inNode hL (r := s + fl[i].1 + d) (by have := hC.bound; omega) (hF.act d (by omega)) hnl).2.2.2 x hx
        rw [show s + fl[i].1 + (d + 1) = s + fl[i].1 + d + 1 by omega, this, ih (by omega)]
    have := key (fl[i].2 - 1) (by have := hF.pos; omega)
    rwa [show s + fl[i].1 + (fl[i].2 - 1) = s + fl[i].1 + fl[i].2 - 1 by have := hF.pos; omega] at this
  have hlw : tr.cell T_NODE (s + fl[i].1 + fl[i].2 - 1) lastw = tr.cell T_NODE (s + fl[i].1) lastw ∨
      tr.cell T_NODE (s + fl[i].1) sCH = 0 := by
    rcases isBool hL (r := s + fl[i].1) (by have := hC.bound; have := hF1.2; omega) (x := sCH) (by simp [boolCols, states])
      with h | h
    · exact Or.inr h
    · left
      have key : ∀ d, d < fl[i].2 → tr.cell T_NODE (s + fl[i].1 + d) lastw = tr.cell T_NODE (s + fl[i].1) lastw := by
        intro d; induction d with
        | zero => intro _; rfl
        | succ d ih =>
          intro hd
          have hc : tr.cell T_NODE (s + fl[i].1 + d) sCH = 1 := by rw [hF.st d (by omega) sCH (by simp [states]), h]
          have hfe : tr.cell T_NODE (s + fl[i].1 + d) fe = 0 :=
            bool01 hL (by have := hC.bound; omega) (by simp [boolCols]) (fun h' => by
              have := (hF.fe d (by omega)).1 h'; omega)
          have := winConst hL (r := s + fl[i].1 + d) (by have := hC.bound; omega) hc hfe lastw (by simp [windowConst])
          rw [show s + fl[i].1 + (d + 1) = s + fl[i].1 + d + 1 by omega, this, ih (by omega)]
      have := key (fl[i].2 - 1) (by have := hF.pos; omega)
      rwa [show s + fl[i].1 + (fl[i].2 - 1) = s + fl[i].1 + fl[i].2 - 1 by have := hF.pos; omega] at this
  simp only [K, N]
  simp only [hst sTAG (by simp [states]), hst sHPL (by simp [states]), hst sHPF (by simp [states]),
    hst sKEY (by simp [states]), hst sVLEN (by simp [states]), hst sVH (by simp [states]),
    hst sBM (by simp [states]), hst sCH (by simp [states]),
    hcst tl (by simp [nodeConst]), hcst te (by simp [nodeConst]), hcst tb1 (by simp [nodeConst]),
    hcst tb2 (by simp [nodeConst]), hcst nokey (by simp [nodeConst]), hcst nochild (by simp [nodeConst])] at S
  refine ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1, S.2.2.2.2.1, S.2.2.2.2.2.1, S.2.2.2.2.2.2.1, fun h => ?_⟩
  have := S.2.2.2.2.2.2.2 h
  rcases hlw with e | e
  · rw [e] at this; exact this
  · rw [h] at e; exact absurd e fp_one_ne_zero

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

theorem fieldRow {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length) :
    s + fl[i].1 < tr.height T_NODE ∧ s + fl[i].1 + fl[i].2 ≤ tr.height T_NODE := by
  have := (hC.fields.field _ (List.getElem_mem hi)); have := this.1.pos; have := hC.bound; omega

/-- Field length from its state. -/
theorem fieldLength {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length) :
    let K := fun x => tr.cell T_NODE (s + fl[i].1) x
    (K sTAG = 1 → fl[i].2 = 1) ∧ (K sHPL = 1 → fl[i].2 = 4) ∧ (K sHPF = 1 → fl[i].2 = 1) ∧
    (K sKEY = 1 → (fl[i].2 + 1 : Nat) = (K hplen).toNat) ∧
    (K sVLEN = 1 → fl[i].2 = 4) ∧ (K sVH = 1 → fl[i].2 = 32) ∧ (K sBM = 1 → fl[i].2 = 2) ∧
    (K sCH = 1 → fl[i].2 = 32) ∧ (K sMEM = 1 → fl[i].2 = 8) := by
  intro K
  have hP : tr.height T_NODE + 4 < P := by have := height_le hL; unfold P; omega
  obtain ⟨he, hst, hidx⟩ := fieldEndRow hL hC hi
  have hF := (hC.fields.field _ (List.getElem_mem hi)).1
  have hr := fieldRow hL hC hi
  have FL := fieldLen hL (r := s + fl[i].1 + fl[i].2 - 1) (by have := hF.pos; omega) he
  simp only [hst sTAG (by simp [states]), hst sHPL (by simp [states]), hst sHPF (by simp [states]),
    hst sKEY (by simp [states]), hst sVLEN (by simp [states]), hst sVH (by simp [states]),
    hst sBM (by simp [states]), hst sCH (by simp [states]), hst sMEM (by simp [states]), hidx] at FL
  have conv : ∀ c : Nat, c < P → ((fl[i].2 - 1 : Nat) : Fp) = (c : Fp) → fl[i].2 = c + 1 := by
    intro c hc e
    have := ofNat_inj (by have := hF.pos; omega) hc e
    have := hF.pos; omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · exact conv 0 (by unfold P; omega) (FL.1 h)
  · exact conv 3 (by unfold P; omega) (FL.2.1 h)
  · exact conv 0 (by unfold P; omega) (FL.2.2.1 h)
  · have e := FL.2.2.2.1 h
    -- idx + 2 = hplen at the end row; hplen is node-constant
    have hcst : tr.cell T_NODE (s + fl[i].1 + fl[i].2 - 1) hplen = K hplen := by
      have key : ∀ d, d < fl[i].2 → tr.cell T_NODE (s + fl[i].1 + d) hplen = K hplen := by
        intro d; induction d with
        | zero => intro _; rfl
        | succ d ih =>
          intro hd
          have hnl : tr.cell T_NODE (s + fl[i].1 + d) nl = 0 := by
            have hfe : tr.cell T_NODE (s + fl[i].1 + d) fe = 0 :=
              bool01 hL (by omega) (by simp [boolCols]) (fun h' => by have := (hF.fe d (by omega)).1 h'; omega)
            exact bool01 hL (by omega) (by simp [boolCols]) (fun h' => by
              have := ((rowFacts hL (by omega)).2.2.2.2.1 h').2.1; rw [hfe] at this; exact fp_zero_ne_one this)
          have := (inNode hL (r := s + fl[i].1 + d) (by omega) (hF.act d (by omega)) hnl).2.2.2 hplen (by simp [nodeConst])
          rw [show s + fl[i].1 + (d + 1) = s + fl[i].1 + d + 1 by omega, this, ih (by omega)]
      have := key (fl[i].2 - 1) (by have := hF.pos; omega)
      rwa [show s + fl[i].1 + (fl[i].2 - 1) = s + fl[i].1 + fl[i].2 - 1 by have := hF.pos; omega] at this
    rw [hcst] at e
    have : ((fl[i].2 - 1 : Nat) : Fp) + 2 = Fp.ofNat (fl[i].2 + 1) := by
      rw [natCast_eq, show (2 : Fp) = Fp.ofNat 2 from rfl, ofNat_add']; congr 1; have := hF.pos; omega
    rw [← e, this, Fp.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact conv 3 (by unfold P; omega) (FL.2.2.2.2.1 h)
  · exact conv 31 (by unfold P; omega) (FL.2.2.2.2.2.1 h)
  · exact conv 1 (by unfold P; omega) (FL.2.2.2.2.2.2.1 h)
  · exact conv 31 (by unfold P; omega) (FL.2.2.2.2.2.2.2.1 h)
  · exact conv 7 (by unfold P; omega) (FL.2.2.2.2.2.2.2.2 h)

/-- A MEM field is the last field. -/
theorem memLast {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length)
    (hm : tr.cell T_NODE (s + fl[i].1) sMEM = 1) : i + 1 = fl.length := by
  rcases Nat.lt_or_ge (i + 1) fl.length with h | h
  · exfalso
    obtain ⟨he, hst, -⟩ := fieldEndRow hL hC hi
    have hr := fieldRow hL hC hi
    have hF := (hC.fields.field _ (List.getElem_mem hi)).1
    have hnl := (rowFacts hL (r := s + fl[i].1 + fl[i].2 - 1) (by have := hF.pos; omega)).2.2.2.2.2
      (by rw [hst sMEM (by simp [states]), hm]) he
    -- a node end inside the segment, before its last row
    have hnext := hC.fields.next h
    have hF1 := hC.fields.field _ (List.getElem_mem h)
    have p0 := hF.pos; have p1 := hF1.1.pos; have p2 := hF1.2
    have := hC.seg.2.2.2.2.2 (s + fl[i].1 + fl[i].2 - 1) (by omega) (by omega)
    simp only [one, decide_eq_false_iff_not] at this; exact this hnl
  · omega

end ZkFormal.NearV3.NodeProof3
