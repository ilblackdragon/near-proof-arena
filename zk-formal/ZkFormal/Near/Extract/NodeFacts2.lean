import ZkFormal.Near.Extract.NodeFacts

/-!
# ZkFormal.Near.Extract.NodeFacts2 — field, byte and window facts of `node`
-/

namespace ZkFormal.Near.NodeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}

theorem mem_fields {e : Expr} (h : e ∈ cFields) : e ∈ Node.constraints := mem_of (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem mem_bytes {e : Expr} (h : e ∈ cBytes) : e ∈ Node.constraints := mem_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem mem_windows {e : Expr} (h : e ∈ cWindows) : e ∈ Node.constraints :=
  mem_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem mem_links {e : Expr} (h : e ∈ cLinks) : e ∈ Node.constraints :=
  mem_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

variable (hL : TableLocal Node.table tr T_NODE pub)
include hL

/-- Inside a field: same state, `idx + 1`, not a field start. -/
theorem inField {r : Nat} (hr : r + 1 < tr.height T_NODE) (ha : tr.cell T_NODE r act = 1)
    (he : tr.cell T_NODE r fe = 0) :
    (∀ x ∈ states, tr.cell T_NODE (r + 1) x = tr.cell T_NODE r x) ∧
    tr.cell T_NODE (r + 1) idx = tr.cell T_NODE r idx + 1 ∧ tr.cell T_NODE (r + 1) fs = 0 := by
  have hr' : r < tr.height T_NODE := by omega
  have h1 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c fe))) (sub (n idx) (.add (c idx) (k 1))))
    (mem_fields (by simp [cFields]))
  have h2 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c fe))) (n fs)) (mem_fields (by simp [cFields]))
  simp only [eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2
  rw [ha, he] at h1 h2
  refine ⟨fun x hx => ?_, by grind, by grind⟩
  have h3 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c fe))) (sub (n x) (c x)))
    (mem_fields (by unfold cFields; simp only [List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨x, hx, rfl⟩)))
  simp only [eval_mul, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h3
  rw [ha, he] at h3; grind

/-- After a field end (not a node end): new field starts. -/
theorem afterField {r : Nat} (hr : r + 1 < tr.height T_NODE) (he : tr.cell T_NODE r fe = 1)
    (hl : tr.cell T_NODE r nl = 0) :
    tr.cell T_NODE (r + 1) idx = 0 ∧ tr.cell T_NODE (r + 1) fs = 1 := by
  have hr' : r < tr.height T_NODE := by omega
  have h1 := con hL hr' (e := mul3 (c fe) (Dsl.not (c nl)) (n idx)) (mem_fields (by simp [cFields]))
  have h2 := con hL hr' (e := mul3 (c fe) (Dsl.not (c nl)) (Dsl.not (n fs))) (mem_fields (by simp [cFields]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1 h2
  rw [he, hl] at h1 h2
  exact ⟨by grind, by grind⟩

/-- Field lengths: at a field end, `idx` is the field's last index. -/
theorem fieldLen {r : Nat} (hr : r < tr.height T_NODE) (he : tr.cell T_NODE r fe = 1) :
    (tr.cell T_NODE r sTAG = 1 → tr.cell T_NODE r idx = 0) ∧
    (tr.cell T_NODE r sHPL = 1 → tr.cell T_NODE r idx = 3) ∧
    (tr.cell T_NODE r sHPF = 1 → tr.cell T_NODE r idx = 0) ∧
    (tr.cell T_NODE r sKEY = 1 → tr.cell T_NODE r idx + 2 = tr.cell T_NODE r hplen) ∧
    (tr.cell T_NODE r sVLEN = 1 → tr.cell T_NODE r idx = 3) ∧
    (tr.cell T_NODE r sVH = 1 → tr.cell T_NODE r idx = 31) ∧
    (tr.cell T_NODE r sBM = 1 → tr.cell T_NODE r idx = 1) ∧
    (tr.cell T_NODE r sCH = 1 → tr.cell T_NODE r idx = 31) ∧
    (tr.cell T_NODE r sMEM = 1 → tr.cell T_NODE r idx = 7) := by
  have h1 := con hL hr (e := mul3 (c fe) (c sTAG) (c idx)) (mem_fields (by simp [cFields]))
  have h2 := con hL hr (e := mul3 (c fe) (c sHPL) (sub (c idx) (k 3))) (mem_fields (by simp [cFields]))
  have h3 := con hL hr (e := mul3 (c fe) (c sHPF) (c idx)) (mem_fields (by simp [cFields]))
  have h4 := con hL hr (e := mul3 (c fe) (c sKEY) (sub (.add (c idx) (k 2)) (c hplen))) (mem_fields (by simp [cFields]))
  have h5 := con hL hr (e := mul3 (c fe) (c sVLEN) (sub (c idx) (k 3))) (mem_fields (by simp [cFields]))
  have h6 := con hL hr (e := mul3 (c fe) (c sVH) (sub (c idx) (k 31))) (mem_fields (by simp [cFields]))
  have h7 := con hL hr (e := mul3 (c fe) (c sBM) (sub (c idx) (k 1))) (mem_fields (by simp [cFields]))
  have h8 := con hL hr (e := mul3 (c fe) (c sCH) (sub (c idx) (k 31))) (mem_fields (by simp [cFields]))
  have h9 := con hL hr (e := mul3 (c fe) (c sMEM) (sub (c idx) (k 7))) (mem_fields (by simp [cFields]))
  simp only [eval_mul3, eval_c, eval_sub, eval_add, eval_k] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [he] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · rw [h] at h1; grind
  · rw [h] at h2; grind
  · rw [h] at h3; grind
  · rw [h] at h4; grind
  · rw [h] at h5; grind
  · rw [h] at h6; grind
  · rw [h] at h7; grind
  · rw [h] at h8; grind
  · rw [h] at h9; grind

/-- Field successions (at a field end that is not the node end, next row's state). -/
theorem succ {r : Nat} (hr : r + 1 < tr.height T_NODE) (he : tr.cell T_NODE r fe = 1) :
    let N := fun x => tr.cell T_NODE (r + 1) x
    let K := fun x => tr.cell T_NODE r x
    (K sTAG = 1 → N sHPL = K tl + K te ∧ N sBM = K tb1 ∧ N sVLEN = K tb2) ∧
    (K sHPL = 1 → N sHPF = 1) ∧
    (K sHPF = 1 → N sKEY = 1 - K nokey ∧ N sVLEN = K nokey * K tl ∧ N sCH = K nokey * K te) ∧
    (K sKEY = 1 → N sVLEN = K tl ∧ N sCH = K te) ∧
    (K sVLEN = 1 → N sVH = 1) ∧
    (K sVH = 1 → N sMEM = K tl ∧ N sBM = K tb2) ∧
    (K sBM = 1 → N sMEM = K nochild ∧ N sCH = 1 - K nochild) ∧
    (K sCH = 1 → N sCH + N sMEM = 1 ∧ N sMEM = K lastw) := by
  intro N K
  have hr' : r < tr.height T_NODE := by omega
  have c1 := con hL hr' (e := mul3 (c fe) (c sTAG) (sub (.add (c tl) (c te)) (n sHPL))) (mem_fields (by simp [cFields]))
  have c2 := con hL hr' (e := mul3 (c fe) (c sTAG) (sub (c tb1) (n sBM))) (mem_fields (by simp [cFields]))
  have c3 := con hL hr' (e := mul3 (c fe) (c sTAG) (sub (c tb2) (n sVLEN))) (mem_fields (by simp [cFields]))
  have c4 := con hL hr' (e := mul3 (c fe) (c sHPL) (Dsl.not (n sHPF))) (mem_fields (by simp [cFields]))
  have c5 := con hL hr' (e := mul3 (c fe) (c sHPF) (sub (Dsl.not (c nokey)) (n sKEY))) (mem_fields (by simp [cFields]))
  have c6 := con hL hr' (e := mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c tl)) (n sVLEN)))
    (mem_fields (by simp [cFields]))
  have c7 := con hL hr' (e := mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c te)) (n sCH))) (mem_fields (by simp [cFields]))
  have c8 := con hL hr' (e := mul3 (c fe) (c sKEY) (sub (c tl) (n sVLEN))) (mem_fields (by simp [cFields]))
  have c9 := con hL hr' (e := mul3 (c fe) (c sKEY) (sub (c te) (n sCH))) (mem_fields (by simp [cFields]))
  have c10 := con hL hr' (e := mul3 (c fe) (c sVLEN) (Dsl.not (n sVH))) (mem_fields (by simp [cFields]))
  have c11 := con hL hr' (e := mul3 (c fe) (c sVH) (sub (c tl) (n sMEM))) (mem_fields (by simp [cFields]))
  have c12 := con hL hr' (e := mul3 (c fe) (c sVH) (sub (c tb2) (n sBM))) (mem_fields (by simp [cFields]))
  have c13 := con hL hr' (e := mul3 (c fe) (c sBM) (sub (c nochild) (n sMEM))) (mem_fields (by simp [cFields]))
  have c14 := con hL hr' (e := mul3 (c fe) (c sBM) (sub (Dsl.not (c nochild)) (n sCH))) (mem_fields (by simp [cFields]))
  have c15 := con hL hr' (e := mul3 (c fe) (c sCH) (sub (k 1) (.add (n sCH) (n sMEM)))) (mem_fields (by simp [cFields]))
  have c16 := con hL hr' (e := mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM))) (mem_fields (by simp [cFields]))
  simp only [eval_mul3, eval_mul, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, nxt hr]
    at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
  rw [he] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
  simp only [N, K]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at c1 c2 c3; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at c4; grind
  · rw [h] at c5 c6 c7; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at c8 c9; exact ⟨by grind, by grind⟩
  · rw [h] at c10; grind
  · rw [h] at c11 c12; exact ⟨by grind, by grind⟩
  · rw [h] at c13 c14; exact ⟨by grind, by grind⟩
  · rw [h] at c15 c16; exact ⟨by grind, by grind⟩

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL

theorem flags {r : Nat} (hr : r < tr.height T_NODE) :
    (tr.cell T_NODE r nokey = 1 → tr.cell T_NODE r hplen = 1) ∧
    tr.cell T_NODE r nochild * popE.eval tr T_NODE r pub = 0 ∧
    tr.cell T_NODE r tv * (tr.cell T_NODE r tb1 + tr.cell T_NODE r te) = 0 ∧
    ∀ i, i < 16 → (tr.cell T_NODE r tl + tr.cell T_NODE r te) * tr.cell T_NODE r (bm i) = 0 := by
  have c1 := con hL hr (e := .mul (c nokey) (sub (c hplen) (k 1))) (mem_fields (by simp [cFields]))
  have c2 := con hL hr (e := .mul (c nochild) popE) (mem_fields (by simp [cFields]))
  have c3 := con hL hr (e := .mul (c tv) (.add (c tb1) (c te))) (mem_fields (by simp [cFields]))
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k] at c1 c2 c3
  refine ⟨fun h => by rw [h] at c1; grind, c2, c3, fun i hi => ?_⟩
  have c4 := con hL hr (e := .mul (.add (c tl) (c te)) (c (bm i)))
    (mem_fields (by unfold cFields; simp only [List.mem_append, List.mem_map, List.mem_range]
                    exact Or.inr ⟨i, hi, rfl⟩))
  simpa using c4

/-- Bytes of the non-window fields. -/
theorem bytes {r : Nat} (hr : r < tr.height T_NODE) :
    (tr.cell T_NODE r sTAG = 1 → tr.cell T_NODE r b = tagE.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r sHPL = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r b = tr.cell T_NODE r hplen) ∧
    (tr.cell T_NODE r sHPL = 1 → tr.cell T_NODE r fs = 0 → tr.cell T_NODE r b = 0) ∧
    (tr.cell T_NODE r sHPF + tr.cell T_NODE r sKEY = 1 →
      tr.cell T_NODE r b = 16 * hiE.eval tr T_NODE r pub + loE.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r sHPF = 1 → hiE.eval tr T_NODE r pub = 2 * tr.cell T_NODE r tl + tr.cell T_NODE r odd ∧
      (tr.cell T_NODE r odd = 0 → loE.eval tr T_NODE r pub = 0)) ∧
    (tr.cell T_NODE r tv = 1 → tr.cell T_NODE r sVLEN = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r b = 72) ∧
    (tr.cell T_NODE r tv = 1 → tr.cell T_NODE r sVLEN = 1 → tr.cell T_NODE r fs = 0 → tr.cell T_NODE r b = 0) ∧
    (tr.cell T_NODE r sBM = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r b = bmLo.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r sBM = 1 → tr.cell T_NODE r fs = 0 → tr.cell T_NODE r b = bmHi.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r act - winE.eval tr T_NODE r pub = 1 → tr.cell T_NODE r pb = tr.cell T_NODE r b) := by
  have c1 := con hL hr (e := .mul (c sTAG) (sub (c b) tagE)) (mem_bytes (by simp [cBytes]))
  have c2 := con hL hr (e := mul3 (c sHPL) (c fs) (sub (c b) (c hplen))) (mem_bytes (by simp [cBytes]))
  have c3 := con hL hr (e := mul3 (c sHPL) (Dsl.not (c fs)) (c b)) (mem_bytes (by simp [cBytes]))
  have c4 := con hL hr (e := .mul (.add (c sHPF) (c sKEY)) (sub (c b) (.add (smul 16 hiE) loE)))
    (mem_bytes (by simp [cBytes]))
  have c5 := con hL hr (e := .mul (c sHPF) (sub hiE (.add (smul 2 (c tl)) (c odd)))) (mem_bytes (by simp [cBytes]))
  have c6 := con hL hr (e := mul3 (c sHPF) (Dsl.not (c odd)) loE) (mem_bytes (by simp [cBytes]))
  have c7 := con hL hr (e := .mul (mul3 (c tv) (c sVLEN) (c fs)) (sub (c b) (k 72))) (mem_bytes (by simp [cBytes]))
  have c8 := con hL hr (e := .mul (mul3 (c tv) (c sVLEN) (Dsl.not (c fs))) (c b)) (mem_bytes (by simp [cBytes]))
  have c9 := con hL hr (e := mul3 (c sBM) (c fs) (sub (c b) bmLo)) (mem_bytes (by simp [cBytes]))
  have c10 := con hL hr (e := mul3 (c sBM) (Dsl.not (c fs)) (sub (c b) bmHi)) (mem_bytes (by simp [cBytes]))
  have c11 := con hL hr (e := .mul (sub (c act) winE) (sub (c pb) (c b))) (mem_bytes (by simp [cBytes]))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_smul]
    at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  refine ⟨fun h => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_, fun h => ⟨?_, fun h' => ?_⟩, fun h h' h'' => ?_,
    fun h h' h'' => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [h] at c1; grind
  · rw [h, h'] at c2; grind
  · rw [h, h'] at c3; grind
  · rw [h] at c4; grind
  · rw [h] at c5; grind
  · rw [h, h'] at c6; grind
  · rw [h, h', h''] at c7; grind
  · rw [h, h', h''] at c8; grind
  · rw [h, h'] at c9; grind
  · rw [h, h'] at c10; grind
  · rw [h] at c11; grind

end ZkFormal.Near.NodeProof
