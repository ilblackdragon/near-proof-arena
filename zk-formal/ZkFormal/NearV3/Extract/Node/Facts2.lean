import ZkFormal.NearV3.Extract.Node.Facts

/-!
# ZkFormal.Near.Extract.NodeFacts2 — field, byte and window facts of `node`
-/

namespace ZkFormal.NearV3.NodeProof3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}

theorem mem_fields {e : Expr} (h : e ∈ cFields) : e ∈ NodeV3.constraints := mem_of (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem mem_bytes {e : Expr} (h : e ∈ cBytes) : e ∈ NodeV3.constraints := mem_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem mem_windows {e : Expr} (h : e ∈ cWindows) : e ∈ NodeV3.constraints :=
  mem_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem mem_links {e : Expr} (h : e ∈ cLinks) : e ∈ NodeV3.constraints :=
  mem_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

variable (hL : TableLocal NodeV3.table tr T_NODE pub)
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

/-- The `VLEN` accumulator. -/
theorem vlenStep {r : Nat} (hr : r + 1 < tr.height T_NODE) (hv : tr.cell T_NODE r sVLEN = 1) (he : tr.cell T_NODE r fe = 0) :
    tr.cell T_NODE (r + 1) vacc = tr.cell T_NODE r vacc + tr.cell T_NODE (r + 1) vsc * tr.cell T_NODE (r + 1) b ∧
    tr.cell T_NODE (r + 1) vsc = 256 * tr.cell T_NODE r vsc := by
  have c1 := con hL (by omega : r < _) (e := mul3 (c sVLEN) (Dsl.not (c fe))
    (sub (n vacc) (.add (c vacc) (.mul (n vsc) (n b))))) (mem_bytes (by simp [cBytes]))
  have c2 := con hL (by omega : r < _) (e := mul3 (c sVLEN) (Dsl.not (c fe)) (sub (n vsc) (smul 256 (c vsc))))
    (mem_bytes (by simp [cBytes]))
  simp only [eval_mul3, eval_mul, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_smul, nxt hr] at c1 c2
  rw [hv, he] at c1 c2; exact ⟨by grind, by grind⟩

/-- The `HPL` accumulator. -/
theorem hplStep {r : Nat} (hr : r + 1 < tr.height T_NODE) (hv : tr.cell T_NODE r sHPL = 1) (he : tr.cell T_NODE r fe = 0) :
    tr.cell T_NODE (r + 1) vacc = tr.cell T_NODE r vacc + tr.cell T_NODE (r + 1) vsc * tr.cell T_NODE (r + 1) b ∧
    tr.cell T_NODE (r + 1) vsc = 256 * tr.cell T_NODE r vsc := by
  have c1 := con hL (by omega : r < _) (e := mul3 (c sHPL) (Dsl.not (c fe))
    (sub (n vacc) (.add (c vacc) (.mul (n vsc) (n b))))) (mem_bytes (by simp [cBytes]))
  have c2 := con hL (by omega : r < _) (e := mul3 (c sHPL) (Dsl.not (c fe)) (sub (n vsc) (smul 256 (c vsc))))
    (mem_bytes (by simp [cBytes]))
  simp only [eval_mul3, eval_mul, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_smul, nxt hr] at c1 c2
  rw [hv, he] at c1 c2; exact ⟨by grind, by grind⟩

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

theorem flags {r : Nat} (hr : r < tr.height T_NODE) :
    (tr.cell T_NODE r nokey = 1 → tr.cell T_NODE r hplen = 1) ∧
    tr.cell T_NODE r nochild * popE.eval tr T_NODE r pub = 0 ∧
    tr.cell T_NODE r tv * (tr.cell T_NODE r tb1 + tr.cell T_NODE r te) = 0 ∧
    tr.cell T_NODE r tw * (1 - tr.cell T_NODE r tv) = 0 ∧
    tr.cell T_NODE r dup * (1 - tr.cell T_NODE r act) = 0 ∧ tr.cell T_NODE r hd * (1 - tr.cell T_NODE r act) = 0 ∧
    ∀ i, i < 16 → (tr.cell T_NODE r tl + tr.cell T_NODE r te) * tr.cell T_NODE r (bm i) = 0 := by
  have c1 := con hL hr (e := .mul (c nokey) (sub (c hplen) (k 1))) (mem_fields (by simp [cFields]))
  have c2 := con hL hr (e := .mul (c nochild) popE) (mem_fields (by simp [cFields]))
  have c3 := con hL hr (e := .mul (c tv) (.add (c tb1) (c te))) (mem_fields (by simp [cFields]))
  have c3a := con hL hr (e := .mul (c tw) (Dsl.not (c tv))) (mem_fields (by simp [cFields]))
  have c3b := con hL hr (e := .mul (c dup) (Dsl.not (c act))) (mem_fields (by simp [cFields]))
  have c3c := con hL hr (e := .mul (c hd) (Dsl.not (c act))) (mem_fields (by simp [cFields]))
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k, eval_not] at c1 c2 c3 c3a c3b c3c
  refine ⟨fun h => by rw [h] at c1; grind, c2, c3, c3a, c3b, c3c, fun i hi => ?_⟩
  have c4 := con hL hr (e := .mul (.add (c tl) (c te)) (c (bm i)))
    (mem_fields (by unfold cFields; simp only [List.mem_append, List.mem_map, List.mem_range]
                    exact Or.inr ⟨i, hi, rfl⟩))
  simpa using c4

/-- The HPL accumulator ends at the node's declared hex-prefix length. -/
theorem hplEnd {r : Nat} (hr : r < tr.height T_NODE)
    (hh : tr.cell T_NODE r sHPL = 1) (he : tr.cell T_NODE r fe = 1) :
    tr.cell T_NODE r vacc = tr.cell T_NODE r hplen := by
  have h := con hL hr (e := mul3 (c sHPL) (c fe) (sub (c vacc) (c hplen)))
    (mem_bytes (by simp [cBytes]))
  simp only [eval_mul3, eval_c, eval_sub, hh, he] at h
  grind

theorem hplTop {r : Nat} (hr : r < tr.height T_NODE)
    (hh : tr.cell T_NODE r sHPL = 1) (he : tr.cell T_NODE r fe = 1) :
    tr.cell T_NODE r b = 0 := by
  have h := con hL hr (e := mul3 (c sHPL) (c fe) (c b))
    (mem_bytes (by simp [cBytes]))
  simp only [eval_mul3, eval_c, hh, he] at h
  grind

/-- The HPL byte uses the existing Boolean nibble columns. -/
theorem hplNibble {r : Nat} (hr : r < tr.height T_NODE)
    (hh : tr.cell T_NODE r sHPL = 1) :
    tr.cell T_NODE r b = 16 * hiE.eval tr T_NODE r pub + loE.eval tr T_NODE r pub := by
  have h := con hL hr (e := .mul (c sHPL) (sub (c b) (.add (smul 16 hiE) loE)))
    (mem_bytes (by simp [cBytes]))
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_smul, hh] at h
  grind

/-- Bytes of the non-window fields. -/
theorem bytes {r : Nat} (hr : r < tr.height T_NODE) :
    (tr.cell T_NODE r sTAG = 1 → tr.cell T_NODE r b = tagE.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r sHPL = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r vacc = tr.cell T_NODE r b) ∧
    (tr.cell T_NODE r sHPL = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r vsc = 1) ∧
    (tr.cell T_NODE r sHPF + tr.cell T_NODE r sKEY = 1 →
      tr.cell T_NODE r b = 16 * hiE.eval tr T_NODE r pub + loE.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r sHPF = 1 → hiE.eval tr T_NODE r pub = 2 * tr.cell T_NODE r tl + tr.cell T_NODE r odd ∧
      (tr.cell T_NODE r odd = 0 → loE.eval tr T_NODE r pub = 0)) ∧
    (tr.cell T_NODE r sVLEN = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r vacc = tr.cell T_NODE r b ∧ tr.cell T_NODE r vsc = 1) ∧
    (tr.cell T_NODE r tv = 1 → tr.cell T_NODE r sVLEN = 1 → tr.cell T_NODE r fe = 1 →
      tr.cell T_NODE r vacc = tr.cell T_NODE r vlen ∧ tr.cell T_NODE r b = 0) ∧
    (tr.cell T_NODE r sBM = 1 → tr.cell T_NODE r fs = 1 → tr.cell T_NODE r b = bmLo.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r sBM = 1 → tr.cell T_NODE r fs = 0 → tr.cell T_NODE r b = bmHi.eval tr T_NODE r pub) ∧
    (tr.cell T_NODE r act - winE.eval tr T_NODE r pub = 1 → tr.cell T_NODE r pb = tr.cell T_NODE r b) := by
  have c1 := con hL hr (e := .mul (c sTAG) (sub (c b) tagE)) (mem_bytes (by simp [cBytes]))
  have c2 := con hL hr (e := mul3 (c sHPL) (c fs) (sub (c vacc) (c b))) (mem_bytes (by simp [cBytes]))
  have c3 := con hL hr (e := mul3 (c sHPL) (c fs) (sub (c vsc) (k 1))) (mem_bytes (by simp [cBytes]))
  have c4 := con hL hr (e := .mul (.add (c sHPF) (c sKEY)) (sub (c b) (.add (smul 16 hiE) loE)))
    (mem_bytes (by simp [cBytes]))
  have c5 := con hL hr (e := .mul (c sHPF) (sub hiE (.add (smul 2 (c tl)) (c odd)))) (mem_bytes (by simp [cBytes]))
  have c6 := con hL hr (e := mul3 (c sHPF) (Dsl.not (c odd)) loE) (mem_bytes (by simp [cBytes]))
  have c7 := con hL hr (e := mul3 (c sVLEN) (c fs) (sub (c vacc) (c b))) (mem_bytes (by simp [cBytes]))
  have c7' := con hL hr (e := mul3 (c sVLEN) (c fs) (sub (c vsc) (k 1))) (mem_bytes (by simp [cBytes]))
  have c8 := con hL hr (e := .mul (mul3 (c tv) (c sVLEN) (c fe)) (sub (c vacc) (c vlen))) (mem_bytes (by simp [cBytes]))
  have c8' := con hL hr (e := .mul (mul3 (c tv) (c sVLEN) (c fe)) (c b)) (mem_bytes (by simp [cBytes]))
  have c9 := con hL hr (e := mul3 (c sBM) (c fs) (sub (c b) bmLo)) (mem_bytes (by simp [cBytes]))
  have c10 := con hL hr (e := mul3 (c sBM) (Dsl.not (c fs)) (sub (c b) bmHi)) (mem_bytes (by simp [cBytes]))
  have c11 := con hL hr (e := .mul (sub (c act) winE) (sub (c pb) (c b))) (mem_bytes (by simp [cBytes]))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_smul]
    at c1 c2 c3 c4 c5 c6 c7 c7' c8 c8' c9 c10 c11
  refine ⟨fun h => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_, fun h => ⟨?_, fun h' => ?_⟩, fun h h' => ?_,
    fun h h' h'' => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [h] at c1; grind
  · rw [h, h'] at c2; grind
  · rw [h, h'] at c3; grind
  · rw [h] at c4; grind
  · rw [h] at c5; grind
  · rw [h, h'] at c6; grind
  · rw [h, h'] at c7 c7'; exact ⟨by grind, by grind⟩
  · rw [h, h', h''] at c8 c8'; exact ⟨by grind, by grind⟩
  · rw [h, h'] at c9; grind
  · rw [h, h'] at c10; grind
  · rw [h] at c11; grind

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

theorem winRead {r : Nat} (hr : r < tr.height T_NODE) (hw : tr.cell T_NODE r sVH + tr.cell T_NODE r sCH = 1) :
    tr.cell T_NODE r b = tr.cell T_NODE r (reg 0) ∧ tr.cell T_NODE r pb = tr.cell T_NODE r (preg 0) := by
  have c1 := con hL hr (e := .mul winE (sub (c b) (c (reg 0)))) (mem_windows (by simp [cWindows]))
  have c2 := con hL hr (e := .mul winE (sub (c pb) (c (preg 0)))) (mem_windows (by simp [cWindows]))
  simp only [winE, eval_mul, eval_c, eval_sub, eval_add] at c1 c2
  rw [hw] at c1 c2; exact ⟨by grind, by grind⟩

theorem winShift {r : Nat} (hr : r + 1 < tr.height T_NODE)
    (hw : tr.cell T_NODE r sVH + tr.cell T_NODE r sCH = 1) (he : tr.cell T_NODE r fe = 0) (i : Nat) (hi : i < 31) :
    tr.cell T_NODE (r + 1) (reg i) = tr.cell T_NODE r (reg (i + 1)) ∧
    tr.cell T_NODE (r + 1) (preg i) = tr.cell T_NODE r (preg (i + 1)) := by
  have hr' : r < tr.height T_NODE := by omega
  have mem : ∀ e ∈ [mul3 winE (Dsl.not (c fe)) (sub (n (reg i)) (c (reg (i + 1)))),
      mul3 winE (Dsl.not (c fe)) (sub (n (preg i)) (c (preg (i + 1))))], e ∈ NodeV3.constraints := by
    intro e he'
    apply mem_windows
    unfold cWindows; simp only [List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, he'⟩)))
  have c1 := con hL hr' (mem (mul3 winE (Dsl.not (c fe)) (sub (n (reg i)) (c (reg (i + 1))))) (by simp))
  have c2 := con hL hr' (mem (mul3 winE (Dsl.not (c fe)) (sub (n (preg i)) (c (preg (i + 1))))) (by simp))
  simp only [winE, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, nxt hr] at c1 c2
  rw [hw, he] at c1 c2; exact ⟨by grind, by grind⟩

theorem winLoad {r : Nat} (hr : r < tr.height T_NODE) (hf : tr.cell T_NODE r fs = 1) (i : Nat) (hi : i < 32) :
    (tr.cell T_NODE r sCH = 1 → tr.cell T_NODE r rv = 0 → tr.cell T_NODE r (preg i) = tr.cell T_NODE r (reg i)) ∧
    (tr.cell T_NODE r sVH = 1 → tr.cell T_NODE r tw = 0 → tr.cell T_NODE r (preg i) = tr.cell T_NODE r (reg i)) := by
  have mem : ∀ e ∈ [.mul (mul3 (c fs) (c sCH) (Dsl.not (c rv))) (sub (c (preg i)) (c (reg i))),
      .mul (mul3 (c fs) (c sVH) (Dsl.not (c tw))) (sub (c (preg i)) (c (reg i)))], e ∈ NodeV3.constraints := by
    intro e he'
    apply mem_windows
    unfold cWindows; simp only [List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨i, hi, he'⟩))
  have c1 := con hL hr (mem (.mul (mul3 (c fs) (c sCH) (Dsl.not (c rv))) (sub (c (preg i)) (c (reg i)))) (by simp))
  have c2 := con hL hr (mem (.mul (mul3 (c fs) (c sVH) (Dsl.not (c tw))) (sub (c (preg i)) (c (reg i)))) (by simp))
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_sub] at c1 c2
  rw [hf] at c1 c2
  exact ⟨fun h h' => by rw [h, h'] at c1; grind, fun h h' => by rw [h, h'] at c2; grind⟩

theorem winConst {r : Nat} (hr : r + 1 < tr.height T_NODE) (hc : tr.cell T_NODE r sCH = 1)
    (he : tr.cell T_NODE r fe = 0) : ∀ x ∈ windowConst, tr.cell T_NODE (r + 1) x = tr.cell T_NODE r x := by
  intro x hx
  have c := con hL (by omega : r < _) (e := mul3 (c sCH) (Dsl.not (c fe)) (sub (n x) (c x)))
    (mem_windows (by unfold cWindows; simp only [List.mem_append, List.mem_map]
                     exact Or.inl (Or.inr ⟨x, hx, rfl⟩)))
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, nxt hr] at c
  rw [hc, he] at c; grind

theorem winMisc {r : Nat} (hr : r < tr.height T_NODE) :
    tr.cell T_NODE r rv * (1 - tr.cell T_NODE r sCH) = 0 ∧
    tr.cell T_NODE r gD = tr.cell T_NODE r gP + tr.cell T_NODE r fs * tr.cell T_NODE r sVH * tr.cell T_NODE r tv ∧
    (tr.cell T_NODE r gP = 1 → tr.cell T_NODE r dI = (K_NPRE : Fp) + (16 : Nat) * tr.cell T_NODE r cid ∧
      tr.cell T_NODE r dL = tr.cell T_NODE r clen) ∧
    (tr.cell T_NODE r gD - tr.cell T_NODE r gP = 1 →
      tr.cell T_NODE r dI = (K_VPRE : Fp) + (16 : Nat) * tr.cell T_NODE r vid ∧ tr.cell T_NODE r dL = tr.cell T_NODE r vlen) := by
  have c1 := con hL hr (e := .mul (c rv) (Dsl.not (c sCH))) (mem_windows (by simp [cWindows]))
  have c2 := con hL hr (e := sub (c gD) (.add (c gP) (.mul vhStart (c tv)))) (mem_windows (by simp [cWindows]))
  have c3 := con hL hr (e := .mul (c gP) (sub (c dI) (mid K_NPRE (c cid)))) (mem_windows (by simp [cWindows]))
  have c4 := con hL hr (e := .mul (c gP) (sub (c dL) (c clen))) (mem_windows (by simp [cWindows]))
  have c5 := con hL hr (e := .mul valStart (sub (c dI) (mid K_VPRE (c vid)))) (mem_windows (by simp [cWindows]))
  have c6 := con hL hr (e := .mul valStart (sub (c dL) (c vlen))) (mem_windows (by simp [cWindows]))
  simp only [vhStart, valStart, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_mid] at c1 c2 c3 c4 c5 c6
  refine ⟨c1, by grind, fun h => ?_, fun h => ?_⟩
  · rw [h] at c3 c4; exact ⟨by grind, by grind⟩
  · rw [h] at c5 c6; exact ⟨by grind, by grind⟩

theorem winIndex {r : Nat} (hr : r + 1 < tr.height T_NODE) (he : tr.cell T_NODE r fe = 1) :
    (tr.cell T_NODE r sCH = 0 → tr.cell T_NODE (r + 1) sCH = 1 → tr.cell T_NODE (r + 1) w = 0) ∧
    (tr.cell T_NODE r sCH = 1 → tr.cell T_NODE (r + 1) sCH = 1 → tr.cell T_NODE (r + 1) w = tr.cell T_NODE r w + 1) := by
  have hr' : r < tr.height T_NODE := by omega
  have c1 := con hL hr' (e := .mul (mul3 (c fe) (Dsl.not (c sCH)) (n sCH)) (n w)) (mem_windows (by simp [cWindows]))
  have c2 := con hL hr' (e := .mul (mul3 (c fe) (c sCH) (n sCH)) (sub (n w) (.add (c w) (k 1))))
    (mem_windows (by simp [cWindows]))
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, nxt hr] at c1 c2
  rw [he] at c1 c2
  exact ⟨fun h h' => by rw [h, h'] at c1; grind, fun h h' => by rw [h, h'] at c2; grind⟩

theorem winSlot {r : Nat} (hr : r < tr.height T_NODE) (hc : tr.cell T_NODE r sCH = 1) :
    (isBr.eval tr T_NODE r pub = 1 →
      (sum ((List.range 16).map fun i => c (jj i))).eval tr T_NODE r pub = 1 ∧
      (sum ((List.range 16).map fun i => Expr.mul (c (jj i)) (c (bm i)))).eval tr T_NODE r pub = 1 ∧
      belowE.eval tr T_NODE r pub = tr.cell T_NODE r w) ∧
    (tr.cell T_NODE r te = 1 → tr.cell T_NODE r w = 0) ∧
    (tr.cell T_NODE r lastw = 1 → tr.cell T_NODE r w + 1 = nWinE.eval tr T_NODE r pub) := by
  have c1 := con hL hr (e := mul3 isBr (c sCH) (sub (sum ((List.range 16).map fun i => c (jj i))) (k 1)))
    (mem_windows (by simp [cWindows]))
  have c2 := con hL hr (e := mul3 isBr (c sCH) (sub (sum ((List.range 16).map fun i => .mul (c (jj i)) (c (bm i)))) (k 1)))
    (mem_windows (by simp [cWindows]))
  have c3 := con hL hr (e := mul3 isBr (c sCH) (sub belowE (c w))) (mem_windows (by simp [cWindows]))
  have c4 := con hL hr (e := .mul (c te) (.mul (c sCH) (c w))) (mem_windows (by simp [cWindows]))
  have c5 := con hL hr (e := mul3 (c lastw) (c sCH) (sub (.add (c w) (k 1)) nWinE)) (mem_windows (by simp [cWindows]))
  simp only [eval_mul3, eval_mul, eval_c, eval_sub, eval_add, eval_k] at c1 c2 c3 c4 c5
  rw [hc] at c1 c2 c3 c4 c5
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at c1 c2 c3; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at c4; grind
  · rw [h] at c5; grind

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

theorem linkGates {r : Nat} (hr : r < tr.height T_NODE) :
    let K := fun x => tr.cell T_NODE r x
    K gP = K fs * K sCH * K rv ∧ K gV = K nf * K dup ∧ K gL = K tl * K sMEM * K fs ∧
    K gS = K sCH * K rv + K sVH * K tv ∧
    K gS * (K dE - (K sCH * ((K_NPRE : Fp) + (16 : Nat) * K cid) + K sVH * ((K_VPRE : Fp) + (16 : Nat) * K vid))) = 0 ∧
    K gDp = K gP + (K gD - K gP) * K tw ∧ K gBm = K fs * K sBM ∧
    K eext = K te * K nokey * (1 - K odd) ∧ K xdead = K te * (1 - K xrv) ∧ K xlast0 = K te * K nokey ∧
    K te * K sCH * (K xrv - K rv) = 0 ∧ K xrv * (1 - K te) = 0 ∧ K te * K sCH * (K xres - K cres) = 0 ∧
    K xrv * (K xtgt - K xres) = 0 ∧ K xrv * K xtgJ = 0 ∧ K xdead * (K xtgt - K nid) = 0 ∧
    K xdead * (K xtgJ - sE.eval tr T_NODE r pub) = 0 ∧
    (K act - K eext) * (K res - K nid) = 0 ∧ K eext * (1 - K xrv) * (K res - K nid) = 0 ∧
    K eext * K xrv * (K res - K xres) = 0 ∧
    K gA = K sKEY + (K sHPF * K odd + (K gP * (K tb1 + K tb2) + (K gD - K gP))) ∧
    K gB = K sKEY + K gL := by
  intro K
  have c1 := con hL hr (e := sub (c gP) (.mul chStart (c rv))) (mem_links (by simp [cLinks]))
  have c2 := con hL hr (e := sub (c gV) (.mul (c nf) (c dup))) (mem_links (by simp [cLinks]))
  have c2a := con hL hr (e := sub (c gL) (mul3 (c tl) (c sMEM) (c fs))) (mem_links (by simp [cLinks]))
  have c2b := con hL hr (e := sub (c gS) gDigs) (mem_links (by simp [cLinks]))
  have c2c := con hL hr (e := .mul (c gS) (sub (c dE) eidE)) (mem_links (by simp [cLinks]))
  have c2d := con hL hr (e := sub (c gDp) gDpost) (mem_links (by simp [cLinks]))
  have c2e := con hL hr (e := sub (c gBm) bmStart) (mem_links (by simp [cLinks]))
  have c3 := con hL hr (e := sub (c eext) (mul3 (c te) (c nokey) (Dsl.not (c odd)))) (mem_links (by simp [cLinks]))
  have c4 := con hL hr (e := sub (c xdead) (.mul (c te) (Dsl.not (c xrv)))) (mem_links (by simp [cLinks]))
  have c5 := con hL hr (e := sub (c xlast0) (.mul (c te) (c nokey))) (mem_links (by simp [cLinks]))
  have c6 := con hL hr (e := mul3 (c te) (c sCH) (sub (c xrv) (c rv))) (mem_links (by simp [cLinks]))
  have c7 := con hL hr (e := .mul (c xrv) (Dsl.not (c te))) (mem_links (by simp [cLinks]))
  have c8 := con hL hr (e := .mul (.mul (c te) (c sCH)) (sub (c xres) (c cres))) (mem_links (by simp [cLinks]))
  have x1 := con hL hr (e := .mul (c xrv) (sub (c xtgt) (c xres))) (mem_links (by simp [cLinks]))
  have x2 := con hL hr (e := .mul (c xrv) (c xtgJ)) (mem_links (by simp [cLinks]))
  have x3 := con hL hr (e := .mul (c xdead) (sub (c xtgt) (c nid))) (mem_links (by simp [cLinks]))
  have x4 := con hL hr (e := .mul (c xdead) (sub (c xtgJ) sE)) (mem_links (by simp [cLinks]))
  have c9 := con hL hr (e := .mul (sub (c act) (c eext)) (sub (c res) (c nid))) (mem_links (by simp [cLinks]))
  have c10 := con hL hr (e := mul3 (c eext) (Dsl.not (c xrv)) (sub (c res) (c nid))) (mem_links (by simp [cLinks]))
  have c11 := con hL hr (e := mul3 (c eext) (c xrv) (sub (c res) (c xres))) (mem_links (by simp [cLinks]))
  have c12 := con hL hr (e := sub (c gA) (.add (c sKEY) (.add (.mul (c sHPF) (c odd))
      (.add (.mul (c gP) isBr) valStart)))) (mem_links (by simp [cLinks]))
  have c13 := con hL hr (e := sub (c gB) (.add (c sKEY) (c gL))) (mem_links (by simp [cLinks]))
  simp only [chStart, isBr, valStart, gDigs, eidE, gDpost, bmStart, eval_mul, eval_mul3, eval_c, eval_not,
    eval_sub, eval_add, eval_neg, eval_mid]
    at c1 c2 c2a c2b c2c c2d c2e c3 c4 c5 c6 c7 c8 x1 x2 x3 x4 c9 c10 c11 c12 c13
  simp only [K]
  exact ⟨by grind, by grind, by grind, by grind, c2c, by grind, by grind, by grind, by grind, by grind,
    c6, c7, c8, x1, x2, x3, x4, c9, c10, c11, by grind, by grind⟩

/-- Edge A / B contents per row kind. -/
theorem edgeFacts {r : Nat} (hr : r < tr.height T_NODE) :
    let K := fun x => tr.cell T_NODE r x
    (K sKEY = 1 → K aI = kiE.eval tr T_NODE r pub ∧ K aS = hiE.eval tr T_NODE r pub ∧ K aN = K nid ∧
      K aJ = kiE.eval tr T_NODE r pub + 1 ∧ K aK = (EK_KEY : Nat) ∧
      K bI = kiE.eval tr T_NODE r pub + 1 ∧ K bS = loE.eval tr T_NODE r pub ∧ K bK = (EK_KEY : Nat) ∧
      (K fe * K te = 0 → K bN = K nid ∧ K bJ = kiE.eval tr T_NODE r pub + 2) ∧
      (K fe = 1 → K te = 1 → K bN = K xtgt ∧ K bJ = K xtgJ)) ∧
    (K gL = 1 → K bI = sE.eval tr T_NODE r pub ∧ K bS = (SYM_END : Nat) ∧ K bN = K nid ∧
      K bJ = sE.eval tr T_NODE r pub ∧ K bK = (EK_LEND : Nat)) ∧
    (K sHPF = 1 → K odd = 1 → K aI = 0 ∧ K aS = loE.eval tr T_NODE r pub ∧ K aK = (EK_KEY : Nat) ∧
      (K xlast0 = 0 → K aN = K nid ∧ K aJ = 1) ∧ (K xlast0 = 1 → K aN = K xtgt ∧ K aJ = K xtgJ)) ∧
    (K gP = 1 → K tb1 + K tb2 = 1 → K aI = 0 ∧ K aS = jIdxE.eval tr T_NODE r pub ∧ K aN = K cres ∧ K aJ = 0 ∧
      K aK = (EK_DOWN : Nat)) ∧
    (K gD - K gP = 1 → K aI = K tl * sE.eval tr T_NODE r pub ∧ K aS = (SYM_END : Nat) ∧ K aN = K vid ∧ K aJ = 0 ∧
      K aK = (EK_VAL : Nat)) := by
  intro K
  have k1 := con hL hr (e := .mul (c sKEY) (sub (c aI) kiE)) (mem_links (by simp [cLinks]))
  have k2 := con hL hr (e := .mul (c sKEY) (sub (c aS) hiE)) (mem_links (by simp [cLinks]))
  have k3 := con hL hr (e := .mul (c sKEY) (sub (c aN) (c nid))) (mem_links (by simp [cLinks]))
  have k4 := con hL hr (e := .mul (c sKEY) (sub (c aJ) (.add kiE (k 1)))) (mem_links (by simp [cLinks]))
  have k4a := con hL hr (e := .mul (c sKEY) (sub (c aK) (k EK_KEY))) (mem_links (by simp [cLinks]))
  have k4b := con hL hr (e := .mul (c sKEY) (sub (c bI) (.add kiE (k 1)))) (mem_links (by simp [cLinks]))
  have k4c := con hL hr (e := .mul (c sKEY) (sub (c bS) loE)) (mem_links (by simp [cLinks]))
  have k4d := con hL hr (e := .mul (c sKEY) (sub (c bK) (k EK_KEY))) (mem_links (by simp [cLinks]))
  have k5 := con hL hr (e := .mul (.mul (c sKEY) (Dsl.not (.mul (c fe) (c te)))) (sub (c bN) (c nid)))
    (mem_links (by simp [cLinks]))
  have k6 := con hL hr (e := .mul (.mul (c sKEY) (Dsl.not (.mul (c fe) (c te)))) (sub (c bJ) (.add kiE (k 2))))
    (mem_links (by simp [cLinks]))
  have k7 := con hL hr (e := mul3 (c sKEY) (c fe) (.mul (c te) (sub (c bN) (c xtgt)))) (mem_links (by simp [cLinks]))
  have k8 := con hL hr (e := mul3 (c sKEY) (c fe) (.mul (c te) (sub (c bJ) (c xtgJ)))) (mem_links (by simp [cLinks]))
  have l1 := con hL hr (e := .mul (c gL) (sub (c bI) sE)) (mem_links (by simp [cLinks]))
  have l2 := con hL hr (e := .mul (c gL) (sub (c bS) (k SYM_END))) (mem_links (by simp [cLinks]))
  have l3 := con hL hr (e := .mul (c gL) (sub (c bN) (c nid))) (mem_links (by simp [cLinks]))
  have l4 := con hL hr (e := .mul (c gL) (sub (c bJ) sE)) (mem_links (by simp [cLinks]))
  have l5 := con hL hr (e := .mul (c gL) (sub (c bK) (k EK_LEND))) (mem_links (by simp [cLinks]))
  have o1 := con hL hr (e := .mul (.mul (c sHPF) (c odd)) (c aI)) (mem_links (by simp [cLinks]))
  have o2 := con hL hr (e := .mul (.mul (c sHPF) (c odd)) (sub (c aS) loE)) (mem_links (by simp [cLinks]))
  have o2a := con hL hr (e := .mul (.mul (c sHPF) (c odd)) (sub (c aK) (k EK_KEY))) (mem_links (by simp [cLinks]))
  have o3 := con hL hr (e := .mul (mul3 (c sHPF) (c odd) (Dsl.not (c xlast0))) (sub (c aN) (c nid)))
    (mem_links (by simp [cLinks]))
  have o4 := con hL hr (e := .mul (mul3 (c sHPF) (c odd) (Dsl.not (c xlast0))) (sub (c aJ) (k 1)))
    (mem_links (by simp [cLinks]))
  have o5 := con hL hr (e := .mul (mul3 (c sHPF) (c odd) (c xlast0)) (sub (c aN) (c xtgt))) (mem_links (by simp [cLinks]))
  have o6 := con hL hr (e := .mul (mul3 (c sHPF) (c odd) (c xlast0)) (sub (c aJ) (c xtgJ))) (mem_links (by simp [cLinks]))
  have b1 := con hL hr (e := .mul (.mul (c gP) isBr) (c aI)) (mem_links (by simp [cLinks]))
  have b2 := con hL hr (e := .mul (.mul (c gP) isBr) (sub (c aS) jIdxE)) (mem_links (by simp [cLinks]))
  have b3 := con hL hr (e := .mul (.mul (c gP) isBr) (sub (c aN) (c cres))) (mem_links (by simp [cLinks]))
  have b4 := con hL hr (e := .mul (.mul (c gP) isBr) (c aJ)) (mem_links (by simp [cLinks]))
  have b5 := con hL hr (e := .mul (.mul (c gP) isBr) (sub (c aK) (k EK_DOWN))) (mem_links (by simp [cLinks]))
  have v1 := con hL hr (e := .mul valStart (sub (c aI) (.mul (c tl) sE))) (mem_links (by simp [cLinks]))
  have v2 := con hL hr (e := .mul valStart (sub (c aS) (k SYM_END))) (mem_links (by simp [cLinks]))
  have v3 := con hL hr (e := .mul valStart (sub (c aN) (c vid))) (mem_links (by simp [cLinks]))
  have v4 := con hL hr (e := .mul valStart (c aJ)) (mem_links (by simp [cLinks]))
  have v5 := con hL hr (e := .mul valStart (sub (c aK) (k EK_VAL))) (mem_links (by simp [cLinks]))
  simp only [isBr, valStart, eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k]
    at k1 k2 k3 k4 k4a k4b k4c k4d k5 k6 k7 k8 l1 l2 l3 l4 l5 o1 o2 o2a o3 o4 o5 o6 b1 b2 b3 b4 b5 v1 v2 v3 v4 v5
  simp only [K]
  refine ⟨fun h => ?_, fun h => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [h] at k1 k2 k3 k4 k4a k4b k4c k4d k5 k6 k7 k8
    refine ⟨by grind, by grind, by grind, by grind, by grind, by grind, by grind, by grind, fun h2 => ?_, fun h2 h3 => ?_⟩
    · rw [h2] at k5 k6; exact ⟨by grind, by grind⟩
    · rw [h2, h3] at k7 k8; exact ⟨by grind, by grind⟩
  · rw [h] at l1 l2 l3 l4 l5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h, h'] at o1 o2 o2a o3 o4 o5 o6
    refine ⟨by grind, by grind, by grind, fun h2 => ?_, fun h2 => ?_⟩
    · rw [h2] at o3 o4; exact ⟨by grind, by grind⟩
    · rw [h2] at o5 o6; exact ⟨by grind, by grind⟩
  · rw [h, h'] at b1 b2 b3 b4 b5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at v1 v2 v3 v4 v5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩

end ZkFormal.NearV3.NodeProof3
