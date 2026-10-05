import ZkFormal.Near.Extract.NodeShape

/-!
# ZkFormal.Near.Extract.NodeBytes — the byte rows of a node field by field
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

/-- Column `x` on rows `r … r+n−1`, as naturals. -/
def rowsB (tr : Trace Fp) (x r n : Nat) : List Nat := (List.range n).map fun d => cv tr T_NODE (r + d) x

/-- A 32-byte register window at row `r`. -/
def win (tr : Trace Fp) (col : Nat → Nat) (r : Nat) : List Nat := (List.range 32).map fun i => cv tr T_NODE r (col i)

theorem rowsB_add (tr : Trace Fp) (x r a b' : Nat) : rowsB tr x r (a + b') = rowsB tr x r a ++ rowsB tr x (r + a) b' := by
  unfold rowsB; rw [List.range_add, List.map_append, List.map_map]
  congr 1; apply List.map_congr_left; intro d _; simp [Nat.add_assoc]

theorem rowsB_one (tr : Trace Fp) (x r : Nat) : rowsB tr x r 1 = [cv tr T_NODE r x] := by simp [rowsB]

theorem rowsB_length (tr : Trace Fp) (x r n : Nat) : (rowsB tr x r n).length = n := by simp [rowsB]

theorem win_length (tr : Trace Fp) (col : Nat → Nat) (r : Nat) : (win tr col r).length = 32 := by simp [win]

theorem rowsB_congr {tr : Trace Fp} {x y r n : Nat} (h : ∀ d, d < n → tr.cell T_NODE (r + d) x = tr.cell T_NODE (r + d) y) :
    rowsB tr x r n = rowsB tr y r n := by
  unfold rowsB; apply List.map_congr_left; intro d hd; rw [List.mem_range] at hd; unfold cv; rw [h d hd]

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL

/-- A window field (`VH` or `CH`, 32 rows from `r0`) emits its registers. -/
theorem winField {r0 : Nat} (hF : Field tr r0 32) (hH : r0 + 32 ≤ tr.height T_NODE)
    (hw : tr.cell T_NODE r0 sVH + tr.cell T_NODE r0 sCH = 1) :
    rowsB tr b r0 32 = win tr reg r0 ∧ rowsB tr pb r0 32 = win tr preg r0 := by
  -- registers shift by one per row
  have hwd : ∀ d, d < 32 → tr.cell T_NODE (r0 + d) sVH + tr.cell T_NODE (r0 + d) sCH = 1 := by
    intro d hd; rw [hF.st d hd sVH (by simp [states]), hF.st d hd sCH (by simp [states]), hw]
  have sh : ∀ d, d < 32 → ∀ i, d + i < 32 →
      tr.cell T_NODE (r0 + d) (reg i) = tr.cell T_NODE r0 (reg (d + i)) ∧
      tr.cell T_NODE (r0 + d) (preg i) = tr.cell T_NODE r0 (preg (d + i)) := by
    intro d; induction d with
    | zero => intro _ i _; simp
    | succ d ih =>
      intro hd i hi
      have hfe : tr.cell T_NODE (r0 + d) fe = 0 :=
        bool01 hL (by omega) (by simp [boolCols]) (fun h' => by have := (hF.fe d (by omega)).1 h'; omega)
      have S := winShift hL (r := r0 + d) (by omega) (hwd d (by omega)) hfe i (by omega)
      have I := ih (by omega) (i + 1) (by omega)
      rw [show r0 + (d + 1) = r0 + d + 1 by omega, S.1, S.2, I.1, I.2,
        show d + (i + 1) = d + 1 + i by omega]
      exact ⟨rfl, rfl⟩
  constructor
  · unfold rowsB win; apply List.map_congr_left; intro d hd; rw [List.mem_range] at hd
    unfold cv; rw [(winRead hL (by omega) (hwd d hd)).1, (sh d hd 0 (by omega)).1, Nat.add_zero]
  · unfold rowsB win; apply List.map_congr_left; intro d hd; rw [List.mem_range] at hd
    unfold cv; rw [(winRead hL (by omega) (hwd d hd)).2, (sh d hd 0 (by omega)).2, Nat.add_zero]

/-- Outside windows the post byte is the pre byte. -/
theorem pbField {r0 L : Nat} (hF : Field tr r0 L) (hH : r0 + L ≤ tr.height T_NODE)
    (hw : tr.cell T_NODE r0 sVH = 0) (hc : tr.cell T_NODE r0 sCH = 0) :
    rowsB tr pb r0 L = rowsB tr b r0 L := by
  apply rowsB_congr; intro d hd
  apply (bytes hL (r := r0 + d) (by omega)).2.2.2.2.2.2.2.2.2
  simp only [winE, eval_add, eval_c]
  rw [hF.act d hd, hF.st d hd sVH (by simp [states]), hF.st d hd sCH (by simp [states]), hw, hc]; decide

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node NearSpec

/-! ## Hex-prefix encoding of a key given as (first nibble?, nibble pairs) -/

theorem packNibbles_pairs (pairs : List (Nat × Nat)) :
    packNibbles (pairs.flatMap fun p => [p.1, p.2]) = pairs.map fun p => UInt8.ofNat (p.1 * 16 + p.2) := by
  induction pairs with
  | nil => rfl
  | cons p rest ih => simp [packNibbles, ih]

theorem flatMap_pairs_length (pairs : List (Nat × Nat)) : (pairs.flatMap fun p => [p.1, p.2]).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p rest ih => simp [ih]; omega

theorem hpN_eq (o : Bool) (lo0 : Nat) (pairs : List (Nat × Nat)) (leaf : Bool) (h0 : lo0 < 16)
    (hp : ∀ p ∈ pairs, p.1 < 16 ∧ p.2 < 16) :
    hpN ((if o then [lo0] else []) ++ pairs.flatMap (fun p => [p.1, p.2])) leaf =
      ((if leaf then 32 else 0) + (if o then 16 + lo0 else 0)) :: pairs.map (fun p => p.1 * 16 + p.2) := by
  have hl := flatMap_pairs_length pairs
  have hm : ∀ l : List (Nat × Nat), (∀ p ∈ l, p.1 < 16 ∧ p.2 < 16) →
      (l.map fun p => UInt8.ofNat (p.1 * 16 + p.2)).map UInt8.toNat = l.map (fun p => p.1 * 16 + p.2) := by
    intro l hl'
    induction l with
    | nil => rfl
    | cons p rest ih =>
      have := hl' p (by simp)
      simp only [List.map_cons, UInt8.toNat_ofNat', List.cons.injEq]
      refine ⟨Nat.mod_eq_of_lt (by omega), ih (fun q hq => hl' q (by simp [hq]))⟩
  cases o with
  | true =>
    simp only [if_true, List.singleton_append]
    unfold hpN hexPrefix
    have : (lo0 :: pairs.flatMap fun p => [p.1, p.2]).length % 2 = 1 := by
      simp only [List.length_cons, hl]; omega
    simp only [this, packNibbles_pairs, List.map_cons, UInt8.toNat_ofNat', hm pairs hp]
    cases leaf <;> simp <;> omega
  | false =>
    simp only [Bool.false_eq_true, if_false, List.nil_append]
    have : (pairs.flatMap fun p => [p.1, p.2]).length % 2 = 0 := by rw [hl]; omega
    cases leaf <;>
    · unfold hpN hexPrefix
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [this]
      simp only [packNibbles_pairs, List.map_cons, UInt8.toNat_ofNat', hm pairs hp]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

/-- Nibbles of a key byte row. -/
def hiN (tr : Trace Fp) (r : Nat) : Nat := bitsVal (fun i => cv tr T_NODE r (hbit i)) 0 4
def loN (tr : Trace Fp) (r : Nat) : Nat := bitsVal (fun i => cv tr T_NODE r (lbit i)) 0 4

theorem hbit_bool {i : Nat} (hi : i < 4) : hbit i ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))))
theorem lbit_bool {i : Nat} (hi : i < 4) : lbit i ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))

theorem fp_cast_eq {a b : Nat} (ha : a < P) (hb : b < P) (h : (a : Fp) = (b : Fp)) : a = b := ofNat_inj ha hb h

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL

theorem nibs {r : Nat} (hr : r < tr.height T_NODE) :
    hiN tr r < 16 ∧ loN tr r < 16 ∧ hiE.eval tr T_NODE r pub = (hiN tr r : Fp) ∧
      loE.eval tr T_NODE r pub = (loN tr r : Fp) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bitsVal_lt _ 0 4 (fun b hb => cvb hL hr (hbit_bool (by omega)))
  · exact bitsVal_lt _ 0 4 (fun b hb => cvb hL hr (lbit_bool (by omega)))
  · exact eval_bits tr T_NODE r pub hbit 0 4 (fun b hb => isBool hL hr (hbit_bool (by omega)))
  · exact eval_bits tr T_NODE r pub lbit 0 4 (fun b hb => isBool hL hr (lbit_bool (by omega)))

theorem keyByte {r : Nat} (hr : r < tr.height T_NODE) (hk : tr.cell T_NODE r sHPF + tr.cell T_NODE r sKEY = 1) :
    cv tr T_NODE r b = hiN tr r * 16 + loN tr r := by
  obtain ⟨h1, h2, h3, h4⟩ := nibs hL hr
  have e := (bytes hL hr).2.2.2.1 hk
  rw [h3, h4, cell_eq_cast tr T_NODE r b] at e
  apply fp_cast_eq (cv_lt _ _ _ _) (by unfold P; omega)
  rw [e, natCast_add, natCast_mul, show ((16 : Nat) : Fp) = 16 from rfl]; grind

theorem hpfNibs {r : Nat} (hr : r < tr.height T_NODE) (hf : tr.cell T_NODE r sHPF = 1) :
    hiN tr r = 2 * cv tr T_NODE r tl + cv tr T_NODE r odd ∧ (cv tr T_NODE r odd = 0 → loN tr r = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := nibs hL hr
  obtain ⟨e1, e2⟩ := ((bytes hL hr).2.2.2.2.1 hf)
  have bt := cvb hL hr (x := tl) (by simp [boolCols])
  have bo := cvb hL hr (x := odd) (by simp [boolCols])
  refine ⟨?_, fun ho => ?_⟩
  · rw [h3, cell_eq_cast tr T_NODE r tl, cell_eq_cast tr T_NODE r odd] at e1
    apply fp_cast_eq (by unfold P; omega) (by unfold P; omega)
    rw [e1, natCast_add, natCast_mul]; rfl
  · have := e2 (of_cv_zero ho)
    rw [h4] at this
    exact fp_cast_eq (by unfold P; omega) (by unfold P; omega) (this.trans rfl)

/-- The tag byte. -/
theorem tagByte {r : Nat} (hr : r < tr.height T_NODE) (ht : tr.cell T_NODE r sTAG = 1) :
    cv tr T_NODE r b = cv tr T_NODE r tb1 + 2 * cv tr T_NODE r tb2 + 3 * cv tr T_NODE r te := by
  have e := (bytes hL hr).1 ht
  simp only [tagE, eval_add, eval_c, eval_smul] at e
  have b1 := cvb hL hr (x := tb1) (by simp [boolCols])
  have b2 := cvb hL hr (x := tb2) (by simp [boolCols])
  have b3 := cvb hL hr (x := te) (by simp [boolCols])
  rw [cell_eq_cast tr T_NODE r tb1, cell_eq_cast tr T_NODE r tb2, cell_eq_cast tr T_NODE r te,
    cell_eq_cast tr T_NODE r b] at e
  apply fp_cast_eq (cv_lt _ _ _ _) (by unfold P; omega)
  rw [e, natCast_add, natCast_add, natCast_mul, natCast_mul]; grind

/-- `HPL` field: `[hplen, 0, 0, 0]`. -/
theorem hplBytes {r0 : Nat} (hF : Field tr r0 4) (hH : r0 + 4 ≤ tr.height T_NODE)
    (hs : tr.cell T_NODE r0 sHPL = 1) : rowsB tr b r0 4 = u32r (cv tr T_NODE r0 hplen) := by
  have st := fun d (hd : d < 4) => hF.st d hd sHPL (by simp [states])
  have z : ∀ d, 0 < d → d < 4 → cv tr T_NODE (r0 + d) b = 0 := by
    intro d h0 hd
    have hfs : tr.cell T_NODE (r0 + d) fs = 0 :=
      bool01 hL (by omega) (by simp [boolCols]) (fun h => by have := (hF.fs d hd).1 h; omega)
    exact cv_zero ((bytes hL (by omega)).2.2.1 (by rw [st d hd, hs]) hfs)
  have f0 := (bytes hL (r := r0) (by omega)).2.1 hs ((hF.fs 0 (by omega)).2 rfl)
  simp only [rowsB, u32r, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero]
  rw [z 1 (by omega) (by omega), z 2 (by omega) (by omega), z 3 (by omega) (by omega)]
  unfold cv; rw [f0]

/-- Touched `VLEN` field: `[72, 0, 0, 0]`. -/
theorem vlenTouched {r0 : Nat} (hF : Field tr r0 4) (hH : r0 + 4 ≤ tr.height T_NODE)
    (hs : tr.cell T_NODE r0 sVLEN = 1) (htv : ∀ d, d < 4 → tr.cell T_NODE (r0 + d) tv = 1) :
    rowsB tr b r0 4 = u32r 72 := by
  have st := fun d (hd : d < 4) => hF.st d hd sVLEN (by simp [states])
  have z : ∀ d, 0 < d → d < 4 → cv tr T_NODE (r0 + d) b = 0 := by
    intro d h0 hd
    have hfs : tr.cell T_NODE (r0 + d) fs = 0 :=
      bool01 hL (by omega) (by simp [boolCols]) (fun h => by have := (hF.fs d hd).1 h; omega)
    exact cv_zero ((bytes hL (by omega)).2.2.2.2.2.2.1 (htv d hd) (by rw [st d hd, hs]) hfs)
  have f0 := (bytes hL (r := r0) (by omega)).2.2.2.2.2.1 (by simpa using htv 0 (by omega)) hs
    ((hF.fs 0 (by omega)).2 rfl)
  simp only [rowsB, u32r, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero]
  rw [z 1 (by omega) (by omega), z 2 (by omega) (by omega), z 3 (by omega) (by omega)]
  unfold cv; rw [f0]; rfl

/-- `KEY` field bytes. -/
theorem keyBytes {r0 L : Nat} (hF : Field tr r0 L) (hH : r0 + L ≤ tr.height T_NODE)
    (hs : tr.cell T_NODE r0 sKEY = 1) :
    rowsB tr b r0 L = (List.range' 0 L).map fun m => hiN tr (r0 + m) * 16 + loN tr (r0 + m) := by
  unfold rowsB; rw [List.range_eq_range']; apply List.map_congr_left; intro d hd
  rw [List.mem_range'] at hd
  apply keyByte hL (by omega)
  rw [hF.st d (by omega) sHPF (by simp [states]), hF.st d (by omega) sKEY (by simp [states]), hs]
  have := stOnly hL (r := r0) (by omega) (by simpa using hF.act 0 (by omega)) hs (by simp [states])
    (y := sHPF) (by simp [states]) (by decide)
  rw [this]; grind

end ZkFormal.Near.NodeProof
