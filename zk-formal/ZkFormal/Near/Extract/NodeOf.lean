import ZkFormal.Near.Extract.NodeBytes

/-!
# ZkFormal.Near.Extract.NodeOf — the view of one node segment, and its bytes
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

def keyPairs (tr : Trace Fp) (s : Nat) : List (Nat × Nat) :=
  (List.range' 0 (cv tr T_NODE s hplen - 1)).map fun m => (hiN tr (s + 6 + m), loN tr (s + 6 + m))

def keyNibs (tr : Trace Fp) (s : Nat) : List Nat :=
  (if cv tr T_NODE s odd = 1 then [loN tr (s + 5)] else []) ++ (keyPairs tr s).flatMap (fun p => [p.1, p.2])

def slotOf (tr : Trace Fp) (s rV rH : Nat) : NSlot :=
  if cv tr T_NODE s tv = 1 then .touched (win tr reg rH) (win tr preg rH) else .ref (rowsB tr b rV 4) (win tr reg rH)

def kidOf (tr : Trace Fp) (r : Nat) : NKid :=
  if cv tr T_NODE r rv = 1 then
    .node (cv tr T_NODE r cid) (cv tr T_NODE r clen) (cv tr T_NODE r cres) (win tr reg r) (win tr preg r)
  else .hash (win tr reg r)

def belowN (tr : Trace Fp) (s j : Nat) : Nat := ((List.range j).map fun i => cv tr T_NODE s (bm i)).sum

def kidsOf (tr : Trace Fp) (s o : Nat) : List NKid :=
  (List.range 16).map fun j => if cv tr T_NODE s (bm j) = 1 then kidOf tr (s + (o + 2 + 32 * belowN tr s j)) else .none

def brOff (tr : Trace Fp) (s : Nat) : Nat := if cv tr T_NODE s tb2 = 1 then 37 else 1

def nodeVOf (tr : Trace Fp) (s : Nat) : NodeV :=
  if cv tr T_NODE s tl = 1 then
    .leaf (keyNibs tr s) (slotOf tr s (s + (5 + cv tr T_NODE s hplen)) (s + (9 + cv tr T_NODE s hplen)))
      (rowsB tr b (s + (41 + cv tr T_NODE s hplen)) 8)
  else if cv tr T_NODE s te = 1 then
    .ext (keyNibs tr s) (kidOf tr (s + (5 + cv tr T_NODE s hplen))) (rowsB tr b (s + (37 + cv tr T_NODE s hplen)) 8)
  else
    .branch (if cv tr T_NODE s tb2 = 1 then some (slotOf tr s (s + 1) (s + 5)) else none) (kidsOf tr s (brOff tr s))
      (rowsB tr b (s + (brOff tr s + 2 + 32 * popN tr s)) 8)

theorem belowN_succ (tr : Trace Fp) (s j : Nat) : belowN tr s (j + 1) = belowN tr s j + cv tr T_NODE s (bm j) := by
  simp [belowN, List.range_succ]

theorem popN_eq (tr : Trace Fp) (s : Nat) : popN tr s = belowN tr s 16 := by unfold popN belowN; rfl

/-- Children in slot order are the windows in order. -/
theorem flatMap_bits {α : Type} (f : Nat → Nat) (F : Nat → List α) (n : Nat) (hf : ∀ j, j < n → f j ≤ 1) :
    (List.range n).flatMap (fun j => if f j = 1 then F (((List.range j).map f).sum) else []) =
      (List.range (((List.range n).map f).sum)).flatMap F := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih (fun j hj => hf j (by omega))]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := hf n (by omega)
    by_cases h : f n = 1
    · rw [if_pos h, h, List.range_succ, List.flatMap_append]; simp
    · rw [if_neg h, show f n = 0 by omega]; simp

theorem rowsB_blocks (tr : Trace Fp) (x r : Nat) (p : Nat) :
    rowsB tr x r (32 * p) = (List.range p).flatMap fun j => rowsB tr x (r + 32 * j) 32 := by
  induction p with
  | zero => simp [rowsB]
  | succ p ih =>
    rw [show 32 * (p + 1) = 32 * p + 32 by omega, rowsB_add, ih, List.range_succ, List.flatMap_append]; simp

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem fieldAt (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) :
    Field tr (s + o) L ∧ s + o + L ≤ tr.height T_NODE := by
  have h1 := hC.fields.field _ hm; have h2 := hC.bound
  exact ⟨h1.1, by have := h1.2; simp only at this; omega⟩

theorem pbOf (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (hx : tr.cell T_NODE (s + o) x = 1)
    (hxs : x ∈ states) (h1 : sVH ≠ x) (h2 : sCH ≠ x) : rowsB tr pb (s + o) L = rowsB tr b (s + o) L := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 hF.pos
  exact pbField hL hF hH (stOnly hL hr ha hx hxs (by simp [states]) h1) (stOnly hL hr ha hx hxs (by simp [states]) h2)

theorem cvConst (hC : NodeCtx tr s ℓ fl) {x d : Nat} (hx : x ∈ nodeConst) (hd : d < ℓ) :
    cv tr T_NODE (s + d) x = cv tr T_NODE s x := by unfold cv; rw [segConst hL hC hx hd]

/-- Hex-prefixed key bytes (`HPF` then `KEY*`), for a leaf or an extension. -/
theorem keySer (hC : NodeCtx tr s ℓ fl) (hlt : tr.cell T_NODE s tl + tr.cell T_NODE s te = 1)
    (hh1 : 1 ≤ cv tr T_NODE s hplen) (hℓ : 6 + cv tr T_NODE s hplen ≤ ℓ)
    (sF : tr.cell T_NODE (s + 5) sHPF = 1) (hm5 : (5, 1) ∈ fl)
    (sK : cv tr T_NODE s hplen ≠ 1 → tr.cell T_NODE (s + 6) sKEY = 1)
    (hm6 : cv tr T_NODE s hplen ≠ 1 → (6, cv tr T_NODE s hplen - 1) ∈ fl) :
    rowsB tr b (s + 5) 1 ++ rowsB tr b (s + 6) (cv tr T_NODE s hplen - 1) =
      hpN (keyNibs tr s) (cv tr T_NODE s tl = 1) ∧
    (hpN (keyNibs tr s) (cv tr T_NODE s tl = 1)).length = cv tr T_NODE s hplen := by
  obtain ⟨hF5, hH5⟩ := fieldAt hL hC hm5
  have hr5 : s + 5 < tr.height T_NODE := by omega
  have ha5 : tr.cell T_NODE (s + 5) act = 1 := by simpa using hF5.act 0 (by omega)
  have kb := keyByte hL hr5 (by
    rw [sF, stOnly hL hr5 ha5 sF (by simp [states]) (y := sKEY) (by simp [states]) (by decide)]; grind)
  obtain ⟨hpf1, hpf2⟩ := hpfNibs hL hr5 sF
  rw [cvConst hL hC (x := odd) (d := 5) (by simp [nodeConst]) (by omega)] at hpf1 hpf2
  rw [cvConst hL hC (x := tl) (d := 5) (by simp [nodeConst]) (by omega)] at hpf1
  obtain ⟨n1, n2, -, -⟩ := nibs hL hr5
  have hpairs : ∀ p ∈ keyPairs tr s, p.1 < 16 ∧ p.2 < 16 := by
    intro p hp; unfold keyPairs at hp; rw [List.mem_map] at hp
    obtain ⟨m, hm, rfl⟩ := hp; rw [List.mem_range'] at hm
    have := hC.bound
    obtain ⟨a1, a2, -, -⟩ := nibs hL (r := s + 6 + m) (by omega)
    exact ⟨a1, a2⟩
  have hkey : rowsB tr b (s + 6) (cv tr T_NODE s hplen - 1) = (keyPairs tr s).map fun p => p.1 * 16 + p.2 := by
    by_cases h1 : cv tr T_NODE s hplen = 1
    · simp [keyPairs, h1, rowsB]
    · obtain ⟨hF6, hH6⟩ := fieldAt hL hC (hm6 h1)
      rw [keyBytes hL hF6 hH6 (sK h1), keyPairs, List.map_map]; rfl
  have bt := cvb hL (r := s) (by have := hC.bound; omega) (x := tl) (by simp [boolCols])
  have bo := cvb hL (r := s) (by have := hC.bound; omega) (x := odd) (by simp [boolCols])
  have hlen : (keyPairs tr s).length = cv tr T_NODE s hplen - 1 := by simp [keyPairs]
  unfold keyNibs
  rw [rowsB_one, hkey]
  by_cases ho : cv tr T_NODE s odd = 1
  · rw [if_pos ho]
    have := hpN_eq true (loN tr (s + 5)) (keyPairs tr s) (decide (cv tr T_NODE s tl = 1)) n2 hpairs
    simp only [if_true] at this
    rw [this]
    refine ⟨?_, by simp [hlen]; omega⟩
    simp only [List.singleton_append, List.cons.injEq, and_true]
    rw [kb, hpf1, ho]
    by_cases ht : cv tr T_NODE s tl = 1 <;> simp [ht] <;> omega
  · rw [if_neg ho]
    have := hpN_eq false 0 (keyPairs tr s) (decide (cv tr T_NODE s tl = 1)) (by omega) hpairs
    simp only [Bool.false_eq_true, if_false, List.nil_append] at this ⊢
    rw [this]
    refine ⟨?_, by simp [hlen]; omega⟩
    simp only [List.singleton_append, List.cons.injEq, and_true]
    have ho0 : cv tr T_NODE s odd = 0 := by omega
    rw [kb, hpf1, hpf2 ho0, ho0]
    by_cases ht : cv tr T_NODE s tl = 1 <;> simp [ht] <;> omega

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- The value slot of a leaf or `b2` (VLEN at `rV`, VH at `rH`). -/
theorem slotSer (hC : NodeCtx tr s ℓ fl) {rV rH : Nat} (hV : (rV, 4) ∈ fl) (hVH : (rH, 32) ∈ fl)
    (sV : tr.cell T_NODE (s + rV) sVLEN = 1) (sH : tr.cell T_NODE (s + rH) sVH = 1) (hrH : rH = rV + 4) :
    rowsB tr b (s + rV) 4 ++ rowsB tr b (s + rH) 32 = (slotOf tr s (s + rV) (s + rH)).bytes false ∧
    rowsB tr pb (s + rV) 4 ++ rowsB tr pb (s + rH) 32 = (slotOf tr s (s + rV) (s + rH)).bytes true := by
  obtain ⟨hFV, hHV⟩ := fieldAt hL hC hV
  obtain ⟨hFH, hHH⟩ := fieldAt hL hC hVH
  have hrH : s + rH < tr.height T_NODE := by omega
  have haH : tr.cell T_NODE (s + rH) act = 1 := by simpa using hFH.act 0 (by omega)
  have W := winField hL hFH hHH (by
    rw [sH, stOnly hL hrH haH sH (by simp [states]) (y := sCH) (by simp [states]) (by decide)]; grind)
  have P := pbOf hL hC hV sV (by simp [states]) (by decide) (by decide)
  have hlℓ : s + rH < s + ℓ := by
    have := hC.fields.field _ hVH; simp only at this; have := this.1.pos; omega
  unfold slotOf
  rw [W.1, W.2, P]
  by_cases htv : cv tr T_NODE s tv = 1
  · rw [if_pos htv]
    have htv' : ∀ d, d < 4 → tr.cell T_NODE (s + rV + d) tv = 1 := by
      intro d hd
      rw [show s + rV + d = s + (rV + d) by omega, segConst hL hC (by simp [nodeConst]) (by omega)]
      exact of_cv_one htv
    rw [vlenTouched hL hFV hHV sV htv']
    exact ⟨rfl, rfl⟩
  · rw [if_neg htv]
    refine ⟨rfl, ?_⟩
    simp only [NSlot.bytes, List.append_cancel_left_eq]
    unfold win; apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    have hfs := (hFH.fs 0 (by omega)).2 rfl
    simp only [Nat.add_zero] at hfs
    have htv0 : tr.cell T_NODE (s + rH) tv = 0 := by
      rw [segConst hL hC (by simp [nodeConst]) (by omega)]
      exact bool01 hL (by have := hC.bound; omega) (by simp [boolCols]) (fun h => htv (cv_one h))
    unfold cv; rw [(winLoad hL hrH hfs i hi).2 sH htv0]

/-- Leaf serialization. -/
theorem leafSer (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) :
    rowsB tr b s ℓ = (nodeVOf tr s).ser false ∧ rowsB tr pb s ℓ = (nodeVOf tr s).ser true := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sV, sVH, -⟩ := leafFields hL hC ht
  have hcv : cv tr T_NODE s tl = 1 := cv_one ht
  have mem : ∀ p ∈ leafFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  have hr0 : s < tr.height T_NODE := (nodeStart hL hC).1
  have ha0 : tr.cell T_NODE s act = 1 := (nodeStart hL hC).2
  -- pieces
  have K := keySer hL hC (by rw [ht, typeZeros hL hC (x := tl) (y := te) (by simp) ht (by simp) (by decide)]; grind)
    hh1 (by omega) sF (mem _ (by simp [leafFL, keyFL]))
    (fun h => sK h) (fun h => mem _ (by simp [leafFL, keyFL, h]))
  rw [hcv] at K
  simp only [decide_true] at K
  have S := slotSer hL hC (rV := 5 + cv tr T_NODE s hplen) (rH := 9 + cv tr T_NODE s hplen)
    (mem _ (by simp [leafFL])) (mem _ (by simp [leafFL])) sV sVH (by omega)
  have T0 : rowsB tr b s 1 = [0] := by
    rw [rowsB_one, tagByte hL hr0 sT,
      cv_zero (typeZeros hL hC (x := tl) (y := tb1) (by simp) ht (by simp) (by decide)),
      cv_zero (typeZeros hL hC (x := tl) (y := tb2) (by simp) ht (by simp) (by decide)),
      cv_zero (typeZeros hL hC (x := tl) (y := te) (by simp) ht (by simp) (by decide))]
  obtain ⟨hF1, hH1⟩ := fieldAt hL hC (mem (1, 4) (by simp [leafFL, keyFL]))
  have T1 : rowsB tr b (s + 1) 4 = u32r (cv tr T_NODE s hplen) := by
    rw [hplBytes hL hF1 hH1 sH, cvConst hL hC (by simp [nodeConst]) (by omega)]
  have P0 := pbOf hL hC (o := 0) (L := 1) (mem _ (by simp [leafFL, keyFL])) (by simpa using sT) (by simp [states]) (by decide) (by decide)
  have P1 := pbOf hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) sH (by simp [states]) (by decide) (by decide)
  have P5 := pbOf hL hC (L := 1) (mem _ (by simp [leafFL, keyFL])) sF (by simp [states]) (by decide) (by decide)
  have P6 : rowsB tr pb (s + 6) (cv tr T_NODE s hplen - 1) = rowsB tr b (s + 6) (cv tr T_NODE s hplen - 1) := by
    by_cases h1 : cv tr T_NODE s hplen = 1
    · simp [rowsB, h1]
    · exact pbOf hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [leafFL, keyFL, h1])) (sK h1) (by simp [states]) (by decide) (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, sM⟩ := leafFields hL hC ht
  have P41 := pbOf hL hC (L := 8) (mem _ (by simp [leafFL])) sM (by simp [states]) (by decide) (by decide)
  simp only [Nat.add_zero] at P0
  -- split the rows
  have split : ∀ x, rowsB tr x s ℓ = rowsB tr x s 1 ++ (rowsB tr x (s + 1) 4 ++
      ((rowsB tr x (s + 5) 1 ++ rowsB tr x (s + 6) (cv tr T_NODE s hplen - 1)) ++
      ((rowsB tr x (s + (5 + cv tr T_NODE s hplen)) 4 ++ rowsB tr x (s + (9 + cv tr T_NODE s hplen)) 32) ++
      rowsB tr x (s + (41 + cv tr T_NODE s hplen)) 8))) := by
    intro x
    rw [hℓ, show 49 + cv tr T_NODE s hplen = 1 + (4 + ((1 + (cv tr T_NODE s hplen - 1)) + ((4 + 32) + 8))) by omega]
    simp only [rowsB_add, List.append_assoc]
    rw [show s + 5 + (1 + (cv tr T_NODE s hplen - 1)) = s + (5 + cv tr T_NODE s hplen) by omega]
    rw [show s + (5 + cv tr T_NODE s hplen) + 4 = s + (9 + cv tr T_NODE s hplen) by omega,
      show s + (5 + cv tr T_NODE s hplen) + (4 + 32) = s + (41 + cv tr T_NODE s hplen) by omega]
  unfold nodeVOf; rw [if_pos hcv]
  simp only [NodeV.ser]
  constructor
  · rw [split, T0, T1, K.1, S.1, K.2]; simp only [List.append_assoc]
  · rw [split, ← S.2, P0, P1, P5, P6, P41, T0, T1, K.1, K.2]; simp only [List.append_assoc]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- A child window field. -/
theorem kidSer {r0 : Nat} (hF : Field tr r0 32) (hH : r0 + 32 ≤ tr.height T_NODE)
    (hc : tr.cell T_NODE r0 sCH = 1) :
    rowsB tr b r0 32 = (kidOf tr r0).bytes false ∧ rowsB tr pb r0 32 = (kidOf tr r0).bytes true := by
  have hr : r0 < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE r0 act = 1 := by simpa using hF.act 0 (by omega)
  have W := winField hL hF hH (by
    rw [hc, stOnly hL hr ha hc (by simp [states]) (y := sVH) (by simp [states]) (by decide)]; grind)
  rw [W.1, W.2]
  unfold kidOf
  by_cases hrv : cv tr T_NODE r0 rv = 1
  · rw [if_pos hrv]; exact ⟨rfl, rfl⟩
  · rw [if_neg hrv]
    refine ⟨rfl, ?_⟩
    simp only [NKid.bytes]
    unfold win; apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    have hfs := (hF.fs 0 (by omega)).2 rfl
    simp only [Nat.add_zero] at hfs
    have hrv0 : tr.cell T_NODE r0 rv = 0 := bool01 hL hr (by simp [boolCols]) (fun h => hrv (cv_one h))
    unfold cv; rw [(winLoad hL hr hfs i hi).1 hc hrv0]

/-- Extension serialization. -/
theorem extSer (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) :
    rowsB tr b s ℓ = (nodeVOf tr s).ser false ∧ rowsB tr pb s ℓ = (nodeVOf tr s).ser true := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have htl : tr.cell T_NODE s tl = 0 := typeZeros hL hC (x := te) (y := tl) (by simp) ht (by simp) (by decide)
  have hcv : cv tr T_NODE s te = 1 := cv_one ht
  have hcl : cv tr T_NODE s tl ≠ 1 := by rw [cv_zero htl]; decide
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  have hr0 : s < tr.height T_NODE := (nodeStart hL hC).1
  have K := keySer hL hC (by rw [ht, htl]; grind)
    hh1 (by omega) sF (mem _ (by simp [extFL, keyFL]))
    (fun h => sK h) (fun h => mem _ (by simp [extFL, keyFL, h]))
  simp only [hcl, decide_false] at K
  obtain ⟨hFC, hHC⟩ := fieldAt hL hC (mem (5 + cv tr T_NODE s hplen, 32) (by simp [extFL]))
  have C := kidSer hL hFC hHC sC
  have T0 : rowsB tr b s 1 = [3] := by
    rw [rowsB_one, tagByte hL hr0 sT,
      cv_zero (typeZeros hL hC (x := te) (y := tb1) (by simp) ht (by simp) (by decide)),
      cv_zero (typeZeros hL hC (x := te) (y := tb2) (by simp) ht (by simp) (by decide)), hcv]
  obtain ⟨hF1, hH1⟩ := fieldAt hL hC (mem (1, 4) (by simp [extFL, keyFL]))
  have T1 : rowsB tr b (s + 1) 4 = u32r (cv tr T_NODE s hplen) := by
    rw [hplBytes hL hF1 hH1 sH, cvConst hL hC (by simp [nodeConst]) (by omega)]
  have P0 := pbOf hL hC (o := 0) (L := 1) (mem _ (by simp [extFL, keyFL])) (by simpa using sT) (by simp [states]) (by decide) (by decide)
  have P1 := pbOf hL hC (L := 4) (mem _ (by simp [extFL, keyFL])) sH (by simp [states]) (by decide) (by decide)
  have P5 := pbOf hL hC (L := 1) (mem _ (by simp [extFL, keyFL])) sF (by simp [states]) (by decide) (by decide)
  have P6 : rowsB tr pb (s + 6) (cv tr T_NODE s hplen - 1) = rowsB tr b (s + 6) (cv tr T_NODE s hplen - 1) := by
    by_cases h1 : cv tr T_NODE s hplen = 1
    · simp [rowsB, h1]
    · exact pbOf hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [extFL, keyFL, h1])) (sK h1) (by simp [states]) (by decide) (by decide)
  have P37 := pbOf hL hC (L := 8) (mem _ (by simp [extFL])) sM (by simp [states]) (by decide) (by decide)
  simp only [Nat.add_zero] at P0
  have split : ∀ x, rowsB tr x s ℓ = rowsB tr x s 1 ++ (rowsB tr x (s + 1) 4 ++
      ((rowsB tr x (s + 5) 1 ++ rowsB tr x (s + 6) (cv tr T_NODE s hplen - 1)) ++
      (rowsB tr x (s + (5 + cv tr T_NODE s hplen)) 32 ++
      rowsB tr x (s + (37 + cv tr T_NODE s hplen)) 8))) := by
    intro x
    rw [hℓ, show 45 + cv tr T_NODE s hplen = 1 + (4 + ((1 + (cv tr T_NODE s hplen - 1)) + (32 + 8))) by omega]
    simp only [rowsB_add, List.append_assoc]
    rw [show s + 5 + (1 + (cv tr T_NODE s hplen - 1)) = s + (5 + cv tr T_NODE s hplen) by omega]
    rw [show s + (5 + cv tr T_NODE s hplen) + 32 = s + (37 + cv tr T_NODE s hplen) by omega]
  unfold nodeVOf; rw [if_neg hcl, if_pos hcv]
  simp only [NodeV.ser]
  constructor
  · rw [split, T0, T1, K.1, C.1, K.2]; simp only [List.append_assoc]
  · rw [split, ← C.2, P0, P1, P5, P6, P37, T0, T1, K.1, K.2]; simp only [List.append_assoc]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem bitsVal_split (v : Nat → Nat) (off a : Nat) : ∀ c, bitsVal v off (a + c) = bitsVal v off a + 2 ^ a * bitsVal v (off + a) c
  | 0 => by simp [bitsVal]
  | c + 1 => by
    rw [show a + (c + 1) = a + c + 1 by omega]
    simp only [bitsVal]
    rw [bitsVal_split v off a c, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, show off + (a + c) = off + a + c by omega]
    omega

theorem sum_bits (v : Nat → Nat) : ∀ n, (∀ j, j < n → v j ≤ 1) →
    ((List.range n).map fun j => if v j = 1 then 2 ^ j else 0).sum = bitsVal v 0 n
  | 0, _ => rfl
  | n + 1, hv => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_bits v n (fun j hj => hv j (by omega))]
    simp only [bitsVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add]
    have := hv n (by omega)
    by_cases h : v n = 1
    · rw [if_pos h, h]; simp
    · rw [if_neg h, show v n = 0 by omega]; simp

theorem bitsVal_congr {v v' : Nat → Nat} {off len : Nat} (h : ∀ j, j < len → v (off + j) = v' (off + j)) :
    bitsVal v off len = bitsVal v' off len := by
  induction len with
  | zero => rfl
  | succ len ih => simp only [bitsVal]; rw [ih (fun j hj => h j (by omega)), h len (by omega)]

theorem kidOf_present (tr : Trace Fp) (r : Nat) : (kidOf tr r).present = true := by
  unfold kidOf; split <;> rfl

theorem kidBitmap_kidsOf (tr : Trace Fp) (s o : Nat) (hv : ∀ j, j < 16 → cv tr T_NODE s (bm j) ≤ 1) :
    kidBitmap (kidsOf tr s o) = bitsVal (fun j => cv tr T_NODE s (bm j)) 0 16 := by
  rw [← sum_bits _ 16 hv]
  unfold kidBitmap kidsOf
  rw [List.length_map, List.length_range]
  have : ∀ n, ((List.map (fun j => if cv tr T_NODE s (bm j) = 1 then kidOf tr (s + (o + 2 + 32 * belowN tr s j)) else NKid.none)
      (List.range n)).zip (List.range n)) = (List.range n).map fun j =>
      (if cv tr T_NODE s (bm j) = 1 then kidOf tr (s + (o + 2 + 32 * belowN tr s j)) else NKid.none, j) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.map_append, List.zip_append (by simp), ih]; simp
  rw [this, List.map_map]
  congr 1; apply List.map_congr_left; intro j _
  simp only [Function.comp]
  by_cases h : cv tr T_NODE s (bm j) = 1
  · rw [if_pos h, if_pos h, kidOf_present]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem kids_bytes (tr : Trace Fp) (s o : Nat) (p : Bool) :
    (kidsOf tr s o).flatMap (NKid.bytes p) =
      (List.range 16).flatMap fun j =>
        if cv tr T_NODE s (bm j) = 1 then (kidOf tr (s + (o + 2 + 32 * belowN tr s j))).bytes p else [] := by
  unfold kidsOf; rw [List.flatMap_map]; congr 1; funext j; split <;> rfl

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem brOff_eq (hC : NodeCtx tr s ℓ fl) :
    brOff tr s = if tr.cell T_NODE s tb2 = 1 then 37 else 1 := by
  unfold brOff
  by_cases h : tr.cell T_NODE s tb2 = 1
  · rw [if_pos h, if_pos (cv_one h)]
  · rw [if_neg h, if_neg (fun h' => h (of_cv_one h'))]

/-- Bitmap, children windows and `MEM` of a branch. -/
theorem brRest (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) :
    rowsB tr b (s + brOff tr s) (2 + 32 * popN tr s + 8) =
      [kidBitmap (kidsOf tr s (brOff tr s)) % 256, kidBitmap (kidsOf tr s (brOff tr s)) / 256] ++
        ((kidsOf tr s (brOff tr s)).flatMap (NKid.bytes false) ++ rowsB tr b (s + (brOff tr s + 2 + 32 * popN tr s)) 8) ∧
    rowsB tr pb (s + brOff tr s) (2 + 32 * popN tr s + 8) =
      [kidBitmap (kidsOf tr s (brOff tr s)) % 256, kidBitmap (kidsOf tr s (brOff tr s)) / 256] ++
        ((kidsOf tr s (brOff tr s)).flatMap (NKid.bytes true) ++ rowsB tr b (s + (brOff tr s + 2 + 32 * popN tr s)) 8) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, -, -, sB, -, sM, hW⟩ := B
  have hbv : ∀ j, j < 16 → cv tr T_NODE s (bm j) ≤ 1 := fun j hj => cvb hL (nodeStart hL hC).1 (bm_bool hj)
  have KB := kidBitmap_kidsOf tr s (brOff tr s) hbv
  rw [show (16 : Nat) = 8 + 8 from rfl, bitsVal_split] at KB
  simp only [Nat.zero_add] at KB
  have lo8 := bitsVal_lt (fun j => cv tr T_NODE s (bm j)) 0 8 (fun j hj => hbv _ (by omega))
  have hi8 := bitsVal_lt (fun j => cv tr T_NODE s (bm j)) 8 8 (fun j hj => hbv _ (by omega))
  generalize ho : brOff tr s = o at *
  have mem : ∀ p ∈ brFL o (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  obtain ⟨hFB, hHB⟩ := fieldAt hL hC (mem (o, 2) (by simp [brFL]))
  have hrB : s + o + 1 < tr.height T_NODE := by omega
  -- bitmap bytes
  have bmv : ∀ d, d < 2 → ∀ i, i < 16 → cv tr T_NODE (s + o + d) (bm i) = cv tr T_NODE s (bm i) := by
    intro d hd i hi
    rw [show s + o + d = s + (o + d) by omega]
    exact cvConst hL hC (by unfold nodeConst; simp only [List.mem_append, List.mem_map, List.mem_range]
                            exact Or.inr ⟨i, hi, rfl⟩) (by omega)
  have hb0 : cv tr T_NODE (s + o) b = kidBitmap (kidsOf tr s o) % 256 := by
    have e := (bytes hL (r := s + o) (by omega)).2.2.2.2.2.2.2.1 (by simpa using sB) (by simpa using (hFB.fs 0 (by omega)).2 rfl)
    rw [bmLo, eval_bits tr T_NODE (s + o) pub bm 0 8 (fun j hj => isBool hL (by omega) (bm_bool (by omega))),
      cell_eq_cast tr T_NODE (s + o) b] at e
    have bl := bitsVal_lt (fun b => cv tr T_NODE (s + o) (bm b)) 0 8
      (fun j hj => cvb hL (by omega) (bm_bool (by omega)))
    have := fp_cast_eq (cv_lt _ _ _ _) (by unfold P; omega) e
    rw [this, KB, bitsVal_congr (v' := fun j => cv tr T_NODE s (bm j)) (fun j hj => by
      simpa using bmv 0 (by omega) (0 + j) (by omega))]
    omega
  have hb1 : cv tr T_NODE (s + o + 1) b = kidBitmap (kidsOf tr s o) / 256 := by
    have hs1 : tr.cell T_NODE (s + o + 1) sBM = 1 := by rw [hFB.st 1 (by omega) sBM (by simp [states])]; simpa using sB
    have hf1 : tr.cell T_NODE (s + o + 1) fs = 0 :=
      bool01 hL hrB (by simp [boolCols]) (fun h => by have := (hFB.fs 1 (by omega)).1 h; omega)
    have e := (bytes hL (r := s + o + 1) hrB).2.2.2.2.2.2.2.2.1 hs1 hf1
    rw [bmHi, eval_bits tr T_NODE (s + o + 1) pub bm 8 8 (fun j hj => isBool hL hrB (bm_bool (by omega))),
      cell_eq_cast tr T_NODE (s + o + 1) b] at e
    have bl := bitsVal_lt (fun b => cv tr T_NODE (s + o + 1) (bm b)) 8 8
      (fun j hj => cvb hL hrB (bm_bool (by omega)))
    have := fp_cast_eq (cv_lt _ _ _ _) (by unfold P; omega) e
    rw [this, KB, bitsVal_congr (v' := fun j => cv tr T_NODE s (bm j)) (fun j hj => by
      simpa using bmv 1 (by omega) (8 + j) (by omega))]
    omega
  have BM : rowsB tr b (s + o) 2 = [kidBitmap (kidsOf tr s o) % 256, kidBitmap (kidsOf tr s o) / 256] := by
    rw [← hb0, ← hb1]; simp [rowsB, List.range_succ]
  -- windows
  have CH : ∀ p, (List.range (popN tr s)).flatMap (fun j => rowsB tr (if p then pb else b) (s + o + 2 + 32 * j) 32) =
      (kidsOf tr s o).flatMap (NKid.bytes p) := by
    intro p
    rw [kids_bytes]
    have := flatMap_bits (fun j => cv tr T_NODE s (bm j)) (fun w => (kidOf tr (s + (o + 2 + 32 * w))).bytes p) 16 hbv
    unfold belowN; rw [this, ← belowN, ← popN_eq]
    apply flatMap_congr'; intro j hj; rw [List.mem_range] at hj
    obtain ⟨cj, -, -⟩ := hW j hj
    obtain ⟨hFj, hHj⟩ := fieldAt hL hC (mem (o + 2 + 32 * j, 32) (by simp [brFL]; exact Or.inr ⟨j, hj, rfl⟩))
    have K := kidSer hL hFj hHj cj
    rw [show s + o + 2 + 32 * j = s + (o + 2 + 32 * j) by omega]
    cases p
    · exact K.1
    · exact K.2
  have PB := pbOf hL hC (L := 2) (mem _ (by simp [brFL])) sB (by simp [states]) (by decide) (by decide)
  have PM := pbOf hL hC (L := 8) (mem _ (by simp [brFL])) sM (by simp [states]) (by decide) (by decide)
  have split : ∀ x, rowsB tr x (s + o) (2 + 32 * popN tr s + 8) =
      rowsB tr x (s + o) 2 ++ ((List.range (popN tr s)).flatMap (fun j => rowsB tr x (s + o + 2 + 32 * j) 32) ++
        rowsB tr x (s + (o + 2 + 32 * popN tr s)) 8) := by
    intro x
    rw [rowsB_add, rowsB_add, rowsB_blocks, List.append_assoc,
      show s + o + (2 + 32 * popN tr s) = s + (o + 2 + 32 * popN tr s) by omega]
  constructor
  · rw [split, BM, show b = (if false then pb else b) from rfl, CH false]
  · rw [split, PB, BM, PM, show pb = (if true then pb else b) from rfl, CH true]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem brSer (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) :
    rowsB tr b s ℓ = (nodeVOf tr s).ser false ∧ rowsB tr pb s ℓ = (nodeVOf tr s).ser true := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, sT, sVV, sB, -, sM, -⟩ := B
  have R := brRest hL hC hb
  have hr0 : s < tr.height T_NODE := (nodeStart hL hC).1
  have ha0 : tr.cell T_NODE s act = 1 := (nodeStart hL hC).2
  have hTS := typeSumNat hL hr0 ha0
  have hb1 := cvb hL hr0 (x := tb1) (by simp [boolCols])
  have hb2 := cvb hL hr0 (x := tb2) (by simp [boolCols])
  have hcb : cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 := by
    have e := hb
    rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add] at e
    exact fp_cast_eq (by unfold P; omega) (by unfold P; omega) (e.trans rfl)
  have hcl : cv tr T_NODE s tl ≠ 1 := by omega
  have hce : cv tr T_NODE s te ≠ 1 := by omega
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have T0 : rowsB tr b s 1 = [cv tr T_NODE s tb1 + 2 * cv tr T_NODE s tb2] := by
    rw [rowsB_one, tagByte hL hr0 sT, show cv tr T_NODE s te = 0 by omega, Nat.mul_zero, Nat.add_zero]
  have P0 := pbOf hL hC (o := 0) (L := 1) (mem _ (by simp [brFL])) (by simpa using sT) (by simp [states]) (by decide) (by decide)
  simp only [Nat.add_zero] at P0
  unfold nodeVOf; rw [if_neg hcl, if_neg hce]
  simp only [NodeV.ser]
  by_cases h2 : cv tr T_NODE s tb2 = 1
  · have ho : brOff tr s = 37 := by unfold brOff; rw [if_pos h2]
    rw [if_pos h2]
    rw [ho] at R mem hℓ sB sM
    obtain ⟨sV, sH⟩ := sVV ho
    have S := slotSer hL hC (rV := 1) (rH := 5) (mem _ (by simp [brFL])) (mem _ (by simp [brFL])) sV sH rfl
    have split : ∀ x, rowsB tr x s ℓ = rowsB tr x s 1 ++ ((rowsB tr x (s + 1) 4 ++ rowsB tr x (s + 5) 32) ++
        rowsB tr x (s + 37) (2 + 32 * popN tr s + 8)) := by
      intro x
      rw [hℓ, show 37 + 2 + 32 * popN tr s + 8 = 1 + ((4 + 32) + (2 + 32 * popN tr s + 8)) by omega]
      simp only [rowsB_add, List.append_assoc]
    rw [ho]
    constructor
    · rw [split, T0, S.1, R.1, h2, show cv tr T_NODE s tb1 = 0 by omega]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    · rw [split, P0, T0, S.2, R.2, h2, show cv tr T_NODE s tb1 = 0 by omega]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  · have ho : brOff tr s = 1 := by unfold brOff; rw [if_neg h2]
    rw [if_neg h2]
    rw [ho] at R mem hℓ sB sM
    have split : ∀ x, rowsB tr x s ℓ = rowsB tr x s 1 ++ rowsB tr x (s + 1) (2 + 32 * popN tr s + 8) := by
      intro x
      rw [hℓ, show 1 + 2 + 32 * popN tr s + 8 = 1 + (2 + 32 * popN tr s + 8) by omega, rowsB_add]
    rw [ho]
    constructor
    · rw [split, T0, R.1, show cv tr T_NODE s tb1 = 1 by omega, show cv tr T_NODE s tb2 = 0 by omega]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    · rw [split, P0, T0, R.2, show cv tr T_NODE s tb1 = 1 by omega, show cv tr T_NODE s tb2 = 0 by omega]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

/-- Rows = serialization, for every node type. -/
theorem nodeSer (hC : NodeCtx tr s ℓ fl) :
    rowsB tr b s ℓ = (nodeVOf tr s).ser false ∧ rowsB tr pb s ℓ = (nodeVOf tr s).ser true := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  by_cases h1 : cv tr T_NODE s tl = 1
  · exact leafSer hL hC (of_cv_one h1)
  by_cases h2 : cv tr T_NODE s te = 1
  · exact extSer hL hC (of_cv_one h2)
  apply brSer hL hC
  have hb1 := cvb hL hr0 (x := tb1) (by simp [boolCols])
  have hb2 := cvb hL hr0 (x := tb2) (by simp [boolCols])
  rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add, show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]
  rfl

end ZkFormal.Near.NodeProof
