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
theorem flatMap_bits {α : Type} (f : Nat → Nat) (F : Nat → List α) (hf : ∀ j, f j ≤ 1) (n : Nat) :
    (List.range n).flatMap (fun j => if f j = 1 then F (((List.range j).map f).sum) else []) =
      (List.range (((List.range n).map f).sum)).flatMap F := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := hf n
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
