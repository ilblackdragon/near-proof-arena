import ZkFormal.Near.Extract.NodeGated2

/-!
# ZkFormal.Near.Extract.NodeEdge — EDGE messages of node rows
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

/-- Edge provided by a row (as naturals) with its use count. -/
def eAN (tr : Trace Fp) (r : Nat) : Msg :=
  [cv tr T_NODE r nid, cv tr T_NODE r aI, cv tr T_NODE r aS, cv tr T_NODE r aN, cv tr T_NODE r aJ]
def eBN (tr : Trace Fp) (pub : List Fp) (r : Nat) : Msg :=
  [cv tr T_NODE r nid, (kiE.eval tr T_NODE r pub + 1).toNat, (loE.eval tr T_NODE r pub).toNat, cv tr T_NODE r bN,
    cv tr T_NODE r bJ]

def rowEdgeN (tr : Trace Fp) (pub : List Fp) (r : Nat) : List (Msg × Nat) :=
  (if tr.cell T_NODE r gA = 1 then [(eAN tr r, cv tr T_NODE r mA)] else []) ++
  (if tr.cell T_NODE r gB = 1 then [(eBN tr pub r, cv tr T_NODE r mB)] else [])

theorem toFp_toNat (x : Fp) : Fp.ofNat x.toNat = x := Fp.ofNat_toNat x

theorem rowT_edgeS_N (tr : Trace Fp) (pub : List Fp) (r : Nat) :
    rowT tr pub r B_EDGE true = (rowEdgeN tr pub r).map fun eu => Msg.toFp (eu.1 ++ [0]) := by
  rw [rowT_edgeS]
  unfold rowEdgeN gate
  by_cases h1 : tr.cell T_NODE r gA = 1 <;> by_cases h2 : tr.cell T_NODE r gB = 1 <;>
    simp [h1, h2, edgeAV, edgeBV, eAN, eBN, Msg.toFp, cv, toFp_toNat] <;> rfl

theorem rowT_edgeR_N (tr : Trace Fp) (pub : List Fp) (r : Nat) :
    rowT tr pub r B_EDGE false = (rowEdgeN tr pub r).map fun eu => Msg.toFp (eu.1 ++ [eu.2]) := by
  rw [rowT_edgeR]
  unfold rowEdgeN gate
  by_cases h1 : tr.cell T_NODE r gA = 1 <;> by_cases h2 : tr.cell T_NODE r gB = 1 <;>
    simp [h1, h2, edgeAV, edgeBV, eAN, eBN, Msg.toFp, cv, toFp_toNat]

theorem cv_of_eq {tr : Trace Fp} {r x v : Nat} (h : tr.cell T_NODE r x = ((v : Nat) : Fp)) (hv : v < P) :
    cv tr T_NODE r x = v := by
  unfold cv; rw [h, toNat_natCast, Nat.mod_eq_of_lt hv]

theorem toNat_of_eq {a : Fp} {v : Nat} (h : a = ((v : Nat) : Fp)) (hv : v < P) : a.toNat = v := by
  rw [h, toNat_natCast, Nat.mod_eq_of_lt hv]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem fp_zero_add_eq {c' : Fp} (h : 0 + c' = 1) : c' = 1 := by grind

theorem fp_gA0 (a b' c' d' : Fp) (e : Fp) (h1 : a = 0) (h2 : b' = 0) (h3 : c' = 0) (h4 : d' = 0) :
    a + (b' * e + (c' + (d' + 0))) = 0 := by rw [h1, h2, h3, h4]; grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- Gate values on a row of a node (`gP`, `gD − gP` written out). -/
theorem gatesAt {r : Nat} (hr : r < tr.height T_NODE) :
    tr.cell T_NODE r gA = tr.cell T_NODE r sKEY + (tr.cell T_NODE r sHPF * tr.cell T_NODE r odd *
      (1 - tr.cell T_NODE r nokey * tr.cell T_NODE r xdead) + (tr.cell T_NODE r fs * tr.cell T_NODE r sCH *
      tr.cell T_NODE r rv * (tr.cell T_NODE r tb1 + tr.cell T_NODE r tb2) + (tr.cell T_NODE r fs *
      tr.cell T_NODE r sVH * tr.cell T_NODE r tv + (if r = 0 then 1 else 0)))) ∧
    tr.cell T_NODE r gB = tr.cell T_NODE r sKEY - tr.cell T_NODE r sKEY * tr.cell T_NODE r fe * tr.cell T_NODE r xdead := by
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  refine ⟨?_, G.2.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [G.2.2.2.2.2.2.2.2.2.2.2.1, M.2.1, G.1]
  grind

/-- A row with no edge-providing role emits nothing on EDGE. -/
theorem quietEdge {r : Nat} (hr : r < tr.height T_NODE) (hk : tr.cell T_NODE r sKEY = 0)
    (hf : tr.cell T_NODE r sHPF = 0)
    (hw : tr.cell T_NODE r fs = 0 ∨ (tr.cell T_NODE r sCH = 0 ∧ tr.cell T_NODE r sVH = 0)) (h0 : r ≠ 0) :
    rowEdgeN tr pub r = [] := by
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hA : tr.cell T_NODE r gA = 0 := by
    rw [GA, hk, hf, if_neg h0]
    rcases hw with h | ⟨h1, h2⟩
    · rw [h]; grind
    · rw [h1, h2]; grind
  have hB : tr.cell T_NODE r gB = 0 := by rw [GB, hk]; grind
  simp [rowEdgeN, hA, hB]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem cvC (hC : NodeCtx tr s ℓ fl) {x d : Nat} (hx : x ∈ nodeConst) (hd : d < ℓ) :
    cv tr T_NODE (s + d) x = cv tr T_NODE s x := cvConst hL hC hx hd

/-- A field that provides no edge. -/
theorem plainEdges (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (hx : tr.cell T_NODE (s + o) x = 1) (hxs : x ∈ states) (h1 : sKEY ≠ x) (h2 : sHPF ≠ x) (h3 : sCH ≠ x)
    (h4 : sVH ≠ x) : (List.range' (s + o) L).flatMap (rowEdgeN tr pub) = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  apply flatMap_range'_nil; intro d hd
  have hr : s + o + d < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o + d) act = 1 := hF.act d hd
  have hx' : tr.cell T_NODE (s + o + d) x = 1 := by rw [hF.st d hd x hxs, hx]
  exact quietEdge hL hr (stOnly hL hr ha hx' hxs (by simp [states]) h1) (stOnly hL hr ha hx' hxs (by simp [states]) h2)
    (Or.inr ⟨stOnly hL hr ha hx' hxs (by simp [states]) h3, stOnly hL hr ha hx' hxs (by simp [states]) h4⟩) (by omega)

/-- A window field provides edges only at its first row. -/
theorem winEdges (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (hw : tr.cell T_NODE (s + o) sVH + tr.cell T_NODE (s + o) sCH = 1) :
    (List.range' (s + o) L).flatMap (rowEdgeN tr pub) = rowEdgeN tr pub (s + o) := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hpos := hF.pos
  rw [show L = 1 + (L - 1) by omega, ← List.range'_append_1, List.range'_one, List.flatMap_append,
    List.flatMap_singleton]
  rw [flatMap_range'_nil _ _ _ (fun j hj => by
    have hr : s + o + 1 + j < tr.height T_NODE := by omega
    rw [show s + o + 1 + j = s + o + (1 + j) by omega] at hr ⊢
    have ha := hF.act (1 + j) (by omega)
    have hfs : tr.cell T_NODE (s + o + (1 + j)) fs = 0 :=
      bool01 hL hr (by simp [boolCols]) (fun h => by have := (hF.fs (1 + j) (by omega)).1 h; omega)
    have ha0 : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 hpos
    have hr0 : s + o < tr.height T_NODE := by omega
    have hkf : tr.cell T_NODE (s + o) sKEY = 0 ∧ tr.cell T_NODE (s + o) sHPF = 0 := by
      rcases isBool hL hr0 (x := sVH) (by simp [boolCols, states]) with h1 | h1
      · rw [h1] at hw
        have hc : tr.cell T_NODE (s + o) sCH = 1 := fp_zero_add_eq hw
        exact ⟨stOnly hL (x := sCH) (y := sKEY) hr0 ha0 hc (by simp [states]) (by simp [states]) (by decide),
          stOnly hL (x := sCH) (y := sHPF) hr0 ha0 hc (by simp [states]) (by simp [states]) (by decide)⟩
      · exact ⟨stOnly hL (x := sVH) (y := sKEY) hr0 ha0 h1 (by simp [states]) (by simp [states]) (by decide),
          stOnly hL (x := sVH) (y := sHPF) hr0 ha0 h1 (by simp [states]) (by simp [states]) (by decide)⟩
    obtain ⟨hk, hf⟩ := hkf
    exact quietEdge hL hr (by rw [hF.st _ (by omega) sKEY (by simp [states]), hk])
      (by rw [hF.st _ (by omega) sHPF (by simp [states]), hf]) (Or.inl hfs) (by omega))]
  simp

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem fp_tagA (x : Fp) : (0 : Fp) + (0 * x * 0 + (0 + x)) = x := by grind
theorem fp_keyA (a b' : Fp) : (1 : Fp) + (0 * a * b' + (0 + (0 + 0))) = 1 := by grind
theorem fp_keyB (f d : Fp) : (1 : Fp) - 1 * f * d = 1 - f * d := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem hP_of (hC : NodeCtx tr s ℓ fl) : 2 * (s + ℓ) + 8 < P := by
  have := hC.bound; have := height_le hL; unfold P; omega

/-- The node start: the root provides the walk's first step. -/
theorem tagEdge (hC : NodeCtx tr s ℓ fl) :
    rowEdgeN tr pub s = if s = 0 then [([0, 0, SYM_START, cv tr T_NODE s res, 0], cv tr T_NODE s mA)] else [] := by
  obtain ⟨hr, ha⟩ := nodeStart hL hC
  obtain ⟨-, -, sT⟩ := firstField hL hC
  have z := fun y (hy : y ∈ states) (hne : y ≠ sTAG) => stOnly hL hr ha sT (by simp [states]) hy hne
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  rw [z sKEY (by simp [states]) (by decide), z sHPF (by simp [states]) (by decide),
    z sCH (by simp [states]) (by decide), z sVH (by simp [states]) (by decide)] at GA
  rw [z sKEY (by simp [states]) (by decide)] at GB
  have hB : tr.cell T_NODE s gB = 0 := by rw [GB]; grind
  unfold rowEdgeN; rw [hB]
  by_cases h0 : s = 0
  · subst h0
    have hA : tr.cell T_NODE 0 gA = 1 := by rw [GA, if_pos rfl]; grind
    have E := (edgeFacts hL hr (pub := pub)).2.2.2.2 rfl
    simp only at E
    obtain ⟨e1, e2, e3, e4⟩ := E
    have hn := (firstRow hL (by omega)).2.2.1
    simp [hA, eAN, cv, e1, e2, e3, e4, hn, toNat_natCast, SYM_START, Fp.toNat_zero]
    unfold P; omega
  · have hA : tr.cell T_NODE s gA = 0 := by rw [GA, if_neg h0]; grind
    simp [hA, h0]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem fp_zero_mul (x : Fp) : (0 : Fp) * x = 0 := by grind

theorem fp_hpfA (o k d : Fp) : (0 : Fp) + (1 * o * (1 - k * d) + (0 * 0 * 0 * 0 + (0 * 0 * 0 + 0))) = o * (1 - k * d) := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- Common facts at a row inside a node. -/
theorem inRow (hC : NodeCtx tr s ℓ fl) {d : Nat} (hd : d < ℓ) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp))
    (hnP : n < P) : s + d < tr.height T_NODE ∧ tr.cell T_NODE (s + d) act = 1 ∧ cv tr T_NODE (s + d) nid = n := by
  refine ⟨by have := hC.bound; omega, segAct hL hC hd, ?_⟩
  rw [cvC hL hC (by simp [nodeConst]) hd]; exact cv_of_eq hn hnP

theorem hpfEdge (hC : NodeCtx tr s ℓ fl) (hm : (5, 1) ∈ fl) (sF : tr.cell T_NODE (s + 5) sHPF = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    rowEdgeN tr pub (s + 5) = if cv tr T_NODE s odd = 1 ∧ ¬(cv tr T_NODE s nokey = 1 ∧ cv tr T_NODE s xdead = 1) then
      [([n, 0, loN tr (s + 5), if cv tr T_NODE s xlast0 = 1 then cv tr T_NODE s xres else n,
        if cv tr T_NODE s xlast0 = 1 then 0 else 1], cv tr T_NODE (s + 5) mA)] else [] := by
  have h5 : 5 < ℓ := by have := (hC.fields.field _ hm).2; simp at this; omega
  obtain ⟨hr, ha, hnid⟩ := inRow hL hC h5 hn hnP
  have z := fun y (hy : y ∈ states) (hne : y ≠ sHPF) => stOnly hL hr ha sF (by simp [states]) hy hne
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  rw [z sKEY (by simp [states]) (by decide), sF, z sCH (by simp [states]) (by decide),
    z sVH (by simp [states]) (by decide), if_neg (by omega)] at GA
  rw [z sKEY (by simp [states]) (by decide)] at GB
  have hB : tr.cell T_NODE (s + 5) gB = 0 := by rw [GB]; grind
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx h5
  rw [cst odd (by simp [nodeConst]), cst nokey (by simp [nodeConst]), cst xdead (by simp [nodeConst])] at GA
  have GA' : tr.cell T_NODE (s + 5) gA = tr.cell T_NODE s odd * (1 - tr.cell T_NODE s nokey * tr.cell T_NODE s xdead) := by
    rw [GA]; grind
  have hr0 : s < tr.height T_NODE := by omega
  have bo := isBool hL hr0 (x := odd) (by simp [boolCols])
  have bk := isBool hL hr0 (x := nokey) (by simp [boolCols])
  have bd := isBool hL hr0 (x := xdead) (by simp [boolCols])
  unfold rowEdgeN; rw [hB]
  rcases bo with ho | ho
  · have hA : tr.cell T_NODE (s + 5) gA = 0 := by rw [GA', ho]; exact fp_zero_mul _
    have hc : ¬ (cv tr T_NODE s odd = 1 ∧ ¬(cv tr T_NODE s nokey = 1 ∧ cv tr T_NODE s xdead = 1)) := by
      rw [cv_zero ho]; omega
    rw [hA, if_neg hc]; simp
  · have E := (edgeFacts hL hr (pub := pub)).2.1 sF (show tr.cell T_NODE (s + 5) odd = 1 by
      rw [cst odd (by simp [nodeConst]), ho])
    obtain ⟨e1, e2, e3, e4⟩ := E
    simp only at e1 e2 e3 e4
    obtain ⟨-, -, -, hl⟩ := nibs hL hr (pub := pub)
    have hlx := cst xlast0 (by simp [nodeConst])
    have hxr := cst xres (by simp [nodeConst])
    by_cases hkd : tr.cell T_NODE s nokey = 1 ∧ tr.cell T_NODE s xdead = 1
    · have hA : tr.cell T_NODE (s + 5) gA = 0 := by rw [GA', ho, hkd.1, hkd.2]; decide
      have hc : ¬ (cv tr T_NODE s odd = 1 ∧ ¬(cv tr T_NODE s nokey = 1 ∧ cv tr T_NODE s xdead = 1)) := by
        rw [cv_one hkd.1, cv_one hkd.2]; omega
      rw [hA, if_neg hc]; simp
    · have hA : tr.cell T_NODE (s + 5) gA = 1 := by
        rw [GA', ho]
        rcases bk with hk | hk <;> rcases bd with hd' | hd'
        · rw [hk, hd']; decide
        · rw [hk, hd']; decide
        · rw [hk, hd']; decide
        · exact absurd ⟨hk, hd'⟩ hkd
      have hc : cv tr T_NODE s odd = 1 ∧ ¬(cv tr T_NODE s nokey = 1 ∧ cv tr T_NODE s xdead = 1) :=
        ⟨cv_one ho, fun h => hkd ⟨of_cv_one h.1, of_cv_one h.2⟩⟩
      rw [hA, if_pos hc]
      have hlo : cv tr T_NODE (s + 5) aS = loN tr (s + 5) := by
        unfold cv; rw [e2, hl, toNat_natCast, Nat.mod_eq_of_lt (by have := (nibs hL hr (pub := pub)).2.1; unfold P; omega)]
      have hI : cv tr T_NODE (s + 5) aI = 0 := by unfold cv; rw [e1]; exact Fp.toNat_zero
      rcases isBool hL hr0 (x := xlast0) (by simp [boolCols]) with hx | hx
      · obtain ⟨f1, f2⟩ := e3 (by rw [hlx, hx])
        have hN : cv tr T_NODE (s + 5) aN = n := by unfold cv; rw [f1]; exact hnid
        have hJ : cv tr T_NODE (s + 5) aJ = 1 := by unfold cv; rw [f2]; exact Fp.toNat_one
        simp [eAN, hnid, hlo, hI, hN, hJ, cv_zero hx]
      · obtain ⟨f1, f2⟩ := e4 (by rw [hlx, hx])
        have hN : cv tr T_NODE (s + 5) aN = cv tr T_NODE s xres := by unfold cv; rw [f1, hxr]
        have hJ : cv tr T_NODE (s + 5) aJ = 0 := by unfold cv; rw [f2]; exact Fp.toNat_zero
        simp [eAN, hnid, hlo, hI, hN, hJ, cv_one hx]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem fp_one_gA (a b' c' d' e f g : Fp) : (1 : Fp) + (0 * a * b' + (c' * 0 * d' * e + (f * 0 * g + 0))) = 1 := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- A key byte row: the high-nibble edge (A) and, unless it is the dead last nibble of an
extension, the low-nibble edge (B). -/
theorem keyRowEdge (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (sK : tr.cell T_NODE (s + o) sKEY = 1) {d : Nat} (hd : d < L) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    rowEdgeN tr pub (s + o + d) =
      [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + o + d), n, 2 * d + cv tr T_NODE s odd + 1], cv tr T_NODE (s + o + d) mA)] ++
      (if d + 1 = L ∧ cv tr T_NODE s xdead = 1 then [] else
        [([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + o + d),
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then cv tr T_NODE s xres else n,
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then 0 else 2 * d + cv tr T_NODE s odd + 2], cv tr T_NODE (s + o + d) mB)]) := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hdℓ : o + d < ℓ := by have := (hC.fields.field _ hm).2; simp at this; omega
  have hP := hP_of hL hC
  obtain ⟨hr, ha, hnid⟩ := inRow hL hC hdℓ hn hnP
  rw [← Nat.add_assoc] at hr ha hnid
  have sK' : tr.cell T_NODE (s + o + d) sKEY = 1 := by rw [hF.st d hd sKEY (by simp [states]), sK]
  have z := fun y (hy : y ∈ states) (hne : y ≠ sKEY) => stOnly hL hr ha sK' (by simp [states]) hy hne
  have cst := fun x (hx : x ∈ nodeConst) => (show tr.cell T_NODE (s + o + d) x = tr.cell T_NODE s x by
    rw [Nat.add_assoc]; exact segConst hL hC hx hdℓ)
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  rw [sK', z sHPF (by simp [states]) (by decide), z sCH (by simp [states]) (by decide),
    z sVH (by simp [states]) (by decide), if_neg (by omega)] at GA
  have hA : tr.cell T_NODE (s + o + d) gA = 1 := by rw [GA]; exact fp_one_gA _ _ _ _ _ _ _
  rw [sK', cst xdead (by simp [nodeConst])] at GB
  have hidx := hF.idx d hd
  have E := (edgeFacts hL hr (pub := pub)).1 sK'
  simp only at E
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := E
  obtain ⟨n1, n2, hhi, hlo⟩ := nibs hL hr (pub := pub)
  have bo := cvb hL (r := s) (by omega) (x := odd) (by simp [boolCols])
  have hki : kiE.eval tr T_NODE (s + o + d) pub = ((2 * d + cv tr T_NODE s odd : Nat) : Fp) := by
    simp only [kiE, eval_add, eval_smul, eval_c]
    rw [hidx, cst odd (by simp [nodeConst]), cell_eq_cast tr T_NODE s odd, natCast_add, natCast_mul]
  have kiN1 : (kiE.eval tr T_NODE (s + o + d) pub + 1).toNat = 2 * d + cv tr T_NODE s odd + 1 := by
    rw [hki, show (1 : Fp) = ((1 : Nat) : Fp) from rfl, ← natCast_add]; exact toNat_of_eq rfl (by omega)
  have kiN2 : (kiE.eval tr T_NODE (s + o + d) pub + 2).toNat = 2 * d + cv tr T_NODE s odd + 2 := by
    rw [hki, show (2 : Fp) = ((2 : Nat) : Fp) from rfl, ← natCast_add]; exact toNat_of_eq rfl (by omega)
  have hfe : tr.cell T_NODE (s + o + d) fe = 1 ↔ d + 1 = L := hF.fe d hd
  have eA : eAN tr (s + o + d) = [n, 2 * d + cv tr T_NODE s odd, hiN tr (s + o + d), n, 2 * d + cv tr T_NODE s odd + 1] := by
    unfold eAN
    have hb1 : 2 * d + cv tr T_NODE s odd < P := by omega
    rw [hnid, cv_of_eq (e1.trans hki) hb1, cv_of_eq (e2.trans hhi) (by unfold P; omega),
      show cv tr T_NODE (s + o + d) aN = n by unfold cv; rw [e3]; exact hnid,
      show cv tr T_NODE (s + o + d) aJ = 2 * d + cv tr T_NODE s odd + 1 by
        unfold cv; rw [e4]; exact kiN1]
  unfold rowEdgeN
  rw [hA, if_pos rfl, eA]
  congr 1
  rcases isBool hL hr (x := fe) (by simp [boolCols]) with hf | hf
  · -- not the last row
    have hnl : ¬ d + 1 = L := fun h => by rw [hfe.2 h] at hf; exact fp_one_ne_zero hf
    have hB : tr.cell T_NODE (s + o + d) gB = 1 := by rw [GB, hf]; grind
    obtain ⟨f1, f2⟩ := e5 (by rw [hf]; grind)
    rw [hB, if_pos rfl, if_neg (fun h => hnl h.1), if_neg (fun h => hnl h.1), if_neg (fun h => hnl h.1)]
    unfold eBN
    rw [hnid, kiN1, toNat_of_eq hlo (by unfold P; omega),
      show cv tr T_NODE (s + o + d) bN = n by unfold cv; rw [f1]; exact hnid,
      show cv tr T_NODE (s + o + d) bJ = 2 * d + cv tr T_NODE s odd + 2 by unfold cv; rw [f2]; exact kiN2]
  · have hl : d + 1 = L := hfe.1 hf
    rcases isBool hL (r := s) (by omega) (x := xdead) (by simp [boolCols]) with hx | hx
    · have hB : tr.cell T_NODE (s + o + d) gB = 1 := by rw [GB, hx]; grind
      rw [hB, if_pos rfl, if_neg (fun h => by rw [cv_zero hx] at h; omega)]
      unfold eBN
      rw [hnid, kiN1, toNat_of_eq hlo (by unfold P; omega)]
      rcases isBool hL (r := s) (by omega) (x := te) (by simp [boolCols]) with ht | ht
      · obtain ⟨f1, f2⟩ := e5 (by rw [cst te (by simp [nodeConst]), ht]; grind)
        rw [if_neg (fun h => by rw [cv_zero ht] at h; omega), if_neg (fun h => by rw [cv_zero ht] at h; omega),
          show cv tr T_NODE (s + o + d) bN = n by unfold cv; rw [f1]; exact hnid,
          show cv tr T_NODE (s + o + d) bJ = 2 * d + cv tr T_NODE s odd + 2 by unfold cv; rw [f2]; exact kiN2]
      · obtain ⟨f1, f2⟩ := e6 hf (by rw [cst te (by simp [nodeConst]), ht])
        rw [if_pos ⟨hl, cv_one ht⟩, if_pos ⟨hl, cv_one ht⟩,
          show cv tr T_NODE (s + o + d) bN = cv tr T_NODE s xres by unfold cv; rw [f1, cst xres (by simp [nodeConst])],
          show cv tr T_NODE (s + o + d) bJ = 0 by unfold cv; rw [f2]; exact Fp.toNat_zero]
    · have hB : tr.cell T_NODE (s + o + d) gB = 0 := by rw [GB, hx, hf]; grind
      rw [hB, if_pos (show d + 1 = L ∧ cv tr T_NODE s xdead = 1 from ⟨hl, cv_one hx⟩)]; simp

end ZkFormal.Near.NodeProof
