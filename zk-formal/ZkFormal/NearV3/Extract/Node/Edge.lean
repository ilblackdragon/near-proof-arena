import ZkFormal.NearV3.Extract.Node.Gated2

/-!
# ZkFormal.Near.Extract.NodeEdge — EDGE messages of node rows
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-- Edge provided by a row (as naturals) with its use count. -/
def eAN (tr : Trace Fp) (r : Nat) : Msg :=
  [cv tr T_NODE r nid, cv tr T_NODE r aI, cv tr T_NODE r aS, cv tr T_NODE r aN, cv tr T_NODE r aJ, cv tr T_NODE r aK]
def eBN (tr : Trace Fp) (pub : List Fp) (r : Nat) : Msg :=
  [cv tr T_NODE r nid, cv tr T_NODE r bI, cv tr T_NODE r bS, cv tr T_NODE r bN, cv tr T_NODE r bJ, cv tr T_NODE r bK]

def rowEdgeN (tr : Trace Fp) (pub : List Fp) (r : Nat) : List (Msg × Nat) :=
  (if tr.cell T_NODE r gA = 1 then [(eAN tr r, cv tr T_NODE r mA)] else []) ++
  (if tr.cell T_NODE r gB = 1 then [(eBN tr pub r, cv tr T_NODE r mB)] else [])

theorem toFp_toNat (x : Fp) : Fp.ofNat x.toNat = x := Fp.ofNat_toNat x

theorem fp_zero_mul (x : Fp) : (0 : Fp) * x = 0 := by grind

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

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem fp_zero_add_eq {c' : Fp} (h : 0 + c' = 1) : c' = 1 := by grind

theorem fp_gA0 (a b' c' d' : Fp) (e : Fp) (h1 : a = 0) (h2 : b' = 0) (h3 : c' = 0) (h4 : d' = 0) :
    a + (b' * e + (c' + (d' + 0))) = 0 := by rw [h1, h2, h3, h4]; grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- Gate values on a row of a node (`gP`, `gD − gP` written out). -/
theorem gatesAt {r : Nat} (hr : r < tr.height T_NODE) :
    tr.cell T_NODE r gA = tr.cell T_NODE r sKEY + (tr.cell T_NODE r sHPF * tr.cell T_NODE r odd +
      (tr.cell T_NODE r fs * tr.cell T_NODE r sCH * tr.cell T_NODE r rv * (tr.cell T_NODE r tb1 + tr.cell T_NODE r tb2) +
      tr.cell T_NODE r fs * tr.cell T_NODE r sVH * tr.cell T_NODE r tv)) ∧
    tr.cell T_NODE r gB = tr.cell T_NODE r sKEY + tr.cell T_NODE r tl * tr.cell T_NODE r sMEM * tr.cell T_NODE r fs := by
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  refine ⟨?_, ?_⟩
  · rw [G.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, M.2.1, G.1]; grind
  · rw [G.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, G.2.2.1]

/-- A row with no edge-providing role emits nothing on EDGE. -/
theorem quietEdge {r : Nat} (hr : r < tr.height T_NODE) (hk : tr.cell T_NODE r sKEY = 0)
    (hf : tr.cell T_NODE r sHPF = 0)
    (hw : tr.cell T_NODE r fs = 0 ∨ (tr.cell T_NODE r sCH = 0 ∧ tr.cell T_NODE r sVH = 0 ∧ tr.cell T_NODE r sMEM = 0)) :
    rowEdgeN tr pub r = [] := by
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hA : tr.cell T_NODE r gA = 0 := by
    rw [GA, hk, hf]
    rcases hw with h | ⟨h1, h2, -⟩
    · rw [h]; grind
    · rw [h1, h2]; grind
  have hB : tr.cell T_NODE r gB = 0 := by
    rw [GB, hk]
    rcases hw with h | ⟨-, -, h3⟩
    · rw [h]; grind
    · rw [h3]; grind
  simp [rowEdgeN, hA, hB]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem cvC (hC : NodeCtx tr s ℓ fl) {x d : Nat} (hx : x ∈ nodeConst) (hd : d < ℓ) :
    cv tr T_NODE (s + d) x = cv tr T_NODE s x := cvConst hL hC hx hd

/-- A field that provides no edge. -/
theorem plainEdges (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (hx : tr.cell T_NODE (s + o) x = 1) (hxs : x ∈ states) (h1 : sKEY ≠ x) (h2 : sHPF ≠ x) (h3 : sCH ≠ x)
    (h4 : sVH ≠ x) (h5 : sMEM ≠ x) : (List.range' (s + o) L).flatMap (rowEdgeN tr pub) = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  apply flatMap_range'_nil; intro d hd
  have hr : s + o + d < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o + d) act = 1 := hF.act d hd
  have hx' : tr.cell T_NODE (s + o + d) x = 1 := by rw [hF.st d hd x hxs, hx]
  exact quietEdge hL hr (stOnly hL hr ha hx' hxs (by simp [states]) h1) (stOnly hL hr ha hx' hxs (by simp [states]) h2)
    (Or.inr ⟨stOnly hL hr ha hx' hxs (by simp [states]) h3, stOnly hL hr ha hx' hxs (by simp [states]) h4,
      stOnly hL hr ha hx' hxs (by simp [states]) h5⟩)

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
      (by rw [hF.st _ (by omega) sHPF (by simp [states]), hf]) (Or.inl hfs))]
  simp

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem fp_tagA (x : Fp) : (0 : Fp) + (0 * x * 0 + (0 + x)) = x := by grind
theorem fp_keyA (a b' : Fp) : (1 : Fp) + (0 * a * b' + (0 + (0 + 0))) = 1 := by grind
theorem fp_keyB (f d : Fp) : (1 : Fp) - 1 * f * d = 1 - f * d := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem hP_of (hC : NodeCtx tr s ℓ fl) : 2 * (s + ℓ) + 8 < P := by
  have := hC.bound; have := height_le hL; unfold P; omega

/-- The node start provides no edge (the walks' `START` edges come from the instance heads). -/
theorem tagEdge (hC : NodeCtx tr s ℓ fl) : rowEdgeN tr pub s = [] := by
  obtain ⟨hr, ha⟩ := nodeStart hL hC
  obtain ⟨-, -, sT⟩ := firstField hL hC
  have z := fun y (hy : y ∈ states) (hne : y ≠ sTAG) => stOnly hL hr ha sT (by simp [states]) hy hne
  exact quietEdge hL hr (z sKEY (by simp [states]) (by decide)) (z sHPF (by simp [states]) (by decide))
    (Or.inr ⟨z sCH (by simp [states]) (by decide), z sVH (by simp [states]) (by decide),
      z sMEM (by simp [states]) (by decide)⟩)

/-- Common facts at a row inside a node. -/
theorem inRow (hC : NodeCtx tr s ℓ fl) {d : Nat} (hd : d < ℓ) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp))
    (hnP : n < P) : s + d < tr.height T_NODE ∧ tr.cell T_NODE (s + d) act = 1 ∧ cv tr T_NODE (s + d) nid = n := by
  refine ⟨by have := hC.bound; omega, segAct hL hC hd, ?_⟩
  rw [cvC hL hC (by simp [nodeConst]) hd]; exact cv_of_eq hn hnP


/-- The odd first nibble (`HPF` row of an odd key). -/
theorem hpfEdge (hC : NodeCtx tr s ℓ fl) (hm : (5, 1) ∈ fl) (sF : tr.cell T_NODE (s + 5) sHPF = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    rowEdgeN tr pub (s + 5) = if cv tr T_NODE s odd = 1 then
      [([n, 0, loN tr (s + 5), if cv tr T_NODE s xlast0 = 1 then cv tr T_NODE s xtgt else n,
        if cv tr T_NODE s xlast0 = 1 then cv tr T_NODE s xtgJ else 1, EK_KEY], cv tr T_NODE (s + 5) mA)] else [] := by
  have h5 : 5 < ℓ := by have := (hC.fields.field _ hm).2; simp at this; omega
  obtain ⟨hr, ha, hnid⟩ := inRow hL hC h5 hn hnP
  have z := fun y (hy : y ∈ states) (hne : y ≠ sHPF) => stOnly hL hr ha sF (by simp [states]) hy hne
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx h5
  have hB : tr.cell T_NODE (s + 5) gB = 0 := by
    rw [GB, z sKEY (by simp [states]) (by decide), z sMEM (by simp [states]) (by decide)]; grind
  have GA' : tr.cell T_NODE (s + 5) gA = tr.cell T_NODE s odd := by
    rw [GA, z sKEY (by simp [states]) (by decide), sF, z sCH (by simp [states]) (by decide),
      z sVH (by simp [states]) (by decide), cst odd (by simp [nodeConst])]; grind
  have hr0 : s < tr.height T_NODE := by omega
  unfold rowEdgeN; rw [hB]
  rcases isBool hL hr0 (x := odd) (by simp [boolCols]) with ho | ho
  · rw [if_neg (show ¬ cv tr T_NODE s odd = 1 by rw [cv_zero ho]; decide), GA', ho]; simp
  · have E := (edgeFacts hL hr (pub := pub)).2.2.1 sF (show tr.cell T_NODE (s + 5) odd = 1 by
      rw [cst odd (by simp [nodeConst]), ho])
    obtain ⟨e1, e2, eK, e3, e4⟩ := E
    simp only at e1 e2 eK e3 e4
    obtain ⟨-, -, -, hl⟩ := nibs hL hr (pub := pub)
    have hlx := cst xlast0 (by simp [nodeConst])
    rw [if_pos (cv_one ho), GA', ho, if_pos rfl]
    have hlo : cv tr T_NODE (s + 5) aS = loN tr (s + 5) := by
      unfold cv; rw [e2, hl, toNat_natCast, Nat.mod_eq_of_lt (by have := (nibs hL hr (pub := pub)).2.1; unfold P; omega)]
    have hI : cv tr T_NODE (s + 5) aI = 0 := by unfold cv; rw [e1]; exact Fp.toNat_zero
    have hK : cv tr T_NODE (s + 5) aK = EK_KEY := cv_of_eq eK (by unfold EK_KEY P; omega)
    rcases isBool hL hr0 (x := xlast0) (by simp [boolCols]) with hx | hx
    · obtain ⟨f1, f2⟩ := e3 (by rw [hlx, hx])
      have hN : cv tr T_NODE (s + 5) aN = n := by unfold cv; rw [f1]; exact hnid
      have hJ : cv tr T_NODE (s + 5) aJ = 1 := by unfold cv; rw [f2]; exact Fp.toNat_one
      simp [eAN, hnid, hlo, hI, hN, hJ, hK, cv_zero hx]
    · obtain ⟨f1, f2⟩ := e4 (by rw [hlx, hx])
      have hN : cv tr T_NODE (s + 5) aN = cv tr T_NODE s xtgt := by
        unfold cv; rw [f1, cst xtgt (by simp [nodeConst])]
      have hJ : cv tr T_NODE (s + 5) aJ = cv tr T_NODE s xtgJ := by
        unfold cv; rw [f2, cst xtgJ (by simp [nodeConst])]
      simp [eAN, hnid, hlo, hI, hN, hJ, hK, cv_one hx]

/-- A key byte row: the high-nibble edge (A) and the low-nibble edge (B); the last nibble of an
extension goes to `(xtgt, xtgJ)`. -/
theorem keyRowEdge (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (sK : tr.cell T_NODE (s + o) sKEY = 1) {d : Nat} (hd : d < L) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    rowEdgeN tr pub (s + o + d) =
      [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + o + d), n, 2 * d + cv tr T_NODE s odd + 1, EK_KEY],
          cv tr T_NODE (s + o + d) mA),
       ([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + o + d),
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then cv tr T_NODE s xtgt else n,
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then cv tr T_NODE s xtgJ else 2 * d + cv tr T_NODE s odd + 2, EK_KEY],
          cv tr T_NODE (s + o + d) mB)] := by
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
  have hA : tr.cell T_NODE (s + o + d) gA = 1 := by
    rw [GA, sK', z sHPF (by simp [states]) (by decide), z sCH (by simp [states]) (by decide),
      z sVH (by simp [states]) (by decide)]; grind
  have hB : tr.cell T_NODE (s + o + d) gB = 1 := by
    rw [GB, sK', z sMEM (by simp [states]) (by decide)]; grind
  have hidx := hF.idx d hd
  have E := (edgeFacts hL hr (pub := pub)).1 sK'
  simp only at E
  obtain ⟨e1, e2, e3, e4, eK, eBI, eBS, eBK, e5, e6⟩ := E
  obtain ⟨n1, n2, hhi, hlo⟩ := nibs hL hr (pub := pub)
  have bo := cvb hL (r := s) (by omega) (x := odd) (by simp [boolCols])
  have hki : kiE.eval tr T_NODE (s + o + d) pub = ((2 * d + cv tr T_NODE s odd : Nat) : Fp) := by
    simp only [kiE, eval_add, eval_smul, eval_c]
    rw [hidx, cst odd (by simp [nodeConst]), cell_eq_cast tr T_NODE s odd, natCast_add, natCast_mul]
  have kiN1 : (kiE.eval tr T_NODE (s + o + d) pub + 1) = ((2 * d + cv tr T_NODE s odd + 1 : Nat) : Fp) := by
    rw [hki, show (1 : Fp) = ((1 : Nat) : Fp) from rfl, ← natCast_add]
  have kiN2 : (kiE.eval tr T_NODE (s + o + d) pub + 2) = ((2 * d + cv tr T_NODE s odd + 2 : Nat) : Fp) := by
    rw [hki, show (2 : Fp) = ((2 : Nat) : Fp) from rfl, ← natCast_add]
  have hfe : tr.cell T_NODE (s + o + d) fe = 1 ↔ d + 1 = L := hF.fe d hd
  have eA : eAN tr (s + o + d) =
      [n, 2 * d + cv tr T_NODE s odd, hiN tr (s + o + d), n, 2 * d + cv tr T_NODE s odd + 1, EK_KEY] := by
    unfold eAN
    rw [hnid, cv_of_eq (e1.trans hki) (by omega), cv_of_eq (e2.trans hhi) (by unfold P; omega),
      show cv tr T_NODE (s + o + d) aN = n by unfold cv; rw [e3]; exact hnid,
      cv_of_eq (e4.trans kiN1) (by omega), cv_of_eq eK (by unfold EK_KEY P; omega)]
  have eB1 : cv tr T_NODE (s + o + d) bI = 2 * d + cv tr T_NODE s odd + 1 := cv_of_eq (eBI.trans kiN1) (by omega)
  have eB2 : cv tr T_NODE (s + o + d) bS = loN tr (s + o + d) := cv_of_eq (eBS.trans hlo) (by unfold P; omega)
  have eB3 : cv tr T_NODE (s + o + d) bK = EK_KEY := cv_of_eq eBK (by unfold EK_KEY P; omega)
  unfold rowEdgeN
  rw [hA, hB, if_pos rfl, if_pos rfl, eA]
  simp only [List.singleton_append, List.cons.injEq, true_and, and_true]
  unfold eBN
  rw [hnid, eB1, eB2, eB3]
  rcases isBool hL hr (x := fe) (by simp [boolCols]) with hf | hf
  · have hnl : ¬ d + 1 = L := fun h => by rw [hfe.2 h] at hf; exact fp_one_ne_zero hf
    obtain ⟨f1, f2⟩ := e5 (by rw [hf]; grind)
    rw [if_neg (fun h => hnl h.1), if_neg (fun h => hnl h.1),
      show cv tr T_NODE (s + o + d) bN = n by unfold cv; rw [f1]; exact hnid,
      cv_of_eq (f2.trans kiN2) (by omega)]
  · have hl : d + 1 = L := hfe.1 hf
    rcases isBool hL (r := s) (by omega) (x := te) (by simp [boolCols]) with ht | ht
    · obtain ⟨f1, f2⟩ := e5 (by rw [cst te (by simp [nodeConst]), ht]; grind)
      rw [if_neg (fun h => by rw [cv_zero ht] at h; omega), if_neg (fun h => by rw [cv_zero ht] at h; omega),
        show cv tr T_NODE (s + o + d) bN = n by unfold cv; rw [f1]; exact hnid, cv_of_eq (f2.trans kiN2) (by omega)]
    · obtain ⟨f1, f2⟩ := e6 hf (by rw [cst te (by simp [nodeConst]), ht])
      rw [if_pos ⟨hl, cv_one ht⟩, if_pos ⟨hl, cv_one ht⟩,
        show cv tr T_NODE (s + o + d) bN = cv tr T_NODE s xtgt by unfold cv; rw [f1, cst xtgt (by simp [nodeConst])],
        show cv tr T_NODE (s + o + d) bJ = cv tr T_NODE s xtgJ by unfold cv; rw [f2, cst xtgJ (by simp [nodeConst])]]

/-- The value window: the `VAL` edge to the value record. -/
theorem vhEdge (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (ho : 0 < o)
    (sH : tr.cell T_NODE (s + o) sVH = 1) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (hh : cv tr T_NODE s tl = 1 → 1 ≤ cv tr T_NODE s hplen ∧ cv tr T_NODE s hplen < ℓ) :
    rowEdgeN tr pub (s + o) = if cv tr T_NODE s tv = 1 then
      [([n, if cv tr T_NODE s tl = 1 then 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd else 0, SYM_END,
        cv tr T_NODE s vid, 0, EK_VAL], cv tr T_NODE (s + o) mA)] else [] := by
  have hoℓ : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  have hP := hP_of hL hC
  obtain ⟨hr, ha, hnid⟩ := inRow hL hC hoℓ hn hnP
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 (by omega)).2 rfl
  have z := fun y (hy : y ∈ states) (hne : y ≠ sVH) => stOnly hL hr ha sH (by simp [states]) hy hne
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx hoℓ
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hB : tr.cell T_NODE (s + o) gB = 0 := by
    rw [GB, z sKEY (by simp [states]) (by decide), z sMEM (by simp [states]) (by decide)]; grind
  have hA : tr.cell T_NODE (s + o) gA = tr.cell T_NODE s tv := by
    rw [GA, z sKEY (by simp [states]) (by decide), z sHPF (by simp [states]) (by decide),
      z sCH (by simp [states]) (by decide), sH, hfs, cst tv (by simp [nodeConst])]; grind
  unfold rowEdgeN; rw [hB, hA]
  rcases isBool hL (r := s) (by omega) (x := tv) (by simp [boolCols]) with ht | ht
  · rw [ht, if_neg (show ¬ cv tr T_NODE s tv = 1 by rw [cv_zero ht]; omega)]; simp
  · rw [ht, if_pos (show cv tr T_NODE s tv = 1 from cv_one ht), if_pos rfl]
    have M := winMisc hL hr
    have hgD : tr.cell T_NODE (s + o) gD - tr.cell T_NODE (s + o) gP = 1 := by
      rw [M.2.1, hfs, sH, cst tv (by simp [nodeConst]), ht]
      have G := linkGates hL hr; simp only at G
      rw [G.1, hfs, z sCH (by simp [states]) (by decide)]; grind
    have E := (edgeFacts hL hr (pub := pub)).2.2.2.2 hgD
    simp only at E
    obtain ⟨e1, e2, e3, e4, eK⟩ := E
    have hI : cv tr T_NODE (s + o) aI =
        if cv tr T_NODE s tl = 1 then 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd else 0 := by
      rw [cst tl (by simp [nodeConst])] at e1
      have bo := cvb hL (r := s) (by omega) (x := odd) (by simp [boolCols])
      rcases isBool hL (r := s) (by omega) (x := tl) (by simp [boolCols]) with hl | hl
      · rw [if_neg (show ¬ cv tr T_NODE s tl = 1 by rw [cv_zero hl]; omega)]; unfold cv; rw [e1, hl, fp_zero_mul]
        exact Fp.toNat_zero
      · rw [if_pos (show cv tr T_NODE s tl = 1 from cv_one hl)]
        obtain ⟨h1, hhP⟩ := hh (cv_one hl)
        apply cv_of_eq _ (by omega)
        rw [e1, hl]
        simp only [sE, eval_add, eval_smul, eval_sub, eval_c, eval_k]
        rw [cst hplen (by simp [nodeConst]), cst odd (by simp [nodeConst]), cell_eq_cast tr T_NODE s hplen,
          cell_eq_cast tr T_NODE s odd, show cv tr T_NODE s hplen = (cv tr T_NODE s hplen - 1) + 1 by omega,
          natCast_add (cv tr T_NODE s hplen - 1) 1, natCast_add, natCast_mul]
        grind
    have hS : cv tr T_NODE (s + o) aS = SYM_END := by
      unfold cv; rw [e2]; exact toNat_of_eq rfl (by unfold SYM_END P; omega)
    have hN : cv tr T_NODE (s + o) aN = cv tr T_NODE s vid := by unfold cv; rw [e3, cst vid (by simp [nodeConst])]
    have hJ : cv tr T_NODE (s + o) aJ = 0 := by unfold cv; rw [e4]; exact Fp.toNat_zero
    have hK : cv tr T_NODE (s + o) aK = EK_VAL := cv_of_eq eK (by unfold EK_VAL P; omega)
    unfold eAN; rw [hnid, hI, hS, hN, hJ, hK]; simp

/-- A child window of a branch: the `DOWN` edge to the child's walk target. -/
theorem chEdge (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (ho : 0 < o)
    (sC : tr.cell T_NODE (s + o) sCH = 1) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (htl : tr.cell T_NODE s tl = 0) :
    rowEdgeN tr pub (s + o) = if cv tr T_NODE (s + o) rv = 1 ∧ cv tr T_NODE s te = 0 then
      [([n, 0, cv tr T_NODE (s + o) aS, cv tr T_NODE (s + o) cres, 0, EK_DOWN], cv tr T_NODE (s + o) mA)] else [] := by
  have hoℓ : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  obtain ⟨hr, ha, hnid⟩ := inRow hL hC hoℓ hn hnP
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 (by omega)).2 rfl
  have z := fun y (hy : y ∈ states) (hne : y ≠ sCH) => stOnly hL hr ha sC (by simp [states]) hy hne
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx hoℓ
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hB : tr.cell T_NODE (s + o) gB = 0 := by
    rw [GB, z sKEY (by simp [states]) (by decide), z sMEM (by simp [states]) (by decide)]; grind
  have GA' : tr.cell T_NODE (s + o) gA = tr.cell T_NODE (s + o) rv * (tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2) := by
    rw [GA, z sKEY (by simp [states]) (by decide), z sHPF (by simp [states]) (by decide),
      z sVH (by simp [states]) (by decide), sC, hfs, cst tb1 (by simp [nodeConst]), cst tb2 (by simp [nodeConst])]; grind
  have hr0 : s < tr.height T_NODE := by omega
  have T := typeSumNat hL hr0 (nodeStart hL hC).2
  rw [cv_zero htl] at T
  have hbr : cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 - cv tr T_NODE s te := by omega
  unfold rowEdgeN; rw [hB]
  rcases isBool hL hr0 (x := te) (by simp [boolCols]) with he | he
  · have hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1 := by
      rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add, hbr, cv_zero he]; rfl
    rw [hb, show tr.cell T_NODE (s + o) rv * 1 = tr.cell T_NODE (s + o) rv by grind] at GA'
    rw [GA']
    rcases isBool hL hr (x := rv) (by simp [boolCols]) with hv | hv
    · rw [hv, if_neg (show ¬ (cv tr T_NODE (s + o) rv = 1 ∧ cv tr T_NODE s te = 0) by rw [cv_zero hv]; omega)]; simp
    · rw [hv, if_pos (show cv tr T_NODE (s + o) rv = 1 ∧ cv tr T_NODE s te = 0 from ⟨cv_one hv, cv_zero he⟩), if_pos rfl]
      have hgP : tr.cell T_NODE (s + o) gP = 1 := by
        have G := linkGates hL hr; simp only at G; rw [G.1, hfs, sC, hv]; grind
      have E := (edgeFacts hL hr (pub := pub)).2.2.2.1 hgP (show tr.cell T_NODE (s + o) tb1 + tr.cell T_NODE (s + o) tb2 = 1 by
        rw [cst tb1 (by simp [nodeConst]), cst tb2 (by simp [nodeConst]), hb])
      simp only at E
      obtain ⟨e1, e2, e3, e4, eK⟩ := E
      have hI : cv tr T_NODE (s + o) aI = 0 := by unfold cv; rw [e1]; exact Fp.toNat_zero
      have hN : cv tr T_NODE (s + o) aN = cv tr T_NODE (s + o) cres := by unfold cv; rw [e3]
      have hJ : cv tr T_NODE (s + o) aJ = 0 := by unfold cv; rw [e4]; exact Fp.toNat_zero
      have hK : cv tr T_NODE (s + o) aK = EK_DOWN := by unfold cv; rw [eK]; rfl
      unfold eAN; rw [hnid, hI, hN, hJ, hK]; simp
  · have hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 0 := by
      rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add, hbr, cv_one he]; rfl
    rw [hb, show tr.cell T_NODE (s + o) rv * 0 = 0 by grind] at GA'
    rw [GA', if_neg (show ¬ (cv tr T_NODE (s + o) rv = 1 ∧ cv tr T_NODE s te = 0) by rw [cv_one he]; omega)]; simp

/-- The `MEM` field: a leaf's first `MEM` row provides the `LEND` marker at `(nid, s)`. -/
theorem memEdges (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 8) ∈ fl) (ho : 0 < o)
    (sM : tr.cell T_NODE (s + o) sMEM = 1) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (hh : cv tr T_NODE s tl = 1 → 1 ≤ cv tr T_NODE s hplen ∧ cv tr T_NODE s hplen < ℓ) :
    (List.range' (s + o) 8).flatMap (rowEdgeN tr pub) = if cv tr T_NODE s tl = 1 then
      [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, n,
        2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, EK_LEND], cv tr T_NODE (s + o) mB)] else [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hoℓ : o < ℓ := by have := (hC.fields.field _ hm).2; simp at this; omega
  have hP := hP_of hL hC
  rw [show (8 : Nat) = 1 + 7 from rfl, ← List.range'_append_1, List.range'_one, List.flatMap_append,
    List.flatMap_singleton]
  rw [flatMap_range'_nil _ _ _ (fun j hj => by
    have hr : s + o + 1 + j < tr.height T_NODE := by omega
    rw [show s + o + 1 + j = s + o + (1 + j) by omega] at hr ⊢
    have ha := hF.act (1 + j) (by omega)
    have hfs : tr.cell T_NODE (s + o + (1 + j)) fs = 0 :=
      bool01 hL hr (by simp [boolCols]) (fun h => by have := (hF.fs (1 + j) (by omega)).1 h; omega)
    have sM' : tr.cell T_NODE (s + o + (1 + j)) sMEM = 1 := by rw [hF.st _ (by omega) sMEM (by simp [states]), sM]
    exact quietEdge hL hr (stOnly hL hr ha sM' (by simp [states]) (by simp [states]) (by decide))
      (stOnly hL hr ha sM' (by simp [states]) (by simp [states]) (by decide)) (Or.inl hfs))]
  simp only [List.append_nil]
  obtain ⟨hr, ha, hnid⟩ := inRow hL hC hoℓ hn hnP
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 (by omega)).2 rfl
  have z := fun y (hy : y ∈ states) (hne : y ≠ sMEM) => stOnly hL hr ha sM (by simp [states]) hy hne
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx hoℓ
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hA : tr.cell T_NODE (s + o) gA = 0 := by
    rw [GA, z sKEY (by simp [states]) (by decide), z sHPF (by simp [states]) (by decide),
      z sCH (by simp [states]) (by decide), z sVH (by simp [states]) (by decide)]; grind
  have GB' : tr.cell T_NODE (s + o) gB = tr.cell T_NODE s tl := by
    rw [GB, z sKEY (by simp [states]) (by decide), sM, hfs, cst tl (by simp [nodeConst])]; grind
  unfold rowEdgeN; rw [hA, GB']
  rcases isBool hL (r := s) (by omega) (x := tl) (by simp [boolCols]) with hl | hl
  · rw [if_neg (show ¬ cv tr T_NODE s tl = 1 by rw [cv_zero hl]; decide), hl]; simp
  · rw [if_pos (cv_one hl), hl, if_pos rfl]
    have hgL : tr.cell T_NODE (s + o) gL = 1 := by
      have G := linkGates hL hr; simp only at G; rw [G.2.2.1, cst tl (by simp [nodeConst]), hl, sM, hfs]; grind
    obtain ⟨l1, l2, l3, l4, l5⟩ := (edgeFacts hL hr (pub := pub)).2.1 hgL
    simp only at l1 l2 l3 l4 l5
    obtain ⟨h1, hhP⟩ := hh (cv_one hl)
    have bo := cvb hL (r := s) (by omega) (x := odd) (by simp [boolCols])
    have hsE : sE.eval tr T_NODE (s + o) pub = ((2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd : Nat) : Fp) := by
      simp only [sE, eval_add, eval_smul, eval_sub, eval_c, eval_k]
      rw [cst hplen (by simp [nodeConst]), cst odd (by simp [nodeConst]), cell_eq_cast tr T_NODE s hplen,
        cell_eq_cast tr T_NODE s odd, show cv tr T_NODE s hplen = (cv tr T_NODE s hplen - 1) + 1 by omega,
        natCast_add (cv tr T_NODE s hplen - 1) 1, natCast_add, natCast_mul]
      grind
    unfold eBN
    rw [hnid, cv_of_eq (l1.trans hsE) (by omega), cv_of_eq l2 (by unfold SYM_END P; omega),
      show cv tr T_NODE (s + o) bN = n by unfold cv; rw [l3]; exact hnid, cv_of_eq (l4.trans hsE) (by omega),
      cv_of_eq l5 (by unfold EK_LEND P; omega)]
    simp

end ZkFormal.NearV3.NodeProof3
