import StateM5a.WalkEnd

/-!
# StateM5a.BrOsl — the `MATQ` / `MATR` answers of a split's new branch (`BR.oSL`) from `Holds`

A `BR.oSL` row at `(w, d)` received its `SPQ(w, d, …)` from the walk's split row (`WalkEnd.osl_spq`;
a split row does not descend, so by `WalkEnd.sn_term_unique` it is **the** non-descending `SN` row
of walk `w`).  Hence every `oSL` row at `(w, d)` received the same `SPQ` message
(`osl_same`): the request fields of a split's new branch are pinned by its walk position.

The split row's two keys differ at the split nibble (`split_kid_ne`: the walk key `kid` has `y`
there, the old key `kid2` the row's nibble `k_jm ≠ y`), so the two `MATQ` requests of an `oSL` row
(`gmat`: the new leaf under `kid`; `oSL·xl`: the re-keyed old leaf under `xk = kid2`) have
different keys.

* **`osl_mat`** / **`osl_mat2`**: the `MATR` answer an `oSL` row receives for each request is its
  `MatRel` (responders `SN.oLM`, `SnMatOK`).  The responder's request came from a `BR` row at
  `(w, d)`: an active row is excluded by `OslApart` (`WalkEnd.oslApart`); another `oSL` row there
  has the same `SPQ`, so its request (both are functions of the `SPQ` fields and the row's
  `kid`/`xk`) is this row's, and the cross case would need `xk = kid`.
-/

namespace StateM5a.BrOsl

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups

local notation "P" => 2013265921

set_option maxRecDepth 100000

def brMatR2 : List Expr :=
  [Br.c "w", Br.c "d" + 1, Br.c "xk", Br.c "nh2f"] ++ pack2 (fun b => Br.c "nh2" b) ++
    (List.range 4).map fun k => Br.c "nm2" k

theorem br_matr2_r : rcv B_MATR (Br.c "oSL" * Br.c "xl") brMatR2 ∈ Br.interactions := memD_mem (by decide)

theorem sn_mem_gxn : Sn.gX * (1 - Sn.c "mN") ∈ Sn.constraints := by unfold Sn.constraints; simp

/-! ## The flags of a split's new branch -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

open StateM5a.RowBr in
set_option maxHeartbeats 4000000 in
/-- **An `oSL` row**: active, no walk op, a new node. -/
theorem osl_flags (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (h1 : ev tr t r pub (Br.c "oSL") = 1) :
    ev tr t r pub (Br.c "act") = 1 ∧ ev tr t r pub (Br.c "gnew") = 1 ∧ ev tr t r pub (Br.c "gdn") = 0 ∧
    ev tr t r pub (Br.c "mF") = 0 ∧ ev tr t r pub (Br.c "mU") = 0 ∧ ev tr t r pub (Br.c "mD") = 0 ∧
    ev tr t r pub (Br.c "oFD") = 0 ∧ ev tr t r pub (Br.c "oFA") = 0 ∧ ev tr t r pub (Br.c "oFV") = 0 ∧
    ev tr t r pub (Br.c "oUD") = 0 ∧ ev tr t r pub (Br.c "oUN") = 0 ∧ ev tr t r pub (Br.c "oUV") = 0 ∧
    ev tr t r pub (Br.c "oDH") = 0 ∧ ev tr t r pub (Br.c "oDL") = 0 ∧ ev tr t r pub (Br.c "oDN") = 0 ∧
    ev tr t r pub (Br.c "oD1") = 0 ∧ ev tr t r pub (Br.c "oDA") = 0 ∧ ev tr t r pub (Br.c "oDS") = 0 ∧
    ev tr t r pub (Br.c "oDV") = 0 ∧ ev tr t r pub (Br.c "oDZ") = 0 ∧ ev tr t r pub Br.gold = 0 := by
  have hb : ∀ s ∈ flagNames, ev tr t r pub (Br.c s) ≤ 1 := fun s hs => bool_le (hold rfl hc (br_bool' s hs))
  have b1 := hb "act" (by simp [flagNames]); have b2 := hb "mF" (by simp [flagNames]); have b3 := hb "mU" (by simp [flagNames])
  have b4 := hb "mD" (by simp [flagNames]); have b5 := hb "gdn" (by simp [flagNames]); have b6 := hb "gnew" (by simp [flagNames])
  have b7 := hb "oFD" (by simp [flagNames]); have b8 := hb "oFA" (by simp [flagNames]); have b9 := hb "oUD" (by simp [flagNames])
  have b10 := hb "oUN" (by simp [flagNames]); have b11 := hb "oDH" (by simp [flagNames]); have b12 := hb "oDL" (by simp [flagNames])
  have b13 := hb "oDN" (by simp [flagNames]); have b14 := hb "oD1" (by simp [flagNames]); have b15 := hb "oFV" (by simp [flagNames])
  have b16 := hb "oDA" (by simp [flagNames]); have b17 := hb "oDS" (by simp [flagNames])
  have b19 := hb "oUV" (by simp [flagNames]); have b20 := hb "oDV" (by simp [flagNames]); have b21 := hb "oDZ" (by simp [flagNames])
  have e1 := eq_of_sub (hold rfl hc FieldWalk.br_mem_act)
  have e2 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mF)
  have e3 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mU)
  have e4 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mD)
  have e5 := eq_of_sub (hold rfl hc FieldWalk.br_mem_gdn)
  have e6 := eq_of_sub (hold rfl hc br_mem_gnew)
  rw [show (Br.c "mF" + Br.c "mU" + Br.c "mD" + Br.c "oSL" : Expr) = ([Br.c "mU", Br.c "mD", Br.c "oSL"]).foldl (· + ·) (Br.c "mF") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl <;> omega)] at e1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e1
  rw [show (Br.c "oFD" + Br.c "oFA" + Br.c "oFV" : Expr) = ([Br.c "oFA", Br.c "oFV"]).foldl (· + ·) (Br.c "oFD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl <;> assumption)] at e2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e2
  rw [show (Br.c "oUD" + Br.c "oUN" + Br.c "oUV" : Expr) = ([Br.c "oUN", Br.c "oUV"]).foldl (· + ·) (Br.c "oUD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl <;> assumption)] at e3
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e3
  rw [show (Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDA" + Br.c "oDS" + Br.c "oDV" + Br.c "oDZ" : Expr) = ([Br.c "oDL", Br.c "oDN", Br.c "oD1", Br.c "oDA", Br.c "oDS", Br.c "oDV", Br.c "oDZ"]).foldl (· + ·) (Br.c "oDH") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)] at e4
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e4
  rw [show (Br.c "oFD" + Br.c "oUD" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDS" : Expr) = ([Br.c "oUD", Br.c "oDH", Br.c "oDL", Br.c "oDN", Br.c "oD1", Br.c "oDS"]).foldl (· + ·) (Br.c "oFD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)] at e5
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e5
  rw [show (Br.c "oUD" + Br.c "oUN" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oSL" + Br.c "oUV" + Br.c "oDV" : Expr) = ([Br.c "oUN", Br.c "oDH", Br.c "oDL", Br.c "oDN", Br.c "oSL", Br.c "oUV", Br.c "oDV"]).foldl (· + ·) (Br.c "oUD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)] at e6
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e6
  have hgold : ev tr t r pub Br.gold = 0 := by
    unfold Br.gold; rw [ev_sub, h1]; rw [show ev tr t r pub (Br.c "act") = 1 by omega]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, hgold⟩

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- On a split row the mismatch is another walk-key nibble (`mN = 1`), at a key position of the
row (`ajm = 1`). -/
theorem split_mN {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (hX : ev tr 3 s pub Sn.gX = 1) :
    ev tr 3 s pub (Sn.c "mN") = 1 ∧ ev tr 3 s pub (Sn.c "ajm") = 1 := by
  have h1 := FieldWsb.wsb_gate hX (FieldRows2.sn_hold hc sn_mem_gxn)
  rw [ev_sub, ev_one] at h1
  have bN := bool_le (FieldRows2.sn_hold hc (RowSnM.sn_bool' "mN" (by simp)))
  have hN : ev tr 3 s pub (Sn.c "mN") = 1 := by
    have := ev_lt (tr := tr) (t := 3) (r := s) (pub := pub) (Sn.c "mN"); omega
  refine ⟨hN, ?_⟩
  have bK := bool_le (FieldRows2.sn_hold hc (RowSnM.sn_bool' "mK" (by simp)))
  have m1 := eq_of_sub (FieldRows2.sn_hold hc RowSnM.sn_mem_m1)
  obtain ⟨-, -, hA, -⟩ := split_flags hc hX
  have bL := bool_le (FieldRows2.sn_hold hc (RowSnM.sn_bool' "mL" (by simp)))
  rw [ev_hadd, ev_hadd, hA, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at m1
  have g : ev tr 3 s pub (Sn.c "mN" + Sn.c "mK") = 1 := by rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega
  have h0 := FieldWsb.wsb_gate g (FieldRows2.sn_hold hc RowSnM.sn_mem_m2)
  rw [ev_sub, ev_one] at h0
  have := ev_lt (tr := tr) (t := 3) (r := s) (pub := pub) (Sn.c "ajm")
  omega

/-- **The split row's two keys differ** at the split nibble `d + jm`: the walk key (`kid`) has `y`
there, the old key (`kid2`) the row's nibble `k_jm ≠ y`. -/
theorem split_nibs (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {s : Nat} (hs : s < tr.height 3)
    (hX : ev tr 3 s pub Sn.gX = 1) :
    (keyOf tr (ev tr 3 s pub (Sn.c "kid")))[ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm")]? =
      some (ev tr 3 s pub (Sn.c "y")) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid2")))[ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm")]? =
      some (ev tr 3 s pub (Sn.c "kj")) ∧
    ev tr 3 s pub (Sn.c "y") ≠ ev tr 3 s pub (Sn.c "kj") := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hg, -, hA, -⟩ := split_flags hc hX
  obtain ⟨hN, hajm⟩ := split_mN hc hX
  have hdep := SnDepthAll.sn_depth_all hH hxN hxL s hs (ev_one_eval hg)
  obtain ⟨hj64, -, hkj, haj⟩ := RowSnM.sn_jm hc hA
  have hne := FieldRows.sn_mismatch_ne hc hN
  have bL := bool_le (FieldRows2.sn_hold hc (RowSnM.sn_bool' "mL" (by simp)))
  have h1 := (sn_nib_mis hH hxN hs (ev_one_eval (show ev tr 3 s pub (Sn.c "mN" + Sn.c "mL") = 1 by
    have m1 := eq_of_sub (FieldRows2.sn_hold hc RowSnM.sn_mem_m1)
    have bK := bool_le (FieldRows2.sn_hold hc (RowSnM.sn_bool' "mK" (by simp)))
    rw [ev_hadd, ev_hadd, hA, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at m1
    rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega))).1
  rw [ev_hadd, Nat.mod_eq_of_lt (by omega)] at h1
  have hg2 : ev tr 3 s pub (Sn.c "g2") = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := sn_flags' hc hg
    obtain ⟨-, -, -, hX'⟩ := split_flags hc hX
    rw [h]
    snfacts hc hg
    omega
  have ha : ev tr 3 s pub (Sn.a (ev tr 3 s pub (Sn.c "jm"))) = 1 := by
    rw [FieldRows2.sn_a_lt _ hj64, ← haj, hajm]
  have h2 := (sn_nib2 hH hxN _ hj64 hs (ev_one_eval (by rw [RowSnN.ev_gm hg2]; exact ha))).1
  rw [RowSnF.ev_dK _ (by omega), FieldRows2.sn_k_lt _ hj64, ← hkj] at h2
  exact ⟨h1, h2, hne⟩

theorem split_kid_ne (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {s : Nat} (hs : s < tr.height 3)
    (hX : ev tr 3 s pub Sn.gX = 1) : ev tr 3 s pub (Sn.c "kid") ≠ ev tr 3 s pub (Sn.c "kid2") := by
  obtain ⟨h1, h2, hne⟩ := split_nibs hH hxN hxL hs hX
  intro e
  rw [e, h2] at h1
  exact hne (Option.some.inj h1).symm

section
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
include hH hD hx hxN hxL hxK hxR hxQ

/-- **Two `oSL` rows of one walk received the same `SPQ`** (the walk's unique split row). -/
theorem osl_same {r r' : Nat} (hr : r < tr.height 2) (hr' : r' < tr.height 2)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) (h1' : ev tr 2 r' pub (Br.c "oSL") = 1)
    (ew : E tr 2 r pub (Br.c "w") = E tr 2 r' pub (Br.c "w")) :
    brSpQ.map (E tr 2 r pub) = brSpQ.map (E tr 2 r' pub) := by
  obtain ⟨s, hs, hX, he⟩ := osl_spq hH hxQ hr h1
  obtain ⟨s', hs', hX', he'⟩ := osl_spq hH hxQ hr' h1'
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hc' := tbl_sn D extra nb np hH s' (List.mem_range.2 hs')
  obtain ⟨hg, h0, -⟩ := split_flags hc hX
  obtain ⟨hg', h0', -⟩ := split_flags hc' hX'
  have w1 : E tr 3 s pub (Sn.c "w") = E tr 2 r pub (Br.c "w") := by
    have := congrArg (fun l => l.getD 0 0) he; simpa [snSpQ, brSpQ] using this
  have w2 : E tr 3 s' pub (Sn.c "w") = E tr 2 r' pub (Br.c "w") := by
    have := congrArg (fun l => l.getD 0 0) he'; simpa [snSpQ, brSpQ] using this
  obtain rfl := sn_term_unique hH hD hx hxN hxK hxR hs hs' (ev_one_eval hg) (ev_one_eval hg') h0 h0'
    (toNat_eq (w1.trans (ew.trans w2.symm)))
  rw [← he, ← he']

end

end

/-! ## Field equalities from equal messages -/

section
variable {tr : Trace Fp} {pub : List Fp}

theorem at_eq {l : List Expr} {t t' r r' : Nat} (he : l.map (E tr t r pub) = l.map (E tr t' r' pub)) {k : Nat}
    {e : Expr} (h : l[k]? = some e) : E tr t r pub e = E tr t' r' pub e := by
  have := congrArg (fun x => x[k]?) he
  simp only [List.getElem?_map, h, Option.map_some, Option.some.injEq] at this
  exact this

theorem at_eq2 {l l' : List Expr} {t t' r r' : Nat} (he : l.map (E tr t r pub) = l'.map (E tr t' r' pub)) {k : Nat}
    {e e' : Expr} (h : l[k]? = some e) (h' : l'[k]? = some e') : E tr t r pub e = E tr t' r' pub e' := by
  have := congrArg (fun x => x[k]?) he
  simp only [List.getElem?_map, h, h', Option.map_some, Option.some.injEq] at this
  exact this

theorem brSpQ_dvh : ∀ i : Nat, i < 16 → brSpQ[28 + i]? = some (Br.c "dvh" i) := by
  decide
theorem brSpQ_h : ∀ i : Nat, i < 16 → brSpQ[5 + i]? = some (Br.c "xl" * Br.c "lvh2" i +
    (1 - Br.c "xl") * (K 256 * Br.c "nh2" (2 * i) + Br.c "nh2" (2 * i + 1))) := by
  decide
theorem brSpQ_nm : ∀ k : Nat, k < 4 → brSpQ[23 + k]? = some ((1 - Br.c "xl") * Br.c "nm2" k) := by
  decide
theorem brMatQ_h : ∀ i : Nat, i < 16 → brMatQ[5 + i]? = some (Br.c "lvh" i) := by
  decide
theorem brMatQ2_h : ∀ i : Nat, i < 16 → brMatQ2[5 + i]? = some (Br.c "lvh2" i) := by
  decide
theorem snMatQ_h : ∀ i : Nat, i < 16 → snMatQ[5 + i]? = some (Sn.c "dvh" i) := by
  decide

/-- A gate `g·(a − b) = 0` with `g = 1`, in the field. -/
theorem gate_E {t r : Nat} {g a b : Expr} (h : ev tr t r pub (g * (a - b)) = 0) (hg : ev tr t r pub g = 1) :
    E tr t r pub a = E tr t r pub b := Fp.ext (FieldVer.eq_of_gate h hg)

theorem e_add1 {t r t' r' : Nat} {a b : Expr} (h : E tr t r pub a = E tr t' r' pub b) :
    E tr t r pub (a + 1) = E tr t' r' pub (b + 1) := by
  simp only [E, eval_succ] at h ⊢; rw [h]; rfl

theorem e_gate1 {t r : Nat} {g a : Expr} (hg : ev tr t r pub g = 1) : E tr t r pub (g * a) = E tr t r pub a := by
  have := ev_one_eval hg
  simp only [E, eval_mul, this]; grind

theorem e_gate1' {t r : Nat} {g a b : Expr} (hg : ev tr t r pub g = 1) :
    E tr t r pub (g * a + (1 - g) * b) = E tr t r pub a := by
  have := ev_one_eval hg
  simp only [E, eval_mul, eval_add, eval_sub, eval_lit, this]; grind

/-- `st2 = d + 1` on an `oUN` / `oSL` row, in the field. -/
theorem st2_E {r : Nat} (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (g1 : ev tr 2 r pub (Br.c "oUN" + Br.c "oSL") = 1) : E tr 2 r pub (Br.c "st2") = E tr 2 r pub (Br.c "d" + 1) := by
  have e := fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc RowBrUN.br_mem_uns) g1)
  simp only [E, eval_mul, eval_sub, eval_add, eval_lit] at e ⊢; grind

end

/-! ## The `MATR` answers of an `oSL` row -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
  (hxMQ : ∀ T ∈ extra, sendsOn T.interactions B_MATQ = false)
  (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ

/-- The `MATQ` an `SN.oLM` row received for a request at `(w, d + 1)` of an `oSL` row `r`: from an
`oSL` row `r'` at `(w, d)` with the same `SPQ` as `r` (an active row there is excluded by
`OslApart`), by its new-leaf request (`gmat`) or its re-keyed-leaf request (`oSL·xl`). -/
theorem osl_matq_src {r s : Nat} (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oSL") = 1)
    (hs : s < tr.height 3) (hlm : (Sn.c "oLM").eval tr 3 s pub = 1)
    (ew : E tr 3 s pub (Sn.c "w") = E tr 2 r pub (Br.c "w"))
    (ed : E tr 3 s pub (Sn.c "d") = E tr 2 r pub (Br.c "d" + 1)) :
    ∃ r', r' < tr.height 2 ∧ ev tr 2 r' pub (Br.c "oSL") = 1 ∧
      brSpQ.map (E tr 2 r pub) = brSpQ.map (E tr 2 r' pub) ∧
      ((snMatQ.map (E tr 3 s pub) = brMatQ.map (E tr 2 r' pub)) ∨
       (ev tr 2 r' pub (Br.c "xl") = 1 ∧ snMatQ.map (E tr 3 s pub) = brMatQ2.map (E tr 2 r' pub))) := by
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm2 := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_matq_r) hs rfl hlm
  obtain ⟨r', hr', i', hi', hb', hss', hp', he2⟩ :=
    sender_m5a B_MATQ 2 (by simp [m5aAir]) (matq_only D) hxMQ (recv_sent hH hm2)
  change i' ∈ Br.interactions at hi'
  have hc' := tbl_br D extra nb np hH r' (List.mem_range.2 hr')
  have hmem : i' ∈ Br.interactions.filter (fun i => decide (i.bus = B_MATQ ∧ i.send = true)) :=
    List.mem_filter.2 ⟨hi', by simp [hb', hss']⟩
  rw [br_matq_s] at hmem
  have bS := br_flag_le hc' "oSL" (by simp)
  have pos : ∀ (l : List Expr), snMatQ.map (E tr 3 s pub) = l.map (E tr 2 r' pub) →
      l[0]? = some (Br.c "w") → l[1]? = some (Br.c "d" + 1) →
      E tr 2 r pub (Br.c "w") = E tr 2 r' pub (Br.c "w") ∧ E tr 2 r pub (Br.c "d") = E tr 2 r' pub (Br.c "d") := by
    intro l he h0 h1'
    have a := at_eq2 he (k := 0) rfl h0
    have b := at_eq2 he (k := 1) rfl h1'
    refine ⟨ew.symm.trans a, ?_⟩
    have := ed.symm.trans b
    simp only [E, eval_succ] at this
    exact fp_cancel this
  have hsl : ev tr 2 r' pub (Br.c "oSL") = 1 → E tr 2 r pub (Br.c "w") = E tr 2 r' pub (Br.c "w") →
      brSpQ.map (E tr 2 r pub) = brSpQ.map (E tr 2 r' pub) := fun h ew' =>
    osl_same hH hD hx hxN hxL hxK hxR hxQ hr hr' h1 h ew'
  rcases List.mem_cons.1 hmem with rfl | hmem
  · have hgm' := eval_one_ev (multNat_one_bit rfl hp')
    obtain ⟨ew', ed'⟩ := pos brMatQ he2 rfl rfl
    have bL := br_flag_le hc' "oDL" (by simp); have bU := br_flag_le hc' "oUN" (by simp)
    rcases (by omega : ev tr 2 r' pub (Br.c "oSL") = 1 ∨ ev tr 2 r' pub (Br.c "oSL") = 0) with hs1 | hsq
    · exact ⟨r', hr', hs1, hsl hs1 ew', Or.inl he2⟩
    · exfalso
      have hg' : ev tr 2 r' pub Br.gold = 1 := by
        rw [RowBr.ev_add_lt (by rw [RowBr.ev_add_lt (by omega)]; omega), RowBr.ev_add_lt (by omega)] at hgm'
        rcases (by omega : ev tr 2 r' pub (Br.c "oDL") = 1 ∨ ev tr 2 r' pub (Br.c "oUN") = 1) with h | h
        · exact FieldWalk.br_gdn_gold hc' (br_oDL_gdn hc' h)
        · exact br_oUN_gold hc' h
      exact oslApart hH hD hx hxN hxL hxK hxR hxQ r' r hr' hr hg' h1 ew'.symm ed'.symm
  · rw [List.mem_singleton] at hmem
    subst hmem
    obtain ⟨ew', -⟩ := pos brMatQ2 he2 rfl rfl
    have hx1 := eval_one_ev (multNat_one_bit rfl hp')
    rw [ev_hmul] at hx1
    have hs1 : ev tr 2 r' pub (Br.c "oSL") = 1 := by
      rcases (by omega : ev tr 2 r' pub (Br.c "oSL") = 1 ∨ ev tr 2 r' pub (Br.c "oSL") = 0) with h | h
      · exact h
      · rw [h] at hx1; simp at hx1
    rw [hs1, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at hx1
    exact ⟨r', hr', hs1, hsl hs1 ew', Or.inr ⟨hx1, he2⟩⟩

include hxM

set_option maxHeartbeats 8000000 in
/-- **The new-leaf `MATR` answer of an `oSL` row** is its request's `MatRel`. -/
theorem osl_mat {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub) {r : Nat} (hr : r < tr.height 2)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) :
    MatRel σ (keyOf tr) (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub))) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, hUN, -, -, hDL, -⟩ := osl_flags hc h1
  have hgm : ev tr 2 r pub (Br.c "oDL" + Br.c "oUN" + Br.c "oSL") = 1 := by
    rw [RowBr.ev_add_lt (by rw [RowBr.ev_add_lt (by omega)]; omega), RowBr.ev_add_lt (by omega)]; omega
  have g1 : ev tr 2 r pub (Br.c "oUN" + Br.c "oSL") = 1 := by rw [RowBr.ev_add_lt (by omega)]; omega
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm1 := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr_r) hr rfl (ev_one_eval hgm)
  obtain ⟨s, hs, i, hi, hb, hss, hp, he1⟩ :=
    sender_m5a B_MATR 3 (by simp [m5aAir]) (matr_only D) hxM (recv_sent hH hm1)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_matr_s hi hb hss
  have hlm := multNat_one_bit (g := Sn.c "oLM") rfl hp
  have he1' : brMatR.map (E tr 2 r pub) = snMatR.map (E tr 3 s pub) := he1
  have ew : E tr 3 s pub (Sn.c "w") = E tr 2 r pub (Br.c "w") := (at_eq2 he1' (k := 0) rfl rfl).symm
  have ed : E tr 3 s pub (Sn.c "d") = E tr 2 r pub (Br.c "d" + 1) := (at_eq2 he1' (k := 1) rfl rfl).symm
  have ek : E tr 2 r pub (Br.c "kid2") = E tr 3 s pub (Sn.c "kid") := at_eq2 he1' (k := 2) rfl rfl
  obtain ⟨r', hr', hs1', hq, hcase⟩ := osl_matq_src hH hD hx hxN hxL hxK hxR hxQ hxMQ hr h1 hs hlm ew ed
  obtain ⟨sq, hsq, hX0, hq0⟩ := osl_spq hH hxQ hr h1
  have hne := split_kid_ne hH hxN hxL hsq hX0
  have k0 : E tr 3 sq pub (Sn.c "kid") = E tr 2 r pub (Br.c "kid") := at_eq2 hq0 (k := 2) rfl rfl
  have x0 : E tr 3 sq pub (Sn.c "kid2") = E tr 2 r pub (Br.c "xk") := at_eq2 hq0 (k := 3) rfl rfl
  have hc' := tbl_br D extra nb np hH r' (List.mem_range.2 hr')
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hUN', -⟩ := osl_flags hc' hs1'
  have g1' : ev tr 2 r' pub (Br.c "oUN" + Br.c "oSL") = 1 := by rw [RowBr.ev_add_lt (by omega)]; omega
  have kk : E tr 2 r pub (Br.c "kid2") = E tr 2 r pub (Br.c "kid") :=
    gate_E (FieldRows.hold rfl hc RowBrUN.br_mem_unk) g1
  have kk' : E tr 2 r' pub (Br.c "kid2") = E tr 2 r' pub (Br.c "kid") :=
    gate_E (FieldRows.hold rfl hc' RowBrUN.br_mem_unk) g1'
  have qk : E tr 2 r pub (Br.c "kid") = E tr 2 r' pub (Br.c "kid") := at_eq hq (k := 2) rfl
  have qx : E tr 2 r pub (Br.c "xk") = E tr 2 r' pub (Br.c "xk") := at_eq hq (k := 3) rfl
  rcases hcase with he2 | ⟨-, he2⟩
  · have key := hS s hs (eval_one_ev hlm)
    have a3 : E tr 3 s pub (Sn.c "d") = E tr 2 r' pub (Br.c "st2") := at_eq2 he2 (k := 3) rfl rfl
    have a4 : E tr 3 s pub (Sn.c "dvlen") = E tr 2 r' pub (Br.c "lvlen") := at_eq2 he2 (k := 4) rfl rfl
    have st : E tr 2 r pub (Br.c "st2") = E tr 2 r' pub (Br.c "st2") := by
      rw [st2_E hc g1, st2_E hc' g1']; exact e_add1 (at_eq hq (k := 1) rfl)
    have lv : E tr 2 r pub (Br.c "lvlen") = E tr 2 r' pub (Br.c "lvlen") := by
      rw [gate_E (FieldRows.hold rfl hc RowBrUN.br_mem_unl) g1,
        gate_E (FieldRows.hold rfl hc' RowBrUN.br_mem_unl) g1']
      exact at_eq hq (k := 27) rfl
    have q1 : ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub) =
        ((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub) := by
      simp only [List.map_map]
      apply List.map_congr_left; intro i hi
      have hi' := List.mem_range.1 hi
      simp only [Function.comp]
      rw [at_eq2 he2 (snMatQ_h i hi') (brMatQ_h i hi'),
        gate_E (FieldRows.hold rfl hc' (RowBrUN.br_mem_unh i hi')) g1',
        gate_E (FieldRows.hold rfl hc (RowBrUN.br_mem_unh i hi')) g1]
      exact (at_eq hq (brSpQ_dvh i hi')).symm
    simp only [rcv, snd, Interaction.msgVal, brMatR, snMatR, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at he1
    obtain ⟨-, -, -, en1, eh1⟩ := he1
    obtain ⟨b1, b2⟩ := List.append_inj eh1 (by simp [pack2])
    rw [toNat_eq ek.symm, toNat_eq (a3.trans st.symm), toNat_eq (a4.trans lv.symm), q1,
      show E tr 3 s pub (Sn.c "nref") = E tr 2 r pub (Br.c "nhf") from en1.symm,
      show List.map (E tr 3 s pub) (pack2 fun b => Sn.c "hn" b) = List.map (E tr 2 r pub) (pack2 fun b => Br.c "nh" b)
        from b1.symm,
      show List.map (E tr 3 s pub) Sn.NM = List.map (E tr 2 r pub) ((List.range 4).map fun k => Br.c "nm" k)
        from b2.symm] at key
    exact key
  · exfalso
    have a2 : E tr 3 s pub (Sn.c "kid") = E tr 2 r' pub (Br.c "xk") := at_eq2 he2 (k := 2) rfl rfl
    apply hne
    apply toNat_eq
    show E tr 3 sq pub (Sn.c "kid") = E tr 3 sq pub (Sn.c "kid2")
    rw [k0, x0, ← kk, ek, a2, ← qx]

set_option maxHeartbeats 8000000 in
/-- **The re-keyed-leaf `MATR` answer of an `oSL` row** (`xl = 1`) is its request's `MatRel`. -/
theorem osl_mat2 {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub) {r : Nat} (hr : r < tr.height 2)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) (hxl : ev tr 2 r pub (Br.c "xl") = 1) :
    MatRel σ (keyOf tr) (ev tr 2 r pub (Br.c "xk")) (ev tr 2 r pub (Br.c "d" + 1)) (ev tr 2 r pub (Br.c "lvlen2"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh2" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nh2f")) ((pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm2" k).map (E tr 2 r pub))) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, hUN, -⟩ := osl_flags hc h1
  have g1 : ev tr 2 r pub (Br.c "oUN" + Br.c "oSL") = 1 := by rw [RowBr.ev_add_lt (by omega)]; omega
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm1 := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr2_r) hr rfl
    (by rw [eval_mul, ev_one_eval h1, ev_one_eval hxl]; grind)
  obtain ⟨s, hs, i, hi, hb, hss, hp, he1⟩ :=
    sender_m5a B_MATR 3 (by simp [m5aAir]) (matr_only D) hxM (recv_sent hH hm1)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_matr_s hi hb hss
  have hlm := multNat_one_bit (g := Sn.c "oLM") rfl hp
  have he1' : brMatR2.map (E tr 2 r pub) = snMatR.map (E tr 3 s pub) := he1
  have ew : E tr 3 s pub (Sn.c "w") = E tr 2 r pub (Br.c "w") := (at_eq2 he1' (k := 0) rfl rfl).symm
  have ed : E tr 3 s pub (Sn.c "d") = E tr 2 r pub (Br.c "d" + 1) := (at_eq2 he1' (k := 1) rfl rfl).symm
  have ek : E tr 2 r pub (Br.c "xk") = E tr 3 s pub (Sn.c "kid") := at_eq2 he1' (k := 2) rfl rfl
  obtain ⟨r', hr', hs1', hq, hcase⟩ := osl_matq_src hH hD hx hxN hxL hxK hxR hxQ hxMQ hr h1 hs hlm ew ed
  obtain ⟨sq, hsq, hX0, hq0⟩ := osl_spq hH hxQ hr h1
  have hne := split_kid_ne hH hxN hxL hsq hX0
  have k0 : E tr 3 sq pub (Sn.c "kid") = E tr 2 r pub (Br.c "kid") := at_eq2 hq0 (k := 2) rfl rfl
  have x0 : E tr 3 sq pub (Sn.c "kid2") = E tr 2 r pub (Br.c "xk") := at_eq2 hq0 (k := 3) rfl rfl
  have hc' := tbl_br D extra nb np hH r' (List.mem_range.2 hr')
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hUN', -⟩ := osl_flags hc' hs1'
  have g1' : ev tr 2 r' pub (Br.c "oUN" + Br.c "oSL") = 1 := by rw [RowBr.ev_add_lt (by omega)]; omega
  have kk' : E tr 2 r' pub (Br.c "kid2") = E tr 2 r' pub (Br.c "kid") :=
    gate_E (FieldRows.hold rfl hc' RowBrUN.br_mem_unk) g1'
  have qk : E tr 2 r pub (Br.c "kid") = E tr 2 r' pub (Br.c "kid") := at_eq hq (k := 2) rfl
  have qx : E tr 2 r pub (Br.c "xk") = E tr 2 r' pub (Br.c "xk") := at_eq hq (k := 3) rfl
  rcases hcase with he2 | ⟨hxl', he2⟩
  · exfalso
    have a2 : E tr 3 s pub (Sn.c "kid") = E tr 2 r' pub (Br.c "kid2") := at_eq2 he2 (k := 2) rfl rfl
    apply hne
    apply toNat_eq
    show E tr 3 sq pub (Sn.c "kid") = E tr 3 sq pub (Sn.c "kid2")
    rw [k0, x0, ek, a2, kk', ← qk]
  · have key := hS s hs (eval_one_ev hlm)
    have a4 : E tr 3 s pub (Sn.c "dvlen") = E tr 2 r' pub (Br.c "lvlen2") := at_eq2 he2 (k := 4) rfl rfl
    have lv : E tr 2 r pub (Br.c "lvlen2") = E tr 2 r' pub (Br.c "lvlen2") := by
      rw [← e_gate1 hxl, ← e_gate1 hxl']
      exact at_eq hq (k := 22) rfl
    have q1 : ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub) =
        ((List.range 16).map fun i => Br.c "lvh2" i).map (E tr 2 r pub) := by
      simp only [List.map_map]
      apply List.map_congr_left; intro i hi
      have hi' := List.mem_range.1 hi
      simp only [Function.comp]
      rw [at_eq2 he2 (snMatQ_h i hi') (brMatQ2_h i hi'), ← e_gate1' (b := K 256 * Br.c "nh2" (2 * i) +
        Br.c "nh2" (2 * i + 1)) hxl', ← e_gate1' (b := K 256 * Br.c "nh2" (2 * i) + Br.c "nh2" (2 * i + 1)) hxl]
      exact (at_eq hq (brSpQ_h i hi')).symm
    simp only [rcv, snd, Interaction.msgVal, brMatR2, snMatR, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at he1
    obtain ⟨-, -, -, en1, eh1⟩ := he1
    obtain ⟨b1, b2⟩ := List.append_inj eh1 (by simp [pack2])
    rw [toNat_eq ek.symm, toNat_eq ed, toNat_eq (a4.trans lv.symm), q1,
      show E tr 3 s pub (Sn.c "nref") = E tr 2 r pub (Br.c "nh2f") from en1.symm,
      show List.map (E tr 3 s pub) (pack2 fun b => Sn.c "hn" b) = List.map (E tr 2 r pub) (pack2 fun b => Br.c "nh2" b)
        from b1.symm,
      show List.map (E tr 3 s pub) Sn.NM = List.map (E tr 2 r pub) ((List.range 4).map fun k => Br.c "nm2" k)
        from b2.symm] at key
    exact key

end

end StateM5a.BrOsl
