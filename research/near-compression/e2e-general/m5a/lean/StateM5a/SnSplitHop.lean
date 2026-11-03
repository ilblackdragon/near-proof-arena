import StateM5a.SnFresh

/-! # StateM5a.SnSplitHop — the hops of a split answer: `SPR` decoding, `jm ≠ 0`, the walk's split
row behind an `oSL` / `oEP` row (split out of `SnSplit`, M5a-7). -/

namespace StateM5a.SnSplit

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF

local notation "P" => 2013265921

set_option maxRecDepth 100000


/-! ## The split answer -/

theorem spr_dec {a b c a' b' c' : Expr} {A B A' B' : List Expr} {f g : Expr → Fp}
    (h : ([a, b, c] ++ A ++ B).map f = ([a', b', c'] ++ A' ++ B').map g) (hA : A.length = A'.length) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ A.map f = A'.map g ∧ B.map f = B'.map g := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := List.append_inj h4 (by simp [hA])
  exact ⟨h1, h2, h3, h5, h6⟩

theorem sn_mem_j0 : Sn.gX * (1 - Sn.c "j0") * (Sn.c "jm" * Sn.c "ij0" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem jm_ne {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (h1 : ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1) : ev tr 3 s pub (Sn.c "jm") ≠ 0 := by
  intro h0
  have := FieldRows2.sn_hold hc sn_mem_j0
  rw [RowSnN.ev_gm h1, ev_sub, ev_hmul, h0, ev_one] at this
  simp at this

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
theorem gX_of {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (h1 : ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1) : ev tr 3 s pub Sn.gX = 1 := by
  have hb : ∀ s' ∈ snNames, ev tr 3 s pub (Sn.c s') ≤ 1 := fun s' hs => sn_flag_le hc s' hs
  have bL := hb "oLX" (by simp [snNames]); have bE := hb "oEX" (by simp [snNames])
  have bU := hb "mU" (by simp [snNames])
  have e3 := sn_sum hc "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc] at e3
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  rw [e3] at c3
  have hle : ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") ≤ 1 := by omega
  have hgX : ev tr 3 s pub Sn.gX = ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") := by
    unfold Sn.gX; rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
  rw [ev_hmul, hgX] at h1
  rw [hgX]
  rcases (by omega : ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") = 0 ∨
    ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") = 1) with h | h
  · rw [h] at h1; simp at h1
  · exact h

section
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
  (hxMQ : ∀ T ∈ extra, sendsOn T.interactions B_MATQ = false)
  (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false)
  (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false)
  (hxE : ∀ T ∈ extra, sendsOn T.interactions B_EPQ = false)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE

/-- The split row behind an `oSL` row of walk `w` is the walk's split row `s`. -/
theorem osl_of_split {s r : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oSL") = 1)
    (hw : E tr 2 r pub (Br.c "w") = E tr 3 s pub (Sn.c "w")) :
    snSpQ.map (E tr 3 s pub) = brSpQ.map (E tr 2 r pub) := by
  obtain ⟨s', hs', hX', hq⟩ := osl_spq hH hxQ hr h1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hc' := tbl_sn D extra nb np hH s' (List.mem_range.2 hs')
  obtain ⟨hg, h0, -⟩ := split_flags hc hX
  obtain ⟨hg', h0', -⟩ := split_flags hc' hX'
  have w' : E tr 3 s' pub (Sn.c "w") = E tr 2 r pub (Br.c "w") := at_eq2 hq (k := 0) rfl rfl
  obtain rfl := sn_term_unique hH hD hx hxN hxK hxR hs hs' (ev_one_eval hg) (ev_one_eval hg') h0 h0'
    (toNat_eq (hw.symm.trans w'.symm))
  exact hq

/-- The split row behind an `oEP` row of walk `w` is the walk's split row `s`. -/
theorem ep_of_split {s p : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (hp : p < tr.height 3) (h1 : ev tr 3 p pub (Sn.c "oEP") = 1)
    (hw : E tr 3 p pub (Sn.c "w") = E tr 3 s pub (Sn.c "w")) :
    ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1 ∧ snEpqS.map (E tr 3 s pub) = snEpqR.map (E tr 3 p pub) := by
  obtain ⟨s', hs', hX', hq⟩ := epq_src hH hxE hp h1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hc' := tbl_sn D extra nb np hH s' (List.mem_range.2 hs')
  have hX'' := gX_of hc' hX'
  obtain ⟨hg, h0, -⟩ := split_flags hc hX
  obtain ⟨hg', h0', -⟩ := split_flags hc' hX''
  have w' : E tr 3 s' pub (Sn.c "w") = E tr 3 p pub (Sn.c "w") := at_eq2 hq (k := 0) rfl rfl
  obtain rfl := sn_term_unique hH hD hx hxN hxK hxR hs hs' (ev_one_eval hg) (ev_one_eval hg') h0 h0'
    (toNat_eq (hw.symm.trans w'.symm))
  exact ⟨hX', hq⟩

end

end

end StateM5a.SnSplit
