import StateM5a.SnSplitKeys

/-! # StateM5a.SnSplitEXA — the extension split (`oEX`): field facts and the old side's memory (`ex_mem`). -/

namespace StateM5a.SnSplitLoc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.RowBrN

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The extension split (`oEX`) -/

theorem ev_limb16_byte3 {tr : Trace Fp} {r : Nat} {pub : List Fp} {v : Nat → Expr} {k : Nat}
    (ha : ev tr 3 r pub (v (2 * k)) < 256)
    (hb : ev tr 3 r pub (v (2 * k + 1)) < 256) : ev tr 3 r pub (limb16 v k) < 65536 := by
  unfold limb16
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 256 * ev tr 3 r pub (v (2 * k + 1)) < P by omega),
    Nat.mod_eq_of_lt (show ev tr 3 r pub (v (2 * k)) + 256 * ev tr 3 r pub (v (2 * k + 1)) < P by omega)]
  omega

theorem sn_mem_chainX {e : Expr} (he : e ∈ memChain (Sn.c "oEX") Sn.M Sn.CM [Sn.own, 0, 0, 0] [0, 0, 0, 0]
    (fun t => Sn.c "cy2" t)) : e ∈ Sn.constraints := by
  unfold Sn.constraints; exact List.mem_append_right _ he

theorem sn_rng_cmb : ∀ t, t < 8 → memD (rcv B_RNG (Sn.c "oEX") [Sn.c "cmb" t]) Sn.interactions = true := by
  decide

theorem sn_mem_z1 : Sn.c "oEX" * Sn.c "z" * (Sn.c "klen" - Sn.c "jm" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_z0 : Sn.c "oEX" * (1 - Sn.c "z") * ((Sn.c "klen" - Sn.c "jm" - 1) * Sn.c "iz" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_xhf : Sn.c "xhf" - Sn.c "oEX" * (Sn.c "z" * Sn.c "xf" + (1 - Sn.c "z") * Sn.c "sxhf") ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_xm (t : Nat) (ht : t < 4) :
    Sn.c "xm" t - Sn.c "oEX" * (Sn.c "z" * Sn.CM.getD t 0 + (1 - Sn.c "z") * Sn.c "sxm" t) ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_map, List.mem_range]; memfind

theorem hdr5_dec {a b c d e a' b' c' d' e' : Expr} {A B A' B' : List Expr} {f g : Expr → Fp}
    (h : ([a, b, c, d, e] ++ A ++ B).map f = ([a', b', c', d', e'] ++ A' ++ B').map g) (hA : A.length = A'.length) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ f d = g d' ∧ f e = g e' ∧ A.map f = A'.map g ∧ B.map f = B'.map g := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨h7, h8⟩ := List.append_inj h6 (by simp [hA])
  exact ⟨h1, h2, h3, h4, h5, h7, h8⟩

theorem hdr4_dec {a b c d a' b' c' d' : Expr} {A B A' B' : List Expr} {f g : Expr → Fp}
    (h : ([a, b, c, d] ++ A ++ B).map f = ([a', b', c', d'] ++ A' ++ B').map g) (hA : A.length = A'.length) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ f d = g d' ∧ A.map f = A'.map g ∧ B.map f = B'.map g := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨h7, h8⟩ := List.append_inj h5 (by simp [hA])
  exact ⟨h1, h2, h3, h4, h7, h8⟩

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
theorem gX_of_oEX {tr : Trace Fp} {pub : List Fp} {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (h1 : ev tr 3 s pub (Sn.c "oEX" * (1 - Sn.c "z")) = 1) : ev tr 3 s pub Sn.gX = 1 ∧ ev tr 3 s pub (Sn.c "oEX") = 1 := by
  have hb : ∀ s' ∈ snNames, ev tr 3 s pub (Sn.c s') ≤ 1 := fun s' hs => sn_flag_le hc s' hs
  have bE := hb "oEX" (by simp [snNames]); have bL := hb "oLX" (by simp [snNames])
  have bU := hb "mU" (by simp [snNames]); have bR := hb "oLR" (by simp [snNames])
  have bEU := hb "oEU" (by simp [snNames])
  have hE : ev tr 3 s pub (Sn.c "oEX") = 1 := by
    rw [ev_hmul] at h1
    rcases (by omega : ev tr 3 s pub (Sn.c "oEX") = 0 ∨ ev tr 3 s pub (Sn.c "oEX") = 1) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have e3 := sn_sum hc "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc] at e3
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  rw [e3] at c3
  refine ⟨?_, hE⟩
  unfold Sn.gX; rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- **The extension split's memory**: `mem = cm + extOwnMem k` (16-bit limbs, `cmb` bytes in `RNG`). -/
theorem ex_mem (hH : Holds (fullAir D extra nb np) pub tr) (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    {s : Nat} (hs : s < tr.height 3) (h1 : ev tr 3 s pub (Sn.c "oEX") = 1)
    (hA : ev tr 3 s pub (Sn.c "act") = 1) (hcont : ev tr 3 s pub (Sn.c "cont") = 0)
    (hM : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 65536) :
    snMem tr pub s = le4 (Sn.CM.map (E tr 3 s pub)) + extOwnMem (snKey tr pub s) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hown, hown'⟩ := RowSnE.ev_own hc hA hcont
  have rb : ∀ t, t < 8 → ev tr 3 s pub (Sn.c "cmb" t) < 256 := fun t ht =>
    WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir])
      (by rw [WsDecode.full_get 3 (by decide)]; exact memD_mem (sn_rng_cmb t ht)) hs (ev_one_eval h1)
  have hCM : ∀ k, k < 4 → ev tr 3 s pub (Sn.CM.getD k 0) < 65536 := by
    intro k hk
    have : Sn.CM.getD k 0 = limb16 (fun b => Sn.c "cmb" b) k := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [this]; exact ev_limb16_byte3 (rb _ (by omega)) (rb _ (by omega))
  have hM' : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 2 ^ 17 := fun k hk => by
    have := hM k hk; omega
  have hCM' : ∀ k, k < 4 → ev tr 3 s pub (Sn.CM.getD k 0) < 2 ^ 17 := fun k hk => by
    have := hCM k hk; omega
  have q := memChain_sound _ _ _ _ _ _ (fun e he => FieldRows2.sn_hold hc (sn_mem_chainX he)) h1 (by
    intro k hk
    refine ⟨hM' k hk, hCM' k hk, ?_, ?_⟩ <;>
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, show (0 : Expr) = Expr.const 0 from rfl,
        ev_const] <;> omega)
  unfold V4 at q
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (0 : Expr) = Expr.const 0 from rfl, ev_const,
    Nat.zero_mod] at q
  rw [← hown]
  unfold snMem le4
  simp only [Sn.M, Sn.CM, memLimbs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, E, sE] at q ⊢
  unfold ev at q hown'
  unfold ev
  omega


end

end StateM5a.SnSplitLoc
