import StateM5a.SnContKey2

/-!
# StateM5a.SnContKey3 — row facts for the full key of a continued head

* `ch_hp` / `ch_klen`: on a continued head, `hp_m` pairs the head's key cells (`m = 1..31`) and
  `klen = 62 + odd + rl`;
* `m_snc_hp`, **`snc_bytes_key`**: the `SNC` part `M` of the hashed `hexPrefix` spells, nibble by
  nibble, the key `kk` from position `d + 62 + odd` on, whenever every active chunk of the head
  looks its nibbles up against `kk` at its position `d + 62 + odd + 64·c + j` (`hlook`);
* **`snc_look_A`** / **`snc_look_B`**: that is the case for the walk key (`kid`, `gA = 0`: the
  chunk's `fA = 1 − gA = 1`) and the second key (`kid2`, `g2 = 1`), via `SnContKey1.snc_kc`.
-/

namespace StateM5a.SnContKey3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.KeyDecode StateM5a.SnContHead
open StateM5a.SnContChain StateM5a.SnContKey1 StateM5a.KeyLookups

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Head facts -/

theorem sum_af (O : Nat) (hO : O ≤ 1) : ((List.range 64).map (af O)).sum = 62 + O := by
  rcases (by omega : O = 0 ∨ O = 1) with rfl | rfl <;> decide

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
include hc

set_option maxHeartbeats 4000000 in
/-- The head's `hp_m` (`1 ≤ m < 32`) pairs its key cells. -/
theorem ch_hp (hk : ∀ j, j < 64 → ev tr 3 r pub (Sn.c "k" j) < 16) (m : Nat) (h1 : 1 ≤ m) (hm : m < 32) :
    ev tr 3 r pub (Sn.c "hp" m) = if ev tr 3 r pub (Sn.c "odd") = 1 then
      16 * ev tr 3 r pub (Sn.c "k" (2 * m - 1)) + ev tr 3 r pub (Sn.c "k" (2 * m))
    else 16 * ev tr 3 r pub (Sn.c "k" (2 * m - 2)) + ev tr 3 r pub (Sn.c "k" (2 * m - 1)) := by
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  have hm33 : m < 33 := by omega
  have h0 : m ≠ 0 := by omega
  have h := FieldRows2.sn_hold hc (e := Sn.c "hp" m - Sn.c "odd" * (sm 16 (Sn.k (2 * m - 1)) + Sn.k (2 * m)) -
      (1 - Sn.c "odd") * (sm 16 (Sn.k (2 * m - 2)) + Sn.k (2 * m - 1))) (by
    unfold Sn.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search m hm33)
  have h' := eq_of_sub h
  rw [FieldRows2.sn_k_lt _ (by omega), FieldRows2.sn_k_lt _ (by omega), FieldRows2.sn_k_lt _ (by omega)] at h'
  simp only [sm, ev_sub, ev_hadd, ev_hmul, ev_mul, ev_const, ev_one] at h'
  have k1 := hk (2 * m - 1) (by omega); have k2 := hk (2 * m) (by omega); have k3 := hk (2 * m - 2) (by omega)
  have hh := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "hp" m)
  generalize ev tr 3 r pub (Sn.c "k" (2 * m - 1)) = x1 at k1 h' ⊢
  generalize ev tr 3 r pub (Sn.c "k" (2 * m)) = x2 at k2 h' ⊢
  generalize ev tr 3 r pub (Sn.c "k" (2 * m - 2)) = x3 at k3 h' ⊢
  generalize ev tr 3 r pub (Sn.c "hp" m) = H at h' hh ⊢
  generalize ev tr 3 r pub (Sn.c "odd") = O at h' ho ⊢
  rcases (by omega : O = 0 ∨ O = 1) with rfl | rfl <;> simp at h' ⊢ <;> omega

set_option maxHeartbeats 4000000 in
/-- **`klen = 62 + odd + rl`** on a continued head (`rl` small). -/
theorem ch_klen (hcont : ev tr 3 r pub (Sn.c "cont") = 1) (hrl : ev tr 3 r pub (Sn.c "rl") < 2 ^ 28) :
    ev tr 3 r pub (Sn.c "klen") = 62 + ev tr 3 r pub (Sn.c "odd") + ev tr 3 r pub (Sn.c "rl") := by
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  have ek := sub_val (eq_of_sub (hold rfl hc m_sn_klen))
  rw [ev_sumE, List.map_map] at ek
  have hs : (List.range KMAX).map (ev tr 3 r pub ∘ Sn.a) = (List.range 64).map (af (ev tr 3 r pub (Sn.c "odd"))) := by
    simp only [KMAX]
    apply List.map_congr_left; intro j _
    exact ch_a hc hcont j
  rw [hs, sum_af _ ho] at ek
  rw [ek]
  have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "klen")
  generalize ev tr 3 r pub (Sn.c "odd") = O at ho ⊢
  generalize ev tr 3 r pub (Sn.c "rl") = L at hrl ⊢
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end

/-! ## `SNC` bytes and keys -/

theorem m_snc_hp (m : Nat) (hm : m < 32) :
    Snc.c "hp" m - sm 16 (Snc.c "k" (2 * m)) - Snc.c "k" (2 * m + 1) ∈ Snc.constraints := by
  unfold Snc.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search m hm

theorem hp16 (H x1 x2 : Nat) (k1 : x1 < 16) (k2 : x2 < 16)
    (h : H % P = ((16 * x1 % P + x2) % P)) (hH : H < P) : H = 16 * x1 + x2 := by
  omega

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)

/-- The `SNC` bytes of a continued head, as `SnContKey2.cont_msg_snc` gives them. -/
def SncBytes (tr : Trace Fp) (pub : List Fp) (r : Nat) (M : List Nat) : Prop :=
  ∀ i, i < M.length → ∃ s, s < tr.height 8 ∧ ∃ m, m < 32 ∧ ev tr 8 s pub (Snc.c "act") = 1 ∧
      ev tr 8 s pub (Snc.c "rid") = r ∧ ev tr 8 s pub (Snc.c "ha" m) = 1 ∧
      1 ≤ ev tr 8 s pub (Snc.c "c") ∧ ev tr 8 s pub (Snc.c "c") ≤ 2 ^ 20 ∧
      37 + i = 5 + 32 * ev tr 8 s pub (Snc.c "c") + m ∧ M[i]! = ev tr 8 s pub (Snc.c "hp" m)

include hH in
set_option maxHeartbeats 4000000 in
/-- **The `SNC` bytes spell a key** that every chunk of the head looks its nibbles up against. -/
theorem snc_bytes_key {r : Nat} {M : List Nat} {kk base : Nat} (hM : SncBytes tr pub r M)
    (hlook : ∀ s, s < tr.height 8 → ev tr 8 s pub (Snc.c "act") = 1 → ev tr 8 s pub (Snc.c "rid") = r →
      ∀ c, ev tr 8 s pub (Snc.c "c") = c + 1 → ∀ j, j < 64 → ev tr 8 s pub (Snc.c "a" j) = 1 →
        (keyOf tr kk)[base + 64 * c + j]? = some (ev tr 8 s pub (Snc.c "k" j))) :
    ∀ i, i < M.length → (keyOf tr kk)[base + 2 * i]? = some (M[i]! / 16) ∧
      (keyOf tr kk)[base + 2 * i + 1]? = some (M[i]! % 16) := by
  intro i hi
  obtain ⟨s, hs, m, hm, ha, hrid, hha, c1, -, hpos, hval⟩ := hM i hi
  have hcs := snc_hc hH s hs
  obtain ⟨c, hc⟩ : ∃ c, ev tr 8 s pub (Snc.c "c") = c + 1 := ⟨ev tr 8 s pub (Snc.c "c") - 1, by omega⟩
  have hn := snc_ha_n hcs m hm hha
  obtain ⟨-, -, hf, -⟩ := snc_shape hcs
  have a0 : ev tr 8 s pub (Snc.c "a" (2 * m)) = 1 := by rw [hf _ (by omega), if_pos (by omega)]
  have a1 : ev tr 8 s pub (Snc.c "a" (2 * m + 1)) = 1 := by rw [hf _ (by omega), if_pos (by omega)]
  have l0 := hlook s hs ha hrid c hc (2 * m) (by omega) a0
  have l1 := hlook s hs ha hrid c hc (2 * m + 1) (by omega) a1
  have hb := (RowFacts.keyOf_bounds hH kk).1
  have k0 := hb _ (List.mem_of_getElem? l0)
  have k1 := hb _ (List.mem_of_getElem? l1)
  have e := eq_of_sub (snc_h hcs (m_snc_hp m hm))
  have e2 := sub_val e
  rw [show ev tr 8 s pub (sm 16 (Snc.c "k" (2 * m))) = 16 * ev tr 8 s pub (Snc.c "k" (2 * m)) % P by
    change ev tr 8 s pub (Expr.mul (.const 16) _) = _
    rw [ev_mul, ev_const, show 16 % P = 16 from rfl]] at e2
  have hH16 := hp16 _ _ _ k0 k1 (by rw [Nat.mod_eq_of_lt (ev_lt _)]; exact e2) (ev_lt _)
  have hi' : i = 32 * c + m := by omega
  rw [hval, hH16, hi']
  rw [show base + 2 * (32 * c + m) = base + 64 * c + 2 * m by omega,
    show base + 64 * c + 2 * m + 1 = base + 64 * c + (2 * m + 1) by omega]
  refine ⟨by rw [l0]; congr 1; omega, by rw [l1]; congr 1; omega⟩

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)

theorem ev_pos (d o c j pv : Nat) (hd : d < 2 ^ 21) (ho : o ≤ 1) (hc : c + 1 ≤ 2 ^ 20) (hj : j < 64)
    (hd62 : pv = ((d + 62 + o) + 64 * c) % P) : (pv + j % P) % P = d + 62 + o + 64 * c + j := by
  rw [hd62]; omega

include hH hxK hN in
set_option maxHeartbeats 4000000 in
/-- **Chunks look up the walk key** (`gA = 0` on the head: `fA = 1`). -/
theorem snc_look_A {r : Nat} (hr : r < tr.height 3) (hA0 : ev tr 3 r pub (Sn.c "gA") = 0)
    (hd : ev tr 3 r pub (Sn.c "d") < 2 ^ 21) :
    ∀ s, s < tr.height 8 → ev tr 8 s pub (Snc.c "act") = 1 → ev tr 8 s pub (Snc.c "rid") = r →
      ∀ c, ev tr 8 s pub (Snc.c "c") = c + 1 → ∀ j, j < 64 → ev tr 8 s pub (Snc.c "a" j) = 1 →
        (keyOf tr (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d") + 62 + ev tr 3 r pub (Sn.c "odd") + 64 * c + j]? =
          some (ev tr 8 s pub (Snc.c "k" j)) := by
  intro s hs ha hrid c hcs j hj haj
  obtain ⟨r0, hr0, hrid0, -, hp, hkA, hfA, -, -⟩ := snc_kc hH hxK c s hs ha hcs
  have e : r0 = r := by omega
  subst e
  have hc := tbl_sn D extra nb np hH r0 (List.mem_range.2 hr)
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  have hf1 : ev tr 8 s pub (Snc.c "fA") = 1 := by rw [hfA, FieldRows2.ev_one_sub0 hA0]
  have hg : (Snc.c "fA" * Snc.a j).eval tr 8 s pub = 1 := ev_one_eval (by
    rw [ev_hmul, hf1, snc_a_lt j hj, haj])
  obtain ⟨h1, -⟩ := snc_nibA hH hN j hj hs hg
  obtain ⟨-, c2⟩ := snc_c_range hH hxK hs ha
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  have ed : ev tr 3 r0 pub (Sn.c "d" + 62 + Sn.c "odd") = ev tr 3 r0 pub (Sn.c "d") + 62 + ev tr 3 r0 pub (Sn.c "odd") := by
    rw [ev_hadd, ev_hadd, show ev tr 3 r0 pub (62 : Expr) = 62 % P from ev_const 62]
    have := ev_lt (tr := tr) (t := 3) (r := r0) (pub := pub) (Sn.c "odd")
    omega
  rw [ed] at hp
  have epj : ev tr 8 s pub (Snc.c "p" + K j) = ev tr 3 r0 pub (Sn.c "d") + 62 + ev tr 3 r0 pub (Sn.c "odd") + 64 * c + j := by
    rw [ev_hadd, show ev tr 8 s pub (K j) = j % P from ev_const j]
    exact ev_pos _ _ _ _ _ hd ho (by omega) hj hp
  rw [epj, hkA] at h1
  exact h1

include hH hxK hN in
set_option maxHeartbeats 4000000 in
/-- **Chunks look up the second key** (`g2 = 1` on the head: `gB = 1`). -/
theorem snc_look_B {r : Nat} (hr : r < tr.height 3) (hg2 : ev tr 3 r pub (Sn.c "g2") = 1)
    (hd : ev tr 3 r pub (Sn.c "d") < 2 ^ 21) :
    ∀ s, s < tr.height 8 → ev tr 8 s pub (Snc.c "act") = 1 → ev tr 8 s pub (Snc.c "rid") = r →
      ∀ c, ev tr 8 s pub (Snc.c "c") = c + 1 → ∀ j, j < 64 → ev tr 8 s pub (Snc.c "a" j) = 1 →
        (keyOf tr (ev tr 3 r pub (Sn.c "kid2")))[ev tr 3 r pub (Sn.c "d") + 62 + ev tr 3 r pub (Sn.c "odd") + 64 * c + j]? =
          some (ev tr 8 s pub (Snc.c "k" j)) := by
  intro s hs ha hrid c hcs j hj haj
  obtain ⟨r0, hr0, hrid0, -, hp, -, -, hkB, hgB⟩ := snc_kc hH hxK c s hs ha hcs
  have e : r0 = r := by omega
  subst e
  have hc := tbl_sn D extra nb np hH r0 (List.mem_range.2 hr)
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  have hg : (Snc.c "gB" * Snc.a j).eval tr 8 s pub = 1 := ev_one_eval (by
    rw [ev_hmul, hgB, hg2, snc_a_lt j hj, haj])
  obtain ⟨h1, -⟩ := snc_nibB hH hN j hj hs hg
  obtain ⟨-, c2⟩ := snc_c_range hH hxK hs ha
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  have ed : ev tr 3 r0 pub (Sn.c "d" + 62 + Sn.c "odd") = ev tr 3 r0 pub (Sn.c "d") + 62 + ev tr 3 r0 pub (Sn.c "odd") := by
    rw [ev_hadd, ev_hadd, show ev tr 3 r0 pub (62 : Expr) = 62 % P from ev_const 62]
    have := ev_lt (tr := tr) (t := 3) (r := r0) (pub := pub) (Sn.c "odd")
    omega
  rw [ed] at hp
  have epj : ev tr 8 s pub (Snc.c "p" + K j) = ev tr 3 r0 pub (Sn.c "d") + 62 + ev tr 3 r0 pub (Sn.c "odd") + 64 * c + j := by
    rw [ev_hadd, show ev tr 8 s pub (K j) = j % P from ev_const j]
    exact ev_pos _ _ _ _ _ hd ho (by omega) hj hp
  rw [epj, hkB] at h1
  exact h1

end

end StateM5a.SnContKey3
