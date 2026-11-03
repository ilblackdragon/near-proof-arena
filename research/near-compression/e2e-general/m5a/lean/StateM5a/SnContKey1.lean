import StateM5a.SnContRec4

/-!
# StateM5a.SnContKey1 — a continued head's full key, decoded (pure) and its `SNC` chain fields

* **`hpDec_split`** / **`hpDec_head`** (pure): the nibbles a continued head's `hexPrefix`
  `hp₀..hp₃₁ ++ M` encodes are the head's `62 + odd` key cells followed by the two nibbles of
  every byte of `M`: `hpDec (hp ++ M) odd = [k₀ .. k₆₁₊odd] ++ M.flatMap nib` (`hp₀ = 32·L +
  odd·(16 + k₀)`, `hp_m` the head's pairing of its key cells, `k_j < 16`).
* **`snc_kc`**: every active `SNC` row with chunk index `c + 1` belongs to a continued head `r0 =
  rid`, and its `KC` fields are that head's: position `p = d + 62 + odd + 64·c` (mod `P`), the
  walk key `kA = kid` with flag `fA = 1 − gA`, the second key `kB = kid2` with flag `gB = g2`
  (induction on `c` over the `KC` chain: the head sends index `1`, a continuing chunk sends
  `c + 1, p + 64` with its own fields).
-/

namespace StateM5a.SnContKey1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.KeyDecode
open StateM5a.KcChain StateM5a.KeyDigest StateM5a.SnContRec1

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Pure: decoding -/

/-- The two nibbles of a byte. -/
def nib (b : Nat) : List Nat := [b / 16, b % 16]

theorem flat_get : ∀ (bs : List Nat) (q e : Nat), e < 2 →
    (bs.flatMap nib)[2 * q + e]? = bs[q]?.map (fun b => if e = 0 then b / 16 else b % 16)
  | [], q, e, _ => by simp
  | b :: bs, 0, e, he => by
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;> simp [nib]
  | b :: bs, q + 1, e, he => by
    have ih := flat_get bs q e he
    simp only [List.flatMap_cons, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by simp [nib]; omega)]
    simp only [nib, List.length_cons, List.length_nil]
    rw [show 2 * (q + 1) + e - (0 + 1 + 1) = 2 * q + e by omega]
    exact ih

theorem flat_len' (bs : List Nat) : (bs.flatMap nib).length = 2 * bs.length := flat_len bs

/-- `hpDec` of a byte list split after its first part. -/
theorem hpDec_split (A M : List Nat) (odd : Nat) (hA : A ≠ []) :
    hpDec (A ++ M) odd = hpDec A odd ++ M.flatMap nib := by
  obtain ⟨a, A', rfl⟩ : ∃ a A', A = a :: A' := by
    cases A with
    | nil => exact absurd rfl hA
    | cons a A' => exact ⟨a, A', rfl⟩
  simp only [hpDec, List.cons_append, List.headD_cons, List.tail_cons, List.flatMap_append, List.append_assoc]
  rfl

/-- **The head part of a continued key** (pure): `hpDec` of the head's 32 `hp` bytes is its
`62 + odd` key cells. -/
theorem hpDec_head (hp k : Nat → Nat) (odd L : Nat) (hO : odd ≤ 1) (hk : ∀ j, j < 64 → k j < 16)
    (h0 : hp 0 = 32 * L + odd * (16 + k 0))
    (hm : ∀ m, 1 ≤ m → m < 32 →
      hp m = if odd = 1 then 16 * k (2 * m - 1) + k (2 * m) else 16 * k (2 * m - 2) + k (2 * m - 1)) :
    hpDec ((List.range 32).map hp) odd = (List.range (62 + odd)).map k := by
  have htail : ((List.range 32).map hp).tail = (List.range 31).map fun q => hp (q + 1) := by
    rw [show List.range 32 = 0 :: List.range' 1 31 from rfl, List.map_cons, List.tail_cons,
      List.range_eq_range', List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map]
    apply List.map_congr_left; intro q _; simp [Function.comp, Nat.add_comm]
  apply List.ext_getElem?
  intro j
  unfold hpDec
  rw [htail]
  have hF := fun q e (he : e < 2) => flat_get ((List.range 31).map fun q => hp (q + 1)) q e he
  rcases (by omega : odd = 0 ∨ odd = 1) with rfl | rfl
  · simp only [Nat.zero_ne_one, ↓reduceIte, List.nil_append]
    obtain ⟨q, e, he2, rfl⟩ : ∃ q e, e < 2 ∧ j = 2 * q + e := ⟨j / 2, j % 2, Nat.mod_lt _ (by decide), by omega⟩
    change (((List.range 31).map fun q => hp (q + 1)).flatMap nib)[2 * q + e]? = _
    rw [hF q e he2]
    by_cases hj : q < 31
    · rw [List.getElem?_map, List.getElem?_range hj, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      have h := hm (q + 1) (by omega) (by omega)
      simp only [Nat.zero_ne_one, ↓reduceIte] at h
      rw [h, show 2 * (q + 1) - 2 = 2 * q by omega, show 2 * (q + 1) - 1 = 2 * q + 1 by omega]
      have := hk (2 * q) (by omega); have := hk (2 * q + 1) (by omega)
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · simp only [↓reduceIte, Nat.add_zero]; omega
      · simp only [Nat.one_ne_zero, ↓reduceIte]; omega
    · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega), List.getElem?_map,
        List.getElem?_eq_none (by simp; omega)]
      rfl
  · simp only [↓reduceIte, List.singleton_append]
    rcases j with _ | j
    · have e0 : ((List.range 32).map hp).headD 0 = hp 0 := rfl
      rw [e0, List.getElem?_cons_zero, List.getElem?_map, List.getElem?_range (by omega), Option.map_some, h0]
      have := hk 0 (by decide)
      congr 1; omega
    · rw [List.getElem?_cons_succ]
      obtain ⟨q, e, he2, rfl⟩ : ∃ q e, e < 2 ∧ j = 2 * q + e := ⟨j / 2, j % 2, Nat.mod_lt _ (by decide), by omega⟩
      change (((List.range 31).map fun q => hp (q + 1)).flatMap nib)[2 * q + e]? = _
      rw [hF q e he2]
      by_cases hj : q < 31
      · rw [List.getElem?_map, List.getElem?_range hj, List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.some.injEq]
        have h := hm (q + 1) (by omega) (by omega)
        simp only [↓reduceIte] at h
        rw [h, show 2 * (q + 1) - 1 = 2 * q + 1 by omega, show 2 * (q + 1) = 2 * q + 2 by omega]
        have := hk (2 * q + 1) (by omega); have := hk (2 * q + 2) (by omega)
        rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
        · simp only [↓reduceIte, Nat.add_zero]; omega
        · simp only [Nat.one_ne_zero, ↓reduceIte]
          rw [show 2 * q + 1 + 1 = 2 * q + 2 by omega]; omega
      · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega), List.getElem?_map,
          List.getElem?_eq_none (by simp; omega)]
        rfl

/-! ## The `KC` chain: an `SNC` chunk's fields are its head's -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
include hH hxK

set_option maxHeartbeats 4000000 in
/-- **An active `SNC` chunk `c + 1` carries its head's key fields.** -/
theorem snc_kc : ∀ c s, s < tr.height 8 → ev tr 8 s pub (Snc.c "act") = 1 → ev tr 8 s pub (Snc.c "c") = c + 1 →
    ∃ r0, r0 < tr.height 3 ∧ ev tr 8 s pub (Snc.c "rid") = r0 ∧ ev tr 3 r0 pub (Sn.c "cont") = 1 ∧
      ev tr 8 s pub (Snc.c "p") = (ev tr 3 r0 pub (Sn.c "d" + 62 + Sn.c "odd") + 64 * c) % P ∧
      ev tr 8 s pub (Snc.c "kA") = ev tr 3 r0 pub (Sn.c "kid") ∧
      ev tr 8 s pub (Snc.c "fA") = ev tr 3 r0 pub (1 - Sn.c "gA") ∧
      ev tr 8 s pub (Snc.c "kB") = ev tr 3 r0 pub (Sn.c "kid2") ∧
      ev tr 8 s pub (Snc.c "gB") = ev tr 3 r0 pub (Sn.c "g2") := by
  intro c
  induction c with
  | zero =>
    intro s hs ha hcs
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kc_r_mem) hs rfl (ev_one_eval ha)
    rcases sender_m5a2 B_KC 3 8 (by simp [m5aAir]) (by simp [m5aAir]) (kc_only D) hxK
        (recv_sent hH hm) with ⟨t, ht, i, hi, hb, hsn, hp, he⟩ | ⟨t, ht, i, hi, hb, hsn, hp, he⟩
    · change i ∈ Sn.interactions at hi
      obtain rfl := filter_one_mem sn_kc_s hi hb hsn
      have hco := eval_one_ev (multNat_one_bit rfl hp)
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      obtain ⟨e0, -, e2, e3, e4, e5, e6, -⟩ := he
      refine ⟨t, ht, by rw [toNat_eq e0, sn_rid hH t ht], hco, ?_, toNat_eq e3, toNat_eq e4, toNat_eq e5,
        toNat_eq e6⟩
      rw [toNat_eq e2, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
    · exfalso
      change i ∈ Snc.interactions at hi
      obtain rfl := filter_one_mem snc_kc_s hi hb hsn
      have hta := snc_more_act (snc_hc hH t ht) (eval_one_ev (multNat_one_bit rfl hp))
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e1 := toNat_eq he.2.1
      obtain ⟨h1, h2⟩ := snc_c_range hH hxK ht hta
      have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e1
      omega
  | succ c ih =>
    intro s hs ha hcs
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kc_r_mem) hs rfl (ev_one_eval ha)
    rcases sender_m5a2 B_KC 3 8 (by simp [m5aAir]) (by simp [m5aAir]) (kc_only D) hxK
        (recv_sent hH hm) with ⟨t, ht, i, hi, hb, hsn, hp, he⟩ | ⟨t, ht, i, hi, hb, hsn, hp, he⟩
    · exfalso
      change i ∈ Sn.interactions at hi
      obtain rfl := filter_one_mem sn_kc_s hi hb hsn
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e1 := toNat_eq he.2.1
      rw [show ev tr 3 t pub (1 : Expr) = 1 from ev_one] at e1
      omega
    · change i ∈ Snc.interactions at hi
      obtain rfl := filter_one_mem snc_kc_s hi hb hsn
      have hta := snc_more_act (snc_hc hH t ht) (eval_one_ev (multNat_one_bit rfl hp))
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := he
      have e1 := toNat_eq e1
      obtain ⟨h1, h2⟩ := snc_c_range hH hxK ht hta
      have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e1
      obtain ⟨r0, hr0, hrid, hco, hp0, hA0, hfA, hB0, hgB⟩ := ih t ht hta (by omega)
      refine ⟨r0, hr0, by rw [toNat_eq e0, hrid], hco, ?_, by rw [toNat_eq e3, hA0], by rw [toNat_eq e4, hfA],
        by rw [toNat_eq e5, hB0], by rw [toNat_eq e6, hgB]⟩
      rw [toNat_eq e2, ev_hadd, hp0, show ev tr 8 t pub (64 : Expr) = 64 % P from ev_const 64]
      omega

end

end StateM5a.SnContKey1
