import StateM5a.SnContSer

/-!
# StateM5a.SnContSer2 — the values a continued head sends, by offset

`headF k`: the value a continued head (`hplen = H`) puts at serialization offset `k` outside the
`SNC` range `[37, 5 + H)`: the tag `3·isE`, `u32 H` as `(hplen − 256·hph, hph, 0, 0)` (M5a-8), `hp_{k−5}` (`k < 37`), the
payload `x_{k−5−H}`, the memory bytes `mb_{k−5−H−payLen}`.  **`cont_ser_val`**: every firing send of
`Sn.serBytes` on a continued head is `(id, pe, ve)` with `pe < serLen`, `pe` outside `[37, 5 + H)`,
and `ve = headF pe`.
-/

namespace StateM5a.SnContSer2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.SnSer StateM5a.SnContHead
open StateM5a.DecodeM5a StateM5a.KcChain StateM5a.SnContSer

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- The head's value at offset `k` (outside the `SNC` range). -/
def headF (H : Nat) (x mb : Nat → Expr) (k : Nat) : Nat :=
  if k = 0 then ev tr 3 r pub (sm 3 (Sn.c "isE"))
  else if k = 1 then ev tr 3 r pub (Sn.c "hplen" - sm 256 (Sn.c "hph"))
  else if k = 2 then ev tr 3 r pub (Sn.c "hph") else if k < 5 then 0
  else if k < 37 then ev tr 3 r pub (Sn.c "hp" (k - 5))
  else if k < 5 + H + payLen tr pub r then ev tr 3 r pub (x (k - 5 - H))
  else ev tr 3 r pub (mb (k - 5 - H - payLen tr pub r))

end

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat} {H : Nat} {x mb : Nat → Expr}

theorem headF_hp {m : Nat} (hm : m < 32) : headF tr pub r H x mb (5 + m) = ev tr 3 r pub (Sn.c "hp" m) := by
  unfold headF
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 5 + m - 5 = m by omega]

theorem headF_x (hH : 32 ≤ H) {t : Nat} (ht : t < payLen tr pub r) :
    headF tr pub r H x mb (5 + H + t) = ev tr 3 r pub (x t) := by
  unfold headF
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show 5 + H + t - 5 - H = t by omega]

theorem headF_mb (hH : 32 ≤ H) {b : Nat} :
    headF tr pub r H x mb (5 + H + payLen tr pub r + b) = ev tr 3 r pub (mb b) := by
  unfold headF
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), show 5 + H + payLen tr pub r + b - 5 - H - payLen tr pub r = b by omega]

theorem headF_0 : headF tr pub r H x mb 0 = ev tr 3 r pub (sm 3 (Sn.c "isE")) := by
  unfold headF; rw [if_pos rfl]
theorem headF_1 : headF tr pub r H x mb 1 = ev tr 3 r pub (Sn.c "hplen" - sm 256 (Sn.c "hph")) := by
  unfold headF; rw [if_neg (by omega), if_pos rfl]
theorem headF_2 : headF tr pub r H x mb 2 = ev tr 3 r pub (Sn.c "hph") := by
  unfold headF; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem headF_z {k : Nat} (h1 : 3 ≤ k) (h2 : k < 5) : headF tr pub r H x mb k = 0 := by
  unfold headF; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem payLen_eq : payLen tr pub r = 32 + 4 * ev tr 3 r pub (Sn.c "isL") := rfl

set_option maxHeartbeats 4000000 in
/-- **The firing byte sends of a continued head, with their values.** -/
theorem cont_ser_val (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hpl : ev tr 3 r pub (Sn.c "hplen") = H) (hH32 : 32 ≤ H) (hHb : H < 2 ^ 27)
    {id g : Expr} (hg : ev tr 3 r pub g = 1)
    {i : Interaction} (hi : i ∈ Sn.serBytes id g x mb) (hp : 0 < i.multNat tr 3 r pub) :
    ∃ pe ve, i.msg = [id, pe, ve] ∧ ev tr 3 r pub pe < 45 + H + 4 * ev tr 3 r pub (Sn.c "isL") ∧
      (ev tr 3 r pub pe < 37 ∨ 5 + H ≤ ev tr 3 r pub pe) ∧
      ev tr 3 r pub ve = headF tr pub r H x mb (ev tr 3 r pub pe) := by
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  have hpL := payLen_eq (tr := tr) (pub := pub) (r := r)
  unfold Sn.serBytes at hi
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hi
  rcases hi with (((rfl | rfl | rfl | rfl | rfl) | ⟨m, hm, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨b, hb, rfl⟩
  · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> rw [ev3_c 0 (by decide)]
    · omega
    · omega
    · rw [headF_0]
  · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> rw [ev3_c 1 (by decide)]
    · omega
    · omega
    · rw [headF_1]
  · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> rw [ev3_c 2 (by decide)]
    · omega
    · omega
    · rw [headF_2]
  · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> rw [ev3_c 3 (by decide)]
    · omega
    · omega
    · rw [headF_z (by omega) (by omega), ev3_c 0 (by decide)]
  · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> rw [ev3_c 4 (by decide)]
    · omega
    · omega
    · rw [headF_z (by omega) (by omega), ev3_c 0 (by decide)]
  · have h1 := ev3_gate_one hg (eval_one_ev (multNat_one_bit rfl hp))
    have hm33 : m < 33 := by simp [HPMAX] at hm; omega
    have hm' : m < 32 := by
      have := ch_ha hc hA hcont m hm33
      rw [h1] at this; split at this <;> omega
    have e : ev tr 3 r pub (K (5 + m)) = 5 + m := by rw [ev3_K, Nat.mod_eq_of_lt (by omega)]
    exact ⟨_, _, rfl, by rw [e]; omega, by rw [e]; omega, by rw [e, headF_hp hm']⟩
  · have hpos : ev tr 3 r pub (5 + Sn.c "hplen" + K t) = 5 + H + t := by
      rw [ev_hadd, ev_hadd, show ev tr 3 r pub (5 : Expr) = 5 from ev_const 5, ev3_K, hpl,
        Nat.mod_eq_of_lt (show t < P by omega), Nat.mod_eq_of_lt (show 5 + H < P by omega),
        Nat.mod_eq_of_lt (show 5 + H + t < P by omega)]
    have htp : t < payLen tr pub r := by
      by_cases h32 : t < 32
      · omega
      · have h1 : ev tr 3 r pub (g * Sn.c "isL") = 1 := by
          have := eval_one_ev (multNat_one_bit (g := if t < 32 then g else g * Sn.c "isL") rfl hp)
          simpa [h32] using this
        have hL1 := ev3_gate_one hg h1
        omega
    exact ⟨_, _, rfl, by rw [hpos]; omega, by rw [hpos]; omega, by rw [hpos, headF_x hH32 htp]⟩
  · have hpos : ev tr 3 r pub (37 + Sn.c "hplen" + sm 4 (Sn.c "isL") + K b) =
        5 + H + payLen tr pub r + b := by
      rw [ev_hadd, ev_hadd, ev_hadd, show ev tr 3 r pub (37 : Expr) = 37 from ev_const 37, ev3_sm, ev3_K, hpl,
        show 4 % P = 4 from rfl, Nat.mod_eq_of_lt (show 4 * ev tr 3 r pub (Sn.c "isL") < P by omega),
        Nat.mod_eq_of_lt (show 37 + H < P by omega), Nat.mod_eq_of_lt (show b < P by omega),
        Nat.mod_eq_of_lt (show 37 + H + 4 * ev tr 3 r pub (Sn.c "isL") < P by omega),
        Nat.mod_eq_of_lt (show 37 + H + 4 * ev tr 3 r pub (Sn.c "isL") + b < P by omega), hpL]
      omega
    exact ⟨_, _, rfl, by rw [hpos]; omega, by rw [hpos]; omega, by rw [hpos, headF_mb hH32]⟩

end

end StateM5a.SnContSer2
