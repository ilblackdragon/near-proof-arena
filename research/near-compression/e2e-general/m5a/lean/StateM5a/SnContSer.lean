import StateM5a.SnSer
import StateM5a.SnContHead

/-!
# StateM5a.SnContSer — where a continued head's byte sends land

On an `SN` row with `act = 1`, `cont = 1` and `hplen = H` (`32 ≤ H`, small), every firing send of
`Sn.serBytes id g x mb` (`g = 1`) is `(id, pe, ve)` with `pe < 45 + H + 4·isL` (the message
length `serLen`), and a send at or past offset `37 + H + 4·isL` is the memory byte `mb b` at
offset `37 + H + 4·isL + b`: the head's `hp` sends stop at offset `5 + 31` (`ha_m = [m < 32]`) and
its payload sends end below `37 + H + 4·isL`.
-/

namespace StateM5a.SnContSer

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.SnSer StateM5a.SnContHead
open StateM5a.DecodeM5a StateM5a.KcChain

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem ev3_c (n : Nat) (hn : n < 1000) : ev tr 3 r pub (no_index (OfNat.ofNat n : Expr)) = n := by
  rw [show (no_index (OfNat.ofNat n : Expr)) = Expr.const n from rfl, ev_const, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 4000000 in
/-- **The firing byte sends of a continued head.** -/
theorem cont_ser_pos (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    {H : Nat} (hpl : ev tr 3 r pub (Sn.c "hplen") = H) (hHb : H < 2 ^ 27)
    {id g : Expr} {x mb : Nat → Expr} (hg : ev tr 3 r pub g = 1)
    {i : Interaction} (hi : i ∈ Sn.serBytes id g x mb) (hp : 0 < i.multNat tr 3 r pub) :
    ∃ pe ve, i.msg = [id, pe, ve] ∧ ev tr 3 r pub pe < 45 + H + 4 * ev tr 3 r pub (Sn.c "isL") ∧
      (37 + H + 4 * ev tr 3 r pub (Sn.c "isL") ≤ ev tr 3 r pub pe →
        ∃ b, b < 8 ∧ ve = mb b ∧ ev tr 3 r pub pe = 37 + H + 4 * ev tr 3 r pub (Sn.c "isL") + b) := by
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  unfold Sn.serBytes at hi
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hi
  rcases hi with (((rfl | rfl | rfl | rfl | rfl) | ⟨m, hm, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨b, hb, rfl⟩
  · exact ⟨_, _, rfl, by rw [ev3_c 0 (by decide)]; omega, fun h => by rw [ev3_c 0 (by decide)] at h; omega⟩
  · exact ⟨_, _, rfl, by rw [ev3_c 1 (by decide)]; omega, fun h => by rw [ev3_c 1 (by decide)] at h; omega⟩
  · exact ⟨_, _, rfl, by rw [ev3_c 2 (by decide)]; omega, fun h => by rw [ev3_c 2 (by decide)] at h; omega⟩
  · exact ⟨_, _, rfl, by rw [ev3_c 3 (by decide)]; omega, fun h => by rw [ev3_c 3 (by decide)] at h; omega⟩
  · exact ⟨_, _, rfl, by rw [ev3_c 4 (by decide)]; omega, fun h => by rw [ev3_c 4 (by decide)] at h; omega⟩
  · have h1 := ev3_gate_one hg (eval_one_ev (multNat_one_bit rfl hp))
    have hm33 : m < 33 := by simp [HPMAX] at hm; omega
    have hm' : m < 32 := by
      have := ch_ha hc hA hcont m hm33
      rw [h1] at this; split at this <;> omega
    have e : ev tr 3 r pub (K (5 + m)) = 5 + m := by rw [ev3_K, Nat.mod_eq_of_lt (by omega)]
    exact ⟨_, _, rfl, by rw [e]; omega, fun h => by rw [e] at h; omega⟩
  · have hpos : ev tr 3 r pub (5 + Sn.c "hplen" + K t) = 5 + H + t := by
      rw [ev_hadd, ev_hadd, show ev tr 3 r pub (5 : Expr) = 5 from ev_const 5, ev3_K, hpl,
        Nat.mod_eq_of_lt (show t < P by omega), Nat.mod_eq_of_lt (show 5 + H < P by omega),
        Nat.mod_eq_of_lt (show 5 + H + t < P by omega)]
    by_cases h32 : t < 32
    · exact ⟨_, _, rfl, by rw [hpos]; omega, fun h => by rw [hpos] at h; omega⟩
    · have h1 : ev tr 3 r pub (g * Sn.c "isL") = 1 := by
        have := eval_one_ev (multNat_one_bit (g := if t < 32 then g else g * Sn.c "isL") rfl hp)
        simpa [h32] using this
      have hL1 := ev3_gate_one hg h1
      exact ⟨_, _, rfl, by rw [hpos]; omega, fun h => by rw [hpos] at h; omega⟩
  · have hpos : ev tr 3 r pub (37 + Sn.c "hplen" + sm 4 (Sn.c "isL") + K b) =
        37 + H + 4 * ev tr 3 r pub (Sn.c "isL") + b := by
      rw [ev_hadd, ev_hadd, ev_hadd, show ev tr 3 r pub (37 : Expr) = 37 from ev_const 37, ev3_sm, ev3_K, hpl,
        show 4 % P = 4 from rfl, Nat.mod_eq_of_lt (show 4 * ev tr 3 r pub (Sn.c "isL") < P by omega),
        Nat.mod_eq_of_lt (show 37 + H < P by omega), Nat.mod_eq_of_lt (show b < P by omega),
        Nat.mod_eq_of_lt (show 37 + H + 4 * ev tr 3 r pub (Sn.c "isL") < P by omega),
        Nat.mod_eq_of_lt (show 37 + H + 4 * ev tr 3 r pub (Sn.c "isL") + b < P by omega)]
    exact ⟨_, _, rfl, by rw [hpos]; omega, fun _ => ⟨b, hb, rfl, hpos⟩⟩

end

end StateM5a.SnContSer
