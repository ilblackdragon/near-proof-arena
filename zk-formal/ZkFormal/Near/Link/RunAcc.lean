import ZkFormal.Near.Link.RunChain

/-!
# ZkFormal.Near.Link.RunAcc — the extracted pre-state accounts and amounts
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem leNat_max : ∀ (l : Bytes), leNat l + 1 = 256 ^ l.length → ∀ b ∈ l, b.toNat = 255
  | [], _ => by simp
  | b :: l, h => by
    have hl := Sound.leNat_lt l
    have hb := b.toNat_lt
    simp only [leNat, List.length_cons, Nat.pow_succ] at h
    have e1 : b.toNat = 255 := by
      have : (b.toNat + 256 * leNat l + 1) % 256 = 0 := by rw [h]; simp [Nat.mul_mod_left]
      omega
    have e2 : leNat l + 1 = 256 ^ l.length := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact e1
    · exact leNat_max l e2 x hx

/-- The pre-state account of a touched slot. -/
def accOf (a : AcctV) : Account :=
  ⟨leN' (a.pre.take 16), leN' ((a.pre.drop 16).take 16), toBytes ((a.pre.drop 32).take 32),
    leN' (a.pre.drop 64)⟩

theorem decode_pre {a : AcctV} (hl : a.pre.length = 72) (hb : Bytes8 a.pre)
    (hnm : ∃ i, i < 16 ∧ a.pre.getD i 0 ≠ 255) : Account.decode (toBytes a.pre) = some (accOf a) := by
  unfold Account.decode
  rw [if_pos (by rw [toBytes_length, hl])]
  have hne : leNat ((toBytes a.pre).take 16) ≠ Params.u128Max := by
    intro he
    obtain ⟨i, hi, hv⟩ := hnm
    have h16 : ((toBytes a.pre).take 16).length = 16 := by simp [toBytes_length, hl]
    have := leNat_max _ (by rw [he, h16]; decide) ((toBytes a.pre).take 16)[i]
      (List.getElem_mem (by rw [h16]; exact hi))
    simp only [List.getElem_take, toBytes, List.getElem_map] at this
    apply hv
    rw [getD_eq_getElem _ _ (by omega)]
    rw [← toNat_ofNat_byte (hb _ (List.getElem_mem (by omega)))]; exact this
  rw [if_neg hne]
  simp only [accOf, leN', toBytes, List.map_take, List.map_drop]

/-- `leN'` ignores trailing zeros. -/
theorem leN'_append_zeros (l : List Nat) (n : Nat) : leN' (l ++ List.replicate n 0) = leN' l := by
  induction l with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.nil_append, leN'] at ih ⊢
      rw [List.replicate_succ, List.map_cons, leNat, ih]; rfl
  | cons x l ih => simp only [List.cons_append, leN', List.map_cons, leNat] at ih ⊢; rw [ih]

theorem ext16 {l l' : List Nat} (h1 : l.length = 16) (h2 : l'.length = 16)
    (h : ∀ i, i < 16 → l.getD i 0 = l'.getD i 0) : l = l' := by
  apply List.ext_getElem (by omega)
  intro i hi hi'
  have := h i (by omega)
  rwa [getD_eq_getElem _ _ hi, getD_eq_getElem _ _ hi'] at this

end Link

end ZkFormal.Near
