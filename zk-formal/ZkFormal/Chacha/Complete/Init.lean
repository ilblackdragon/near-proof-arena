import ZkFormal.Chacha.Complete.Basic

/-!
# ZkFormal.Chacha.Complete.Init — the input-row constraints `cInit` on honest rows

Every `cInit` constraint is `I0 · _` or `I1 · _`; on an `I0` / `I1` row the factor is the
input state, the key range checks and the counter range check (`ctr < 2^26`).
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen
open NearSpecV3

theorem zmul0 {Z : ZEnv} {x : Nat} (h : Z.cur x = 0) (e : Expr) : zev Z (.mul (E.c x) e) = 0 := by
  simp [h]

theorem zmul1 {Z : ZEnv} {x : Nat} (h : Z.cur x = 1) (e : Expr) :
    zev Z (.mul (E.c x) e) = zev Z e := by
  simp [h]

theorem step_kinds {X Y : Row} (hs : Step X Y) :
    (∃ R, ReqOk R ∧ X = .i0 R) ∨ (∃ R, ReqOk R ∧ X = .i1 R) ∨
      (kflag X.kd 0 = 0 ∧ kflag X.kd 1 = 0) := by
  cases hs with
  | i0 R hR => exact .inl ⟨R, hR, rfl⟩
  | i1 R hR => exact .inr (.inl ⟨R, hR, rfl⟩)
  | _ => right; right; simp [Row.kd, kflag] <;> omega

theorem bt_ctr {c b : Nat} (hc : c < 2 ^ 26) (hb : 26 ≤ b) : bt c b = 0 := by
  unfold bt
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hb))]

theorem kWord_blk (R : Req) (j : Nat) :
    kWord (.i0 R) j = (if j < 8 then R.key.getD j 0 else if j = 8 then R.ctr else 0) ∧
    kWord (.i1 R) j = (if j < 8 then R.key.getD j 0 else if j = 8 then R.ctr else 0) :=
  ⟨rfl, rfl⟩

theorem complete_cInit {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y) :
    ∀ e ∈ cInit, zev Z e = 0 := by
  intro e he
  have hI0 := zI0 h; have hI1 := zI1 h
  unfold cInit at he
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    List.mem_range'_1] at he
  rcases step_kinds hs with ⟨R, hR, rfl⟩ | ⟨R, hR, rfl⟩ | ⟨k0, k1⟩
  · -- I0 row
    have e1 : Z.cur colI0 = 1 := by rw [hI0]; rfl
    have e0 : Z.cur colI1 = 0 := by rw [hI1]; rfl
    rcases he with ((((⟨i, ⟨hi, -⟩, l, hl, rfl⟩ | ⟨m, hm, l, hl, rfl⟩) | ⟨m, hm, l, hl, rfl⟩) |
      ⟨b, hb, rfl⟩) | ⟨l, hl, rfl⟩)
    · rw [zmul1 e1, zev_sub, zS h hi hl, zev_initLimb h hR (fun j => (kWord_blk R j).1) hi hl]
      exact Int.sub_self _
    · rw [zmul1 e1, zev_sub, zX h (by omega) hl, zK h (by omega) hl]
      simp only [xWord, kWord, if_pos hm, if_pos (show m < 8 by omega)]
      exact Int.sub_self _
    all_goals first | exact zmul0 e0 _ | skip
  · -- I1 row
    have e0 : Z.cur colI0 = 0 := by rw [hI0]; rfl
    have e1 : Z.cur colI1 = 1 := by rw [hI1]; rfl
    rcases he with ((((⟨i, ⟨hi, -⟩, l, hl, rfl⟩ | ⟨m, hm, l, hl, rfl⟩) | ⟨m, hm, l, hl, rfl⟩) |
      ⟨b, hb, rfl⟩) | ⟨l, hl, rfl⟩)
    · exact zmul0 e0 _
    · exact zmul0 e0 _
    · rw [zmul1 e1, zev_sub, zX h (by omega) hl, zK h (by omega) hl]
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;> exact Int.sub_self _
    · rw [zmul1 e1, zev_c, h.cur, rowCell_X _ (by decide) (by omega)]
      show ((bt R.ctr b : Nat) : Int) = 0
      rw [bt_ctr hR.2.2.1 (by omega)]; rfl
    · rw [zmul1 e1, zev_sub, zS h (by decide) hl, zK h (by decide) hl]
      show ((limbN (init R)[12]! l : Nat) : Int) - _ = 0
      rw [init_get hR (by decide)]
      exact Int.sub_self _
  · -- other rows: both factors vanish
    have e0 : Z.cur colI0 = 0 := by rw [hI0, k0]
    have e1 : Z.cur colI1 = 0 := by rw [hI1, k1]
    rcases he with ((((⟨i, ⟨hi, -⟩, l, hl, rfl⟩ | ⟨m, hm, l, hl, rfl⟩) | ⟨m, hm, l, hl, rfl⟩) |
      ⟨b, hb, rfl⟩) | ⟨l, hl, rfl⟩) <;>
    first | exact zmul0 e0 _ | exact zmul0 e1 _

end ZkFormal.Chacha.Complete
