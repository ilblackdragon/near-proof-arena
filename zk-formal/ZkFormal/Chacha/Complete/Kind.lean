import ZkFormal.Chacha.Complete.Basic

/-!
# ZkFormal.Chacha.Complete.Kind — booleanity and row-kind constraints on honest rows

`cBool` holds because every boolean column is a bit.  The `cKind` constraints read only the
flag / `dr` columns (`250 ≤ c < 268`) and `isFirst`, whose honest values depend only on the
row kinds `X.kd`, `Y.kd`: they are checked once per legal kind pair by kernel evaluation.
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen

theorem complete_cBool {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) : ∀ e ∈ cBool, zev Z e = 0 := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have := rowCell_bool X hx
  simp only [boolC, zev_mul, zev_sub, zev_c, zev_k, h.cur]
  rcases (show rowCell X x = 0 ∨ rowCell X x = 1 by omega) with e | e <;> rw [e] <;> decide

/-! ## Row kinds -/

/-- Expressions reading only flag columns, constants and `isFirst`. -/
def onlyFlags : Expr → Bool
  | .const _ => true
  | .col c _ => decide (250 ≤ c) && decide (c < 268)
  | .isFirst => true
  | .add a b => onlyFlags a && onlyFlags b
  | .mul a b => onlyFlags a && onlyFlags b
  | .neg a => onlyFlags a
  | _ => false

theorem zev_congr_flags {Z Z' : ZEnv}
    (hc : ∀ c, 250 ≤ c → c < 268 → Z.cur c = Z'.cur c) (hn : ∀ c, 250 ≤ c → c < 268 → Z.nxt c = Z'.nxt c)
    (hf : Z.first = Z'.first) : ∀ e : Expr, onlyFlags e = true → zev Z e = zev Z' e
  | .const _, _ => rfl
  | .col c nx, he => by
    simp only [onlyFlags, Bool.and_eq_true, decide_eq_true_eq] at he
    cases nx
    · simp [zev, hc c he.1 he.2]
    · simp [zev, hn c he.1 he.2]
  | .isFirst, _ => hf
  | .add a b, he => by
    simp only [onlyFlags, Bool.and_eq_true] at he
    simp only [zev, zev_congr_flags hc hn hf a he.1, zev_congr_flags hc hn hf b he.2]
  | .mul a b, he => by
    simp only [onlyFlags, Bool.and_eq_true] at he
    simp only [zev, zev_congr_flags hc hn hf a he.1, zev_congr_flags hc hn hf b he.2]
  | .neg a, he => by
    simp only [onlyFlags] at he
    simp only [zev, zev_congr_flags hc hn hf a he]
  | .pub _, he => by simp [onlyFlags] at he
  | .isLast, he => by simp [onlyFlags] at he
  | .isTransition, he => by simp [onlyFlags] at he

theorem cKind_onlyFlags : ∀ e ∈ cKind, onlyFlags e = true := by decide

/-- The abstract environment of a kind pair. -/
def kenv (a b : Kd) (f : Int) : ZEnv :=
  ⟨fun c => if 250 ≤ c ∧ c < 268 then kflag a (c - 250) else 0,
   fun c => if 250 ≤ c ∧ c < 268 then kflag b (c - 250) else 0, f, 0, fun _ => 0⟩

def KindOk (a b : Kd) (f : Int) : Prop := ∀ e ∈ cKind, zev (kenv a b f) e = 0

instance (a b : Kd) (f : Int) : Decidable (KindOk a b f) := by unfold KindOk; infer_instance

theorem k_i0 : KindOk .i0 .i1 0 ∧ KindOk .i0 .i1 1 := by decide +kernel
theorem k_i1 : KindOk .i1 (.q 0 0) 0 := by decide +kernel
theorem k_qp : ∀ dr, dr < 10 → ∀ p, p < 7 → KindOk (.q dr p) (.q dr (p + 1)) 0 := by decide +kernel
theorem k_qd : ∀ dr, dr < 9 → KindOk (.q dr 7) (.q (dr + 1) 0) 0 := by decide +kernel
theorem k_qf : KindOk (.q 9 7) (.f 0) 0 := by decide +kernel
theorem k_ff : ∀ j, j < 3 → KindOk (.f j) (.f (j + 1)) 0 := by decide +kernel
theorem k_fe : KindOk (.f 3) .pad 0 ∧ KindOk (.f 3) .i0 0 := by decide +kernel
theorem k_pd : KindOk .pad .pad 0 ∧ KindOk .pad .pad 1 ∧ KindOk .pad .i0 0 ∧ KindOk .pad .i0 1 := by
  decide +kernel

theorem kindOk_of {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y)
    (hf : Z.first = 0 ∨ (Z.first = 1 ∧ FirstOk X)) : KindOk X.kd Y.kd Z.first := by
  have hY0 : ∀ Y : Row, (Y = .pad ∨ ∃ R', Y = .i0 R') → Y.kd = .pad ∨ Y.kd = .i0 := by
    intro Y hY; rcases hY with rfl | ⟨R', rfl⟩
    · exact .inl rfl
    · exact .inr rfl
  have hX : ∀ X : Row, X.kd ≠ .pad → X.kd ≠ .i0 → ¬ FirstOk X := by
    intro X h1 h2 h3; rcases h3 with rfl | ⟨R, rfl⟩
    · exact h1 rfl
    · exact h2 rfl
  have f0 : X.kd ≠ .pad → X.kd ≠ .i0 → Z.first = 0 := by
    intro h1 h2; rcases hf with hf | hf
    · exact hf
    · exact absurd hf.2 (hX X h1 h2)
  have hf01 : Z.first = 0 ∨ Z.first = 1 := by
    rcases hf with hf | hf
    · exact .inl hf
    · exact .inr hf.1
  cases hs with
  | i0 R hR =>
    rcases hf01 with e | e <;> rw [e]
    · exact k_i0.1
    · exact k_i0.2
  | i1 R hR => rw [f0 (by simp [Row.kd]) (by simp [Row.kd])]; exact k_i1
  | qp R hR dr p hdr hp => rw [f0 (by simp [Row.kd]) (by simp [Row.kd])]; exact k_qp dr hdr p hp
  | qd R hR dr hdr => rw [f0 (by simp [Row.kd]) (by simp [Row.kd])]; exact k_qd dr hdr
  | qf R hR => rw [f0 (by simp [Row.kd]) (by simp [Row.kd])]; exact k_qf
  | ff R hR j hj => rw [f0 (by simp [Row.kd]) (by simp [Row.kd])]; exact k_ff j hj
  | fe R hR Y hY =>
    rw [f0 (by simp [Row.kd]) (by simp [Row.kd])]
    rcases hY0 Y hY with e | e <;> rw [e]
    · exact k_fe.1
    · exact k_fe.2
  | pd Y hY =>
    rcases hY0 Y hY with e | e <;> rw [e] <;> rcases hf01 with e' | e' <;> rw [e']
    · exact k_pd.1
    · exact k_pd.2.1
    · exact k_pd.2.2.1
    · exact k_pd.2.2.2

theorem complete_cKind {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y)
    (hf : Z.first = 0 ∨ (Z.first = 1 ∧ FirstOk X)) : ∀ e ∈ cKind, zev Z e = 0 := by
  intro e he
  rw [zev_congr_flags (Z := Z) (Z' := kenv X.kd Y.kd Z.first) ?_ ?_ rfl e (cKind_onlyFlags e he)]
  · exact kindOk_of h hs hf e he
  · intro c h1 h2; simp only [kenv, h.cur, rowCell_fl X h1 h2, if_pos (And.intro h1 h2)]
  · intro c h1 h2; simp only [kenv, h.nxt, rowCell_fl Y h1 h2, if_pos (And.intro h1 h2)]

end ZkFormal.Chacha.Complete
