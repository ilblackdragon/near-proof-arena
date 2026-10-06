import ZkFormal.Chacha.Complete.QR
import ZkFormal.Chacha.Complete.Init

/-!
# ZkFormal.Chacha.Complete.Copy — state / key copies (`cCopy`) and feed-forward (`cFF`)

* `cCopy`: the next row's state is this row's (`I0, I1, F0..F2`) or the quarter-round of it
  (`Q`); the key/counter cells are constant along a block; nothing is asked of `F3` and
  padding rows.
* `cFF`: on `F j` the outputs are `add32 (fin[i]) (init[i])` (limbs with carries); the
  multiplicity bits are zero off `F` rows.
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen
open NearSpecV3

/-- Close `kflag (kind) k = v` goals for concrete kinds. -/
macro "kfl" : tactic => `(tactic| (simp only [Row.kd, kflag]; repeat' (first | omega | rfl | split)))

section
variable {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y)
include h

theorem zev_gCopy' : zev Z gCopy =
    (kflag X.kd 0 + kflag X.kd 1 + kflag X.kd 10 + kflag X.kd 11 + kflag X.kd 12 : Nat) := by
  simp only [gCopy, zev_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zev_c,
    zI0 h, zI1 h, zF h (show 0 < 4 by decide), zF h (show 1 < 4 by decide),
    zF h (show 2 < 4 by decide)]
  simp only [Int.natCast_add, Nat.reduceAdd]; omega

theorem zev_sumP' : zev Z sumP = (kflag X.kd 2 + kflag X.kd 3 + kflag X.kd 4 + kflag X.kd 5 +
    kflag X.kd 6 + kflag X.kd 7 + kflag X.kd 8 + kflag X.kd 9 : Nat) := by
  simp only [sumP, zev_sum, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.nil_append, zev_c,
    zP h (show 0 < 8 by decide), zP h (show 1 < 8 by decide), zP h (show 2 < 8 by decide),
    zP h (show 3 < 8 by decide), zP h (show 4 < 8 by decide), zP h (show 5 < 8 by decide),
    zP h (show 6 < 8 by decide), zP h (show 7 < 8 by decide)]
  simp only [Int.natCast_add, Nat.reduceAdd]; omega

theorem zev_sumF' : zev Z sumF = (kflag X.kd 10 + kflag X.kd 11 + kflag X.kd 12 + kflag X.kd 13 : Nat) := by
  simp only [sumF, zev_sum, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.nil_append, zev_c,
    zF h (show 0 < 4 by decide), zF h (show 1 < 4 by decide), zF h (show 2 < 4 by decide),
    zF h (show 3 < 4 by decide)]
  simp only [Int.natCast_add, Nat.reduceAdd]; omega

/-- A copied state slot on a row without `P` flags. -/
theorem copyS_plain (hP : ∀ p, p < 8 → kflag X.kd (2 + p) = 0) {i l : Nat} (hi : i < 16) (hl : l < 2)
    (hs : sWord Y i = sWord X i) :
    zev Z (.add (.mul gCopy (E.sub (sN i l) (sC i l)))
      (E.sel colP 8 fun p => E.sub (sN i l) (newS (grp p) i l))) = 0 := by
  rw [zev_add, zev_mul, selP_zero h hP, zev_sub, zSn h hi hl, zS h hi hl, hs]; simp

/-- No copy at all (`F3`, padding). -/
theorem copyS_none (hP : ∀ p, p < 8 → kflag X.kd (2 + p) = 0) (hg : zev Z gCopy = 0) (i l : Nat) :
    zev Z (.add (.mul gCopy (E.sub (sN i l) (sC i l)))
      (E.sel colP 8 fun p => E.sub (sN i l) (newS (grp p) i l))) = 0 := by
  rw [zev_add, zev_mul, selP_zero h hP, hg]; simp

theorem copyK_same (hk : ∀ j, kWord Y j = kWord X j) {j l : Nat} (hj : j < 9) (hl : l < 2) :
    zev Z (.mul (.add gCopy sumP) (E.sub (E.n (colK j l)) (E.c (colK j l)))) = 0 := by
  rw [zev_mul, zev_sub, zKn h hj hl, zK h hj hl, hk]; simp

omit h in
theorem copyK_none (hg : zev Z (.add gCopy sumP) = 0) (j l : Nat) :
    zev Z (.mul (.add gCopy sumP) (E.sub (E.n (colK j l)) (E.c (colK j l)))) = 0 := by
  rw [zev_mul, hg]; simp

end

theorem complete_cCopy {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y) :
    ∀ e ∈ cCopy, zev Z e = 0 := by
  intro e he
  unfold cCopy at he
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at he
  rcases he with ⟨i, hi, l, hl, rfl⟩ | ⟨j, hj, l, hl, rfl⟩
  · -- state slots
    cases hs with
    | i0 R hR => exact copyS_plain h (fun p _ => by kfl) hi hl rfl
    | i1 R hR => exact copyS_plain h (fun p _ => by kfl) hi hl rfl
    | qp R hR dr p hdr hp =>
      exact q_copyS h hR (by omega) (fun i => by simp only [sWord, qState]; rfl) hi hl
    | qd R hR dr hdr =>
      exact q_copyS h hR (by omega) (fun i => by
        simp only [sWord, qState]; rw [show 8 * (dr + 1) + 0 = 8 * dr + 7 + 1 by omega]) hi hl
    | qf R hR => exact q_copyS h hR (by omega) (fun i => rfl) hi hl
    | ff R hR j hj => exact copyS_plain h (fun p _ => by kfl) hi hl rfl
    | fe R hR Y hY =>
      exact copyS_none h (fun p _ => by kfl)
        (by rw [zev_gCopy' h]; rfl) i l
    | pd Y hY => exact copyS_none h (fun p _ => rfl) (by rw [zev_gCopy' h]; rfl) i l
  · -- key / counter
    cases hs with
    | fe R hR Y hY =>
      exact copyK_none (by rw [zev_add, zev_gCopy' h, zev_sumP' h]; rfl) j l
    | pd Y hY => exact copyK_none (by rw [zev_add, zev_gCopy' h, zev_sumP' h]; rfl) j l
    | _ => exact copyK_same h (fun _ => rfl) hj hl

/-! ## Feed-forward -/

section
variable {Z : ZEnv} {R : Req} {j : Nat} {Y : Row} (h : HEnv Z (.f R j) Y) (hR : ReqOk R) (hj : j < 4)

theorem kflag_fF (x : Nat) : kflag (Row.f R j).kd (10 + x) = if x = j then 1 else 0 := by
  show (if 10 + x = 10 + j then 1 else 0) = _
  by_cases e : x = j
  · simp [e]
  · rw [if_neg (by omega), if_neg e]

include h hj in
theorem f_selF (f : Nat → Expr) : zev Z (E.sel colF 4 f) = zev Z (f j) :=
  zev_sel Z colF 4 f j hj (by rw [zF h hj, kflag_fF (R := R) j, if_pos rfl])
    (fun x hx hxj => by rw [zF h hx, kflag_fF (R := R) x, if_neg hxj])

include h hR hj in
theorem f_ffC {q : Nat} (hq : q < 8) : zev Z (ffC j q) = 0 := by
  obtain ⟨kk, l, hk, hl, rfl⟩ : ∃ kk l, kk < 4 ∧ l < 2 ∧ q = 2 * kk + l :=
    ⟨q / 2, q % 2, by omega, by omega, by omega⟩
  have hi : 4 * kk + j < 16 := by omega
  have := add_carry (st_lt hR 80 (4 * kk + j)) (init_lt hR (4 * kk + j)) hl
  simp only [ffC, show (2 * kk + l) / 2 = kk by omega, show (2 * kk + l) % 2 = l by omega,
    zev_addE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zS h hi hl,
    zev_initLimb h hR (fun _ => rfl) hi hl, zcin h hk hl, zC h hk hl, zX h (by omega : kk < 6) hl]
  simp only [sWord, xWord, cCell, if_pos hk, outW, fin] at this ⊢
  omega

end

theorem complete_cFF {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y) :
    ∀ e ∈ cFF, zev Z e = 0 := by
  intro e he
  unfold cFF at he
  simp only [List.mem_append, List.mem_map, List.mem_range] at he
  -- `F` rows
  have hFrow : ∀ R j, ReqOk R → j < 4 → X = .f R j → zev Z e = 0 := by
    intro R j hR hj hX
    subst hX
    rcases he with ⟨q, hq, rfl⟩ | ⟨kk, hk, rfl⟩
    · rw [f_selF h hj]; exact f_ffC h hR hj hq
    · rw [zev_mul, zev_sub, zev_sumF' h]
      have : kflag (Row.f R j).kd 10 + kflag (Row.f R j).kd 11 + kflag (Row.f R j).kd 12 +
          kflag (Row.f R j).kd 13 = 1 := by
        rw [show (10 : Nat) = 10 + 0 from rfl, show (11 : Nat) = 10 + 1 from rfl,
          show (12 : Nat) = 10 + 2 from rfl, show (13 : Nat) = 10 + 3 from rfl,
          kflag_fF, kflag_fF, kflag_fF, kflag_fF]
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
      rw [this]; simp
  -- other rows: no `F` flag, no multiplicity
  have hother : (∀ x, x < 4 → kflag X.kd (10 + x) = 0) → (∀ kk, mflag X kk = 0) → zev Z e = 0 := by
    intro hF hM
    rcases he with ⟨q, hq, rfl⟩ | ⟨kk, hk, rfl⟩
    · exact selF_zero h hF _
    · exact zmul0 (by rw [zM h hk, hM]) _
  cases hs with
  | ff R hR j hj => exact hFrow R j hR (by omega) rfl
  | fe R hR Y hY => exact hFrow R 3 hR (by decide) rfl
  | pd Y hY => exact hother (fun _ _ => rfl) (fun _ => rfl)
  | i0 R hR => exact hother (fun _ _ => by kfl) (fun _ => rfl)
  | i1 R hR => exact hother (fun _ _ => by kfl) (fun _ => rfl)
  | qp R hR dr p hdr hp => exact hother (fun x hx => by kfl) (fun _ => rfl)
  | qd R hR dr hdr => exact hother (fun x hx => by kfl) (fun _ => rfl)
  | qf R hR => exact hother (fun x hx => by kfl) (fun _ => rfl)

end ZkFormal.Chacha.Complete
