import ZkFormal.Udr.Statements

/-!
# ZkFormal.Udr.Compose — L3 results from the `…Stmt` obligations

Everything here is proved (no `sorry`) from the statements of
`ZkFormal.Udr.Statements` taken as hypotheses.
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

/-- **Strong line lemma for interleaved RS codes at the unique-decoding radius**
(`2e + D ≤ n`): at most `3n + 2e + 1` bad challenges, for any column type `J`. -/
theorem strong_line_rs2 (hBW : RsGapStmt) {K : Type} [Field K] (xs : Nat → K) (n D e : Nat)
    (hD : D ≤ n) (hxs : Distinct xs n) (he : 2 * e + D ≤ n) (J : Type)
    (u0 u1 : Word J K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong (rsInterleaved xs n D hD hxs J) e u0 u1 z) ≤ 3 * n + 2 * e + 1 := by
  have hgap := gap_interleave (rsCode xs n D hD hxs) (by omega) (by omega)
    (hBW K xs n D e hD hxs he) J
  have := strong_of_gap (rsInterleaved xs n D hD hxs J) (by omega) hgap u0 u1 Ks hKs
  rwa [Nat.max_eq_left (by omega)] at this

/-- Scalar RS version (`J = Unit` gives words of the scalar code itself). -/
theorem strong_line_rs2_scalar (hBW : RsGapStmt) {K : Type} [Field K] (xs : Nat → K) (n D e : Nat)
    (hD : D ≤ n) (hxs : Distinct xs n) (he : 2 * e + D ≤ n)
    (u0 u1 : Word Unit K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong (rsCode xs n D hD hxs) e u0 u1 z) ≤ 3 * n + 2 * e + 1 := by
  have := strong_of_gap (rsCode xs n D hD hxs) (by omega) (hBW K xs n D e hD hxs he) u0 u1 Ks hKs
  rwa [Nat.max_eq_left (by omega)] at this

/-- **FRI query-phase bound.** With good challenges, if `f 0` is not `e 0`-close
to the layer-0 RS code, fewer than `nn 0 - e 0` query positions pass. -/
theorem fri_far_pass_lt (hF : FriStmt) {K : Type} [Field K] (S : Fri.Setup K) (R : Fri.Run K)
    (e : Nat → Nat) (he : ∀ i, i < S.r → e i ≤ 2 * e (i + 1)) (hg : Fri.GoodChallenges S R e)
    (hfar : ¬ ∃ w, (S.code 0 (Nat.zero_le _)).mem w ∧ dist (S.nn 0) (R.f 0) w ≤ e 0) :
    count (List.range (S.nn 0)) (Fri.passK S R S.r) < S.nn 0 - e 0 := by
  refine Nat.lt_of_not_le fun hle => hfar ?_
  obtain ⟨p, hp⟩ := hF K S R e he hg hle
  refine ⟨fun j _ => ev (S.DD 0) p (S.xs 0 j), ⟨p, fun _ _ => rfl⟩, ?_⟩
  have hc := count_add_count_not (List.range (S.nn 0)) (Fri.passK S R S.r)
  rw [List.length_range] at hc
  refine Nat.le_trans (count_mono_mem _ (F := fun j => ¬ Fri.passK S R S.r j) ?_) (by omega)
  intro j hj hne hpass
  exact hne (by funext u; cases u; exact hp j (List.mem_range.mp hj) hpass)

end ZkFormal.Udr
