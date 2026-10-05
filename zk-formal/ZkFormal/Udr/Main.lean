import ZkFormal.Udr.Compose
import ZkFormal.Udr.BW
import ZkFormal.Udr.Fri
import ZkFormal.Udr.GrandProduct

/-!
# ZkFormal.Udr.Main — the L3 results, unconditional

The `Compose` theorems instantiated with the proved statements.
-/

namespace ZkFormal.Udr

open ArenaCore.Security Lean.Grind

/-- **Strong line lemma, interleaved Reed–Solomon codes, radius `d/2`**
(`2e + D ≤ n`): at most `3n + 2e + 1` bad challenges, for any column type. -/
theorem strong_line_rs {K : Type} [Field K] (xs : Nat → K) (n D e : Nat)
    (hD : D ≤ n) (hxs : Distinct xs n) (he : 2 * e + D ≤ n) (J : Type)
    (u0 u1 : Word J K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong (rsInterleaved xs n D hD hxs J) e u0 u1 z) ≤ 3 * n + 2 * e + 1 :=
  strong_line_rs2 rsGap xs n D e hD hxs he J u0 u1 Ks hKs

/-- Scalar version. -/
theorem strong_line_rs_scalar {K : Type} [Field K] (xs : Nat → K) (n D e : Nat)
    (hD : D ≤ n) (hxs : Distinct xs n) (he : 2 * e + D ≤ n)
    (u0 u1 : Word Unit K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong (rsCode xs n D hD hxs) e u0 u1 z) ≤ 3 * n + 2 * e + 1 :=
  strong_line_rs2_scalar rsGap xs n D e hD hxs he u0 u1 Ks hKs

/-- **FRI query-phase bound** (UDR): with good challenges and a far input word,
fewer than `nn 0 - e 0` positions pass all checks. -/
theorem fri_query_bound {K : Type} [Field K] (S : Fri.Setup K) (R : Fri.Run K)
    (e : Nat → Nat) (he : ∀ i, i < S.r → e i ≤ 2 * e (i + 1) + 1) (hg : Fri.GoodChallenges S R e)
    (hfar : ¬ ∃ w, (S.code 0 (Nat.zero_le _)).mem w ∧ dist (S.nn 0) (R.f 0) w ≤ e 0) :
    count (List.range (S.nn 0)) (Fri.passK S R S.r) < S.nn 0 - e 0 :=
  fri_far_pass_lt fri S R e he hg hfar

end ZkFormal.Udr
