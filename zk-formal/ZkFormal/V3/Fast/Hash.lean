import ArenaCore.SHA256Fast
import NearSpec.Outcome

/-!
# Fast compiled SHA-256 for the v3 verifier's native part (A5, candidate side)

`ArenaCore.SHA256Fast` registers `@[csimp] sha256 = sha256Fast` (kernel-proved). A `csimp`
lemma changes only code compiled *after* it is in scope, and the pinned `NearSpec` /
`NearSpecV3` modules do not import it. So the functions the native verifier calls are
re-stated here with identical bodies (compiled with the fast hash) and redirected by
`@[csimp]` lemmas proved by `rfl` (or induction for the recursive ones). Statements and
proofs see only the specification functions.
-/

namespace ZkFormal.V3.Fast

open NearSpec

/-- `NearSpec.sha256` is an `abbrev` of `ArenaCore.sha256`, but it is compiled as its own
symbol (in `NearSpec.SHA256`, without the fast path), and call sites compile to that symbol;
so it needs its own redirection. -/
@[csimp] theorem nearSpec_sha256_csimp : @NearSpec.sha256 = @ArenaCore.sha256Fast := by
  funext m
  exact congrFun ArenaCore.sha256_eq_sha256Fast m

def merkleLevelF : List Bytes → List Bytes
  | a :: b :: rest => sha256 (a ++ b) :: merkleLevelF rest
  | l => l

theorem merkleLevel_eq_F : @merkleLevel = @merkleLevelF := by
  funext l
  induction l using merkleLevel.induct with
  | case1 a b rest ih => simp [merkleLevel, merkleLevelF, ih]
  | case2 l h => cases l with
    | nil => rfl
    | cons a t => cases t with
      | nil => rfl
      | cons b r => exact absurd rfl (h a b r)

@[csimp] theorem merkleLevel_csimp : @merkleLevel = @merkleLevelF := merkleLevel_eq_F

def merkleFoldF : Nat → List Bytes → Bytes
  | _, [] => zeroHash
  | _, [x] => x
  | 0, x :: _ => x
  | n + 1, l => merkleFoldF n (merkleLevel l)

theorem merkleFold_eq_F : @merkleFold = @merkleFoldF := by
  funext n l
  induction n generalizing l with
  | zero => cases l with
    | nil => rfl
    | cons a t => cases t <;> rfl
  | succ n ih => cases l with
    | nil => rfl
    | cons a t => cases t with
      | nil => rfl
      | cons b r => simp only [merkleFold, merkleFoldF, ih]

@[csimp] theorem merkleFold_csimp : @merkleFold = @merkleFoldF := merkleFold_eq_F

def merkleRootF (leaves : List Bytes) : Bytes := merkleFold leaves.length leaves

@[csimp] theorem merkleRoot_csimp : @merkleRoot = @merkleRootF := rfl

end ZkFormal.V3.Fast
