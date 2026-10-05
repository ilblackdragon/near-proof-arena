import Conformance.AirJson
import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import ArenaCore.SHA256Fast

/-!
`np-lean-eval <air.json> <seed>` — differential test of constraint
evaluation (DESIGN.md §5.1, "constraint polynomials from Lean and from Rust
are compared at random points"). Every column (current and next row), public
input and selector is replaced by a pseudo-random extension element
`decodeChal(sha256("np-eval" ‖ le32 seed ‖ u8 kind ‖ le32 t ‖ le32 i))`
(kinds: 0 cur, 1 next, 2 pub, 3 first, 4 last, 5 trans), and every entry of
`allConstraints` is evaluated with `Expr.evalWith` over `K`. Output: one line
per (table, constraint): `t i l0 … l7`. Rust: `npudr eval-random`.
-/

open Conformance ZkFormal ZkFormal.Stark ZkFormal.Algebra ZkFormal.Air ArenaCore Lean.Grind

attribute [local instance] Semiring.natCast

def rnd (seed kind t i : Nat) : Fp8 :=
  decodeChal (F := Fp) (sha256 (Bytes.ofString "np-eval" ++ Bytes.leN 4 seed ++ [UInt8.ofNat kind]
    ++ Bytes.leN 4 t ++ Bytes.leN 4 i))

def envFor (seed t : Nat) : Env Fp8 :=
  { ofNat := fun n => (n : Fp8), add := (· + ·), mul := (· * ·), neg := (- ·)
    col := fun c nx => rnd seed (if nx then 1 else 0) t c
    pub := fun i => rnd seed 2 t i
    isFirst := rnd seed 3 t 0, isLast := rnd seed 4 t 0, isTransition := rnd seed 5 t 0 }

def main (args : List String) : IO UInt32 := do
  match args with
  | [airP, seedS] =>
    let A ← match parseAirChecked (← IO.FS.readFile airP) with
      | .ok (A, _) => pure A
      | .error e => IO.eprintln s!"np-lean-eval: {e}"; return 2
    let seed := seedS.toNat!
    for (T, t) in A.tables.zipIdx do
      for (e, i) in T.allConstraints.zipIdx do
        let v := e.evalWith (envFor seed t)
        let ls := (StarkField.limbs (F := Fp) v).map (StarkField.toNat (K := Fp8))
        IO.println s!"{t} {i} {" ".intercalate (ls.map toString)}"
    return 0
  | _ => IO.eprintln "usage: np-lean-eval <air.json> <seed>"; return 2
