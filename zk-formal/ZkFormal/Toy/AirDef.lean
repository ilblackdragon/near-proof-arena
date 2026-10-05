import ZkFormal.Air.Basic

/-!
# ZkFormal.Toy.AirDef — the M2 toy AIR (definition only; part of the verifier model closure)

One table of width 4 (bits `b₀..b₃` of a root `s = b₀ + 2b₁ + 4b₂ + 8b₃`), heights
`2..16`, constraints `bᵢ·(bᵢ − 1) = 0` and `s·s − pub₀ = 0`.  Semantics in `Toy.Air`.
-/

namespace ZkFormal.Toy

open ZkFormal.Air

def bit (i : Nat) : Expr := .col i false

def isBool (e : Expr) : Expr := .mul e (.add e (.neg (.const 1)))

def root : Expr :=
  .add (bit 0) (.add (.mul (.const 2) (bit 1)) (.add (.mul (.const 4) (bit 2)) (.mul (.const 8) (bit 3))))

def toyTable : Air.Table where
  width := 4
  constraints := [isBool (bit 0), isBool (bit 1), isBool (bit 2), isBool (bit 3),
    .add (.mul root root) (.neg (.pub 0))]
  interactions := []
  maxLog := 4

def toyAir : Air := ⟨[toyTable], 0, 1⟩

end ZkFormal.Toy
