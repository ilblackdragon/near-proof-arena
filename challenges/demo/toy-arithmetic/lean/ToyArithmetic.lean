/-
DEMO ONLY — NOT NEAR SEMANTICS.

Relation for the `demo-toy-arithmetic` plumbing challenge. It exists so the
pipeline (upload -> build -> formal check -> conformance -> benchmark ->
decision) can be exercised end to end before the spec lane publishes the
real NEAR slice. Nothing admitted under this relation says anything about
NEAR, nearcore or any chain.
-/
namespace Arena.Demo.ToyArithmetic

/-- A request is a pair of 64-bit words. -/
structure Request where
  a : UInt64
  b : UInt64

/-- The public claim: the request together with its wrapping product. -/
structure Claim where
  a : UInt64
  b : UInt64
  c : UInt64

/-- `ToyRelation claim ()` holds iff `c = a * b mod 2^64`. The witness is unit. -/
def ToyRelation (cl : Claim) (_w : Unit) : Prop := cl.c = cl.a * cl.b

/-- The unique expected claim for a request (what the judge's oracle computes). -/
def expectedClaim (r : Request) : Claim := ⟨r.a, r.b, r.a * r.b⟩

theorem expectedClaim_sound (r : Request) : ToyRelation (expectedClaim r) () := rfl

end Arena.Demo.ToyArithmetic
