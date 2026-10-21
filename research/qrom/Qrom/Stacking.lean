import Mathlib

/-! Polynomial identities for the pinned backend's univariate-skip rotation.
These hold at arbitrary points. They do not prove Rust or NV trace semantics. -/
namespace Qrom.Stacking
variable {F : Type*} [CommRing F]

def eqCube : List F → List F → F
  | x :: xs, y :: ys => (x*y + (1-x)*(1-y)) * eqCube xs ys
  | _, _ => 1

def rotCube : List F → List F → F
  | x :: xs, y :: ys => x*(1-y)*eqCube xs ys + (1-x)*y*rotCube xs ys
  | _, _ => 1

def zeroWeight (x : List F) : F := (x.map (1 - ·)).prod
def oneWeight (x : List F) : F := x.prod

theorem eq_append (x y a b : List F) (h : x.length = y.length) :
    eqCube (x ++ a) (y ++ b) = eqCube x y * eqCube a b := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [eqCube]
  | cons v vs ih =>
    cases y with
    | nil => simp at h
    | cons w ws =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append, eqCube, ih ws h]
      ring

/-- High coordinates change only the low block's wraparound term. -/
theorem rot_append (x y a b : List F) (h : x.length = y.length) :
    rotCube (x ++ a) (y ++ b) =
      eqCube a b * rotCube x y + zeroWeight x * oneWeight y *
        (rotCube a b - eqCube a b) := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [rotCube, zeroWeight, oneWeight]
  | cons v vs ih =>
    cases y with
    | nil => simp at h
    | cons w ws =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append, rotCube, eq_append vs ws a b h, ih ws h,
        zeroWeight, oneWeight, List.map_cons, List.prod_cons]
      ring

/-- E = eq_D(u0, omega*r0), A = eq_D(u0,1), B = eq_D(omega*r0,1). -/
def prismRot (E A B : F) (x y : List F) : F :=
  E * eqCube x y + A * B * (rotCube x y - eqCube x y)

/-- Exact polynomial identity for the verifier correction. For an aligned
chunk a is its fixed high address; its first row's predecessor has weight
oneWeight y * rotCube a b. -/
theorem prism_chunk (E A B : F) (x y a b : List F)
    (h : x.length = y.length) :
    prismRot E A B (x ++ a) (y ++ b) =
      eqCube a b * prismRot E A B x y + B * A * zeroWeight x *
        (oneWeight y * rotCube a b - eqCube a b * oneWeight y) := by
  unfold prismRot
  rw [eq_append x y a b h, rot_append x y a b h]
  ring

theorem whole_column_delta (y : List F) :
    oneWeight y * rotCube ([] : List F) [] -
      eqCube ([] : List F) [] * oneWeight y = 0 := by
  simp [rotCube, eqCube]

/-- Little-endian subtraction of one, with wraparound. -/
def predecessor : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: predecessor bs

def embed (bs : List Bool) : List F := bs.map (fun b => if b then 1 else 0)

/-- The recursive rotation kernel at a Boolean source address is exactly
its predecessor's equality weight, including all-zero wraparound. -/
theorem rot_boolean (bs : List Bool) (y : List F) (h : bs.length = y.length) :
    rotCube (embed bs) y = eqCube (embed (predecessor bs)) y := by
  induction bs generalizing y with
  | nil => cases y <;> simp_all [embed, predecessor, rotCube, eqCube]
  | cons b bs ih =>
    cases y with
    | nil => simp at h
    | cons w ws =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b <;> simp [embed, predecessor, rotCube, eqCube, embed] at *
      exact congrArg (w * ·) (ih ws h)

/-- Corrected prism kernel with a Boolean high address, in the same form
as chunk_factors' predecessor weight. -/
theorem prism_chunk_address (E A B : F) (x y : List F) (bs : List Bool)
    (b : List F) (h : x.length = y.length) (hb : bs.length = b.length) :
    prismRot E A B (x ++ embed bs) (y ++ b) =
      eqCube (embed bs) b * prismRot E A B x y + B * A * zeroWeight x *
        (oneWeight y * eqCube (embed (predecessor bs)) b -
          eqCube (embed bs) b * oneWeight y) := by
  rw [prism_chunk E A B x y (embed bs) b h, rot_boolean bs b hb]

end Qrom.Stacking
#print axioms Qrom.Stacking.eq_append
#print axioms Qrom.Stacking.rot_append
#print axioms Qrom.Stacking.prism_chunk
#print axioms Qrom.Stacking.whole_column_delta
#print axioms Qrom.Stacking.rot_boolean
#print axioms Qrom.Stacking.prism_chunk_address
