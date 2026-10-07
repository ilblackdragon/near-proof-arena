import ZkFormal.NearV3.Render.Ups.Ok

/-! Semantic serialization inputs for the update table.  These describe the ordinary node
field sequence, not evaluations of AIR expressions.  They are additive to `InstOk`. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- Byte length of a field sequence. -/
def fieldsLen (sh : List (Nat × Nat)) : Nat := (sh.map Prod.snd).sum

/-- The canonical trie-node serialization as a sequence of typed fields.  The hex-prefix
length includes its flag byte.  A branch's child windows appear in bitmap order. -/
def nodeFields (ty hk children : Nat) : List (Nat × Nat) :=
  [(0, 1)] ++
  (if ty ≤ 1 then [(1, 4), (2, 1)] ++ (if 1 < hk then [(3, hk - 1)] else []) else []) ++
  (if ty = 0 ∨ ty = 3 then [(4, 4), (5, 32)] else []) ++
  (if 2 ≤ ty then [(6, 2)] else []) ++
  List.replicate children (7, 32) ++ [(8, 8)]

/-- Honest node serialization parameters, independent of polynomial constraints. -/
structure FieldsOk (Q : UpsPartI) : Prop where
  ty : Q.ty < 4
  prefixLength : Q.ty ≤ 1 → 1 ≤ Q.qhk
  /-- A leaf has no child windows; an extension has exactly one. -/
  leaf : Q.ty = 0 → nWin Q.shape = 0
  extension : Q.ty = 1 → nWin Q.shape = 1
  shape : Q.shape = nodeFields Q.ty Q.qhk (nWin Q.shape)
  bytes : Q.q.length = fieldsLen Q.shape
  nochild : Q.nochild = if nWin Q.shape = 0 then 1 else 0

end ZkFormal.NearV3.Render.UpsGen
