import ZkFormal.NearV3.Render.Ups.TreePartKinds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem treeNode_type {t : PTrie} {node : NodeV3} (he : treeNode t=some node) :
    nodeTypeCode node=nativeNodeType t := by
  cases t with
  | hash => simp [treeNode] at he
  | leaf => simp [treeNode] at he; subst node; rfl
  | ext => simp [treeNode] at he; subst node; rfl
  | branch value kids mem =>
    simp [treeNode] at he; subst node
    cases value <;> rfl

theorem encodeTreePart_type {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) : Q.ty=nativeNodeType part.output := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q
  exact treeNode_type hd

/-- The node-type fields of PartOk, proved independently of physical allocation. -/
structure PartTypeFacts (Q : UpsPartI) : Prop where
  ty : Q.ty<4
  tyBr : Q.kind=0 ∨ Q.kind=3 ∨ Q.kind=5 ∨ Q.kind=10 → 2≤Q.ty
  tyBV : Q.kind=3 ∨ Q.kind=4 → Q.ty=3
  tyExt : Q.kind=1 ∨ Q.kind=7 ∨ Q.kind=9 ∨ Q.kind=11 → Q.ty=1
  tyLeaf : Q.kind=2 ∨ Q.kind=6 ∨ Q.kind=8 → Q.ty=0

/-- Actual constructor dispatch supplies the full node-type block of PartOk. -/
theorem trace_encoded_typeFacts {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) {part : TreePart} (hp : part∈run.parts)
    {base Q : UpsPartI} (he : encodeTreePart base part=some Q) : PartTypeFacts Q := by
  have hs := traceUpsert_kindTypes t key v run hr part hp
  have ht := encodeTreePart_type he
  have hk := encodeTreePart_kind he
  constructor <;> cases hc : part.kind <;> simp_all [nativeKindTypes,UKind.ix] <;> omega
end ZkFormal.NearV3.Render.UpsGen
