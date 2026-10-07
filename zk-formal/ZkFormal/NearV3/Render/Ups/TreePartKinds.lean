import ZkFormal.NearV3.Render.Ups.PositionedPart

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def nativeNodeType : PTrie→Nat
  | .hash _ => 4
  | .leaf .. => 0
  | .ext .. => 1
  | .branch none .. => 2
  | .branch (some _) .. => 3

def nativeKindTypes : UKind→List Nat
  | .RLP | .MVL | .NLF => [0]
  | .RDE | .MVE | .WEX | .PT => [1]
  | .RBR | .RBV => [3]
  | .RDB | .RBI | .SPB => [2,3]

def TreeRun.KindTypes (run : TreeRun) : Prop :=
  ∀ part∈run.parts,nativeNodeType part.output∈nativeKindTypes part.kind

theorem kindTypes_push {run : TreeRun} (h : run.KindTypes) (part : TreePart)
    (hp : nativeNodeType part.output∈nativeKindTypes part.kind) : (pushPart run part).KindTypes := by
  intro p hm
  simp only [pushPart,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm|rfl
  exact h p hm
  exact hp

theorem leafSplitRun_kindTypes (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).KindTypes := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [TreeRun.KindTypes,terminalRun,wrapRun,pushPart,wrapExt,newLeaf,nativeNodeType,nativeKindTypes]

theorem extSplitRun_kindTypes (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).KindTypes := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,TreeRun.KindTypes,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [TreeRun.KindTypes,terminalRun,wrapRun,pushPart,wrapExt,newLeaf,nativeNodeType,nativeKindTypes]

mutual
/-- Every actual runtime part has the node type required by its operation. -/
theorem traceUpsert_kindTypes : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.KindTypes
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [TreeRun.KindTypes,terminalRun,nativeKindTypes,nativeNodeType,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_kindTypes k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_kindTypes k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          apply kindTypes_push (traceUpsert_kindTypes c _ v inner hr)
          cases k <;> simp [nativeNodeType,nativeKindTypes,UpsSpec.qRDE]
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [TreeRun.KindTypes,terminalRun,nativeNodeType,nativeKindTypes]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      apply kindTypes_push (traceKids_kindTypes _ _ cs n key v inner hr)
      cases bv <;> cases inner.inserted <;> simp [nativeNodeType,nativeKindTypes]

theorem traceKids_kindTypes : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → run.inner.KindTypes
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [TreeRun.KindTypes,terminalRun,nativeNodeType,nativeKindTypes,newLeaf]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_kindTypes c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_kindTypes source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_kindTypes source wholeKey rest n key v inner hr
end
end ZkFormal.NearV3.Render.UpsGen
