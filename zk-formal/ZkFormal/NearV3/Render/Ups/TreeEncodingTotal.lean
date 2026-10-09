import ZkFormal.NearV3.Render.Ups.TreePartEncoding
import ZkFormal.NearV3.Render.Ups.TreePlan

/-! Successful native traces produce serializable source/output nodes for every part.
This supplies executable encoding existence without a per-part success premise. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

def TreeRun.NodeParts (run : TreeRun) : Prop :=
  ∀ part∈run.parts, isNode part.source=true ∧ isNode part.output=true

theorem nodeParts_push {run : TreeRun} (h : run.NodeParts) (part : TreePart)
    (hs : isNode part.source=true) (ho : isNode part.output=true) : (pushPart run part).NodeParts := by
  intro p hp
  simp only [pushPart,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp|rfl
  exact h p hp
  exact ⟨hs,ho⟩

theorem leafSplitRun_nodeParts (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).NodeParts := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [TreeRun.NodeParts,terminalRun,wrapRun,pushPart,isNode,newLeaf,wrapExt]

theorem extSplitRun_nodeParts (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).NodeParts := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,TreeRun.NodeParts,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [TreeRun.NodeParts,terminalRun,wrapRun,pushPart,isNode,newLeaf,wrapExt]

mutual
theorem traceUpsert_nodeParts : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.NodeParts
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [TreeRun.NodeParts,terminalRun,isNode,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_nodeParts k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_nodeParts k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          exact nodeParts_push (traceUpsert_nodeParts c (key.drop k.length) v inner hr) _ rfl rfl
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run; simp [TreeRun.NodeParts,terminalRun,isNode]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact nodeParts_push (traceKids_nodeParts (.branch bv cs m) (n::key) cs n key v inner rfl hr) _ rfl rfl
theorem traceKids_nodeParts : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), isNode source=true →
    traceKids source wholeKey cs n key v=some run → run.inner.NodeParts
  | _, _, .nil, _, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, hs, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simpa [TreeRun.NodeParts,terminalRun,isNode,newLeaf] using hs
  | source, wholeKey, .some c rest, 0, key, v, run, _, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_nodeParts c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, hs, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_nodeParts source wholeKey rest n key v inner hs hr
  | source, wholeKey, .some c rest, n+1, key, v, run, hs, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_nodeParts source wholeKey rest n key v inner hs hr
end

theorem treeNode_exists {t : PTrie} (h : isNode t=true) : ∃ node, treeNode t=some node := by
  cases t <;> simp_all [isNode,treeNode]

theorem encodeTreePart_exists (base : UpsPartI) {part : TreePart}
    (hs : isNode part.source=true) (ho : isNode part.output=true) : ∃ Q, encodeTreePart base part=some Q := by
  obtain ⟨src,hsrc⟩ := treeNode_exists hs
  obtain ⟨dst,hdst⟩ := treeNode_exists ho
  simp [encodeTreePart,hsrc,hdst]

/-- Every emitted runtime part can be encoded, for any subsequently chosen allocator metadata. -/
theorem traceUpsert_part_encoding {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (h : traceUpsert t key v=some run) {part : TreePart} (hp : part∈run.parts) (base : UpsPartI) :
    ∃ Q, encodeTreePart base part=some Q ∧ Q.kind=part.kind.ix := by
  obtain ⟨hs,ho⟩ := traceUpsert_nodeParts t key v run h part hp
  obtain ⟨Q,hQ⟩ := encodeTreePart_exists base hs ho
  exact ⟨Q,hQ,encodeTreePart_kind hQ⟩
/-- Encode every emitted part with the allocator metadata at its global part index. -/
def encodeTreeParts (base : Nat → UpsPartI) : Nat → List TreePart → Option (List UpsPartI)
  | _, [] => some []
  | offset, part::rest => do
    let Q ← encodeTreePart (base offset) part
    let Qs ← encodeTreeParts base (offset+1) rest
    return Q::Qs

theorem encodeTreeParts_total (base : Nat → UpsPartI) : ∀ (parts : List TreePart) (offset : Nat),
    (∀ part∈parts,isNode part.source=true ∧ isNode part.output=true) →
    ∃ Qs, encodeTreeParts base offset parts=some Qs ∧
      Qs.map UpsPartI.kind=parts.map (fun p => p.kind.ix) ∧ Qs.length=parts.length
  | [], _, _ => ⟨[],rfl,rfl,rfl⟩
  | part::rest, offset, hn => by
    obtain ⟨hs,ho⟩ := hn part (by simp)
    obtain ⟨Q,hQ⟩ := encodeTreePart_exists (base offset) hs ho
    obtain ⟨Qs,hQs,hk,hl⟩ := encodeTreeParts_total base rest (offset+1)
      (fun p hp => hn p (by simp [hp]))
    refine ⟨Q::Qs,?_,?_,by simpa using hl⟩
    · simp [encodeTreeParts,hQ,hQs]
    · simp [encodeTreePart_kind hQ,hk]

/-- Native success constructs an encoded sequence with the exact terminal/ancestor plan.
Allocator metadata remains a parameter; no encoding-success or AIR predicate is assumed. -/
theorem upsert_encoded_witness {t result : PTrie} {key : List Nat} {v : Bytes}
    (h : t.upsert key v=some result) (base : Nat → UpsPartI) :
    ∃ run Qs, traceUpsert t key v=some run ∧ run.output=result ∧ run.Planned ∧
      encodeTreeParts base 0 run.parts=some Qs ∧
      Qs.map UpsPartI.kind=run.parts.map (fun p => p.kind.ix) ∧ Qs.length=run.parts.length := by
  obtain ⟨run,hr,ho,hp⟩ := upsert_planned_witness h
  obtain ⟨Qs,hQs,hk,hl⟩ := encodeTreeParts_total base run.parts 0 (traceUpsert_nodeParts t key v run hr)
  exact ⟨run,Qs,hr,ho,hp,hQs,hk,hl⟩

end ZkFormal.NearV3.Render.UpsGen
