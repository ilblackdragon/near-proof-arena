import ZkFormal.NearV3.Render.Ups.NativeProperEdges

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Native walk resolution skips exactly the empty extension nodes. -/
def resolveNative : PTrie→PTrie
  | .ext [] child _ => resolveNative child
  | t => t

def resolvedRecordId (recordId : PTrie→Nat) (t : PTrie) : Nat := recordId (resolveNative t)

theorem nativePathNodes_push (run : TreeRun) (p : TreePart) :
    nativePathNodes (pushPart run p)=(if descendKind p.kind then [p.source] else [])++nativePathNodes run := by
  by_cases h : descendKind p.kind=true <;>
    simp [nativePathNodes,pushPart,List.filter_append,List.reverse_append,h,List.append_assoc]

theorem leafSplitRun_pathNodes (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    nativePathNodes (leafSplitRun k s m key v)=[.leaf k s m] := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [nativePathNodes,wrapRun,terminalRun,pushPart,descendKind]

theorem extSplitRun_pathNodes (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    nativePathNodes (extSplitRun k c m key v)=[.ext k c m] := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,nativePathNodes,terminalRun,descendKind]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [nativePathNodes,terminalRun,wrapRun,pushPart,descendKind]

/-- The first actual source-level record is the runtime root after empty-extension resolution. -/
theorem traceUpsert_pathHead : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → (nativePathNodes run).head?=some (resolveNative t)
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [nativePathNodes,terminalRun,descendKind,resolveNative,he]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; rw [leafSplitRun_pathNodes]; rfl
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      rw [extSplitRun_pathNodes]
      cases k with
      | nil => simp [isPrefix] at hp
      | cons => rfl
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          rw [nativePathNodes_push]
          cases k with
          | nil => simpa [descendKind,resolveNative] using traceUpsert_pathHead c _ v inner hc
          | cons => simp [descendKind,resolveNative]
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> simp [nativePathNodes,terminalRun,descendKind,resolveNative]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      rw [nativePathNodes_push]
      cases hi : inner.inserted with
      | false => simp [hi,descendKind,resolveNative]
      | true =>
        have hin := (traceKids_inserted _ _ _ _ _ _ _ hc hi).2.2
        simp [hi,descendKind,hin,nativePathNodes,terminalRun,resolveNative]

/-- The first generated source ID is exactly the resolved native root ID. -/
theorem sourceLevelIds_resolvedRoot (recordId : PTrie→Nat) {t : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert t key v=some run) :
    (sourceLevelIds recordId run).getD 0 0=resolvedRecordId recordId t := by
  rw [←nativePathNodes_ids]
  have hh := traceUpsert_pathHead t key v run hr
  cases he : nativePathNodes run with
  | nil => simp [he] at hh
  | cons a rest =>
    simp only [he,List.head?_cons,Option.some.injEq] at hh
    simp [hh,resolvedRecordId]
end ZkFormal.NearV3.Render.UpsGen
