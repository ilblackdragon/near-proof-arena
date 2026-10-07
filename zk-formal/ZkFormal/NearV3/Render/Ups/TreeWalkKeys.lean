import ZkFormal.NearV3.Render.Ups.TreeKeyTerminal

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Query nibbles consumed by a proper native ancestor, in source-node coordinates. -/
def partWalkKey (part : TreePart) : List Nat :=
  match part.kind,part.source with
  | .RDB,_ => [part.slot]
  | .RDE,.ext key _ _ => key
  | _,_ => []

/-- Concatenate proper source-node query segments, then the terminal query suffix. -/
def walkQuery (run : TreeRun) : List Nat :=
  ((run.parts.filter (fun p => descendKind p.kind)).reverse.flatMap partWalkKey)++run.terminalKey

theorem walkQuery_push (run : TreeRun) (part : TreePart) :
    walkQuery (pushPart run part)=(if descendKind part.kind then partWalkKey part else [])++walkQuery run := by
  by_cases h : descendKind part.kind=true <;>
    simp [walkQuery,pushPart,List.filter_append,List.reverse_append,List.flatMap_append,h,List.append_assoc]

theorem leafSplitRun_walkQuery (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    walkQuery (leafSplitRun k s m key v)=key := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [walkQuery,wrapRun,terminalRun,pushPart,descendKind]

theorem extSplitRun_walkQuery (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    walkQuery (extSplitRun k c m key v)=key := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,walkQuery,terminalRun,descendKind]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [walkQuery,terminalRun,wrapRun,pushPart,descendKind]

mutual
/-- The actual native ancestor keys concatenate to precisely the original query. -/
theorem traceUpsert_walkQuery : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → walkQuery run=key
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [walkQuery,terminalRun,descendKind]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_walkQuery k s m key v
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_walkQuery k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          rw [walkQuery_push,traceUpsert_walkQuery c _ v inner hc]
          have hk : k++key.drop k.length=key := by
            obtain ⟨rest,he⟩ := (isPrefix_iff k key).mp hp
            rw [he,List.drop_left]
          cases k <;> simpa [descendKind,partWalkKey] using hk
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> simp [walkQuery,terminalRun,descendKind]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      rw [walkQuery_push]
      have hi := traceKids_walkQuery (.branch bv cs m) (n::key) cs n key v inner hc
      cases he : inner.inserted <;> simpa [he,descendKind,partWalkKey] using hi

theorem traceKids_walkQuery : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    (if run.inserted then walkQuery run.inner=wholeKey else walkQuery run.inner=key)
  | _, _, .nil, _, _, _, _, hr => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [walkQuery,terminalRun,descendKind]
  | source, wholeKey, .some child rest, 0, key, v, run, hr => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_walkQuery child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_walkQuery source wholeKey rest n key v inner hc
  | source, wholeKey, .some child rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_walkQuery source wholeKey rest n key v inner hc
end
end ZkFormal.NearV3.Render.UpsGen
