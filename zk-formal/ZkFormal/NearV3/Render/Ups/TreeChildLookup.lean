import ZkFormal.NearV3.Render.Ups.TreeRootSource

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

/-- Ordinary native child-slot lookup; no allocated record ids occur here. -/
def nativeChildAt : Kids → Nat → Option PTrie
  | .nil, _ => none
  | .none _, 0 => none
  | .some child _, 0 => some child
  | .none rest, n+1 => nativeChildAt rest n
  | .some _ rest, n+1 => nativeChildAt rest n

/-- An existing branch descent consumes the source at the actual selected child slot. -/
theorem traceKids_childSource (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun)
    (hr : traceKids source wholeKey cs n key v=some run) (hi : run.inserted=false) :
    run.inner.parts.getLast?.map TreePart.source=nativeChildAt cs n := by
  cases cs with
  | nil => simp [traceKids] at hr
  | none rest =>
    cases n with
    | zero => simp only [traceKids,Option.some.injEq] at hr; subst run; cases hi
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_childSource source wholeKey rest n key v inner hc hi
  | some child rest =>
    cases n with
    | zero =>
      cases hm : child.mem? with
      | none => simp [traceKids,hm] at hr
      | some cm =>
        cases hc : traceUpsert child key v with
        | none => simp [traceKids,hm,hc] at hr
        | some inner =>
          simp only [traceKids,hm,hc,Option.some.injEq] at hr
          subst run
          exact traceUpsert_rootSource hc
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_childSource source wholeKey rest n key v inner hc hi

termination_by cs

/-- Record ids used by the bottom-up branch chain refer to the same native child
selected by the top-down traversal. Authentication of the allocator remains separate. -/
theorem traceKids_childId (recordId : PTrie → Nat) (source : PTrie) (wholeKey : List Nat)
    (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun)
    (hr : traceKids source wholeKey cs n key v=some run) (hi : run.inserted=false) :
    run.inner.parts.getLast?.map (fun p => recordId p.source)=
      (nativeChildAt cs n).map recordId := by
  rw [←traceKids_childSource source wholeKey cs n key v run hr hi]
  simp only [Option.map_map,Function.comp_def]
end ZkFormal.NearV3.Render.UpsGen
