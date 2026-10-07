import ZkFormal.NearV3.Render.Ups.NativeWalkBitmap

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- Actual proper sources in top-down order, excluding empty-extension pass-throughs. -/
def nativePathNodes (run : TreeRun) : List PTrie :=
  ((run.parts.filter (fun p => descendKind p.kind)).reverse.map TreePart.source)++[run.terminalSource]

def nativePathEdgeKind (run : TreeRun) (level : Nat) : Nat :=
  match (nativePathNodes run)[level]? with
  | some (.branch ..) => EK_DOWN
  | _ => EK_KEY

theorem nativePathEdgeKind_bound (run : TreeRun) (level : Nat) : nativePathEdgeKind run level≤1 := by
  unfold nativePathEdgeKind
  cases (nativePathNodes run)[level]? with
  | none => simp [EK_KEY]
  | some node => cases node <;> simp [EK_DOWN,EK_KEY]

theorem nativePathNodes_ids (recordId : PTrie→Nat) (run : TreeRun) :
    (nativePathNodes run).map recordId=sourceLevelIds recordId run := by
  simp [nativePathNodes,sourceLevelIds,List.map_map,Function.comp_def]

/-- The terminal edge's actual target. Value and resolved-child record allocation
remain explicit functions to be connected to authenticated stored views. -/
def nativeTerminalTarget (valueId : Slot→Nat) (resolvedId : PTrie→Nat) (run : TreeRun)
    (self : Nat) : Nat×Nat :=
  if run.terminal=.LP ∨ run.terminal=.BR then
    match run.terminalSource with
    | .leaf _ slot _ | .branch (some slot) _ _ => (valueId slot,0)
    | _ => (0,0)
  else if run.terminal=.LSa then (self,run.matched)
  else
    match run.terminalSource with
    | .ext key child _ =>
      if run.matched+1=key.length then
        match child with
        | .hash _ => (self,key.length)
        | _ => (resolvedId child,0)
      else (self,run.matched+1)
    | _ => (self,run.matched+1)
end ZkFormal.NearV3.Render.UpsGen
