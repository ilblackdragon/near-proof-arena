import ZkFormal.NearV3.Render.Ups.TreePlanKinds

namespace ZkFormal.NearV3.Render.UpsGen
open UpsRows

/-- The source depth of a bottom-up part. All terminal parts share the terminal
source; each subsequent ancestor part moves up one revealed node. -/
def planDepth (terminalDepth terminalParts index : Nat) : Nat :=
  terminalDepth-(index+1-terminalParts)

/-- MEMD refers to the preceding part for an ancestor/wrapper, and to the first
moved part for a split branch that owns a moved child. -/
def planMemoryIndex (kind index : Nat) : Nat :=
  if kind=0 ∨ kind=1 ∨ kind=9 ∨ kind=11 then index else if kind=10 then 1 else 0

/-- Set the depth and local child link independently of record-ID allocation. -/
def withPlanPosition (terminalDepth terminalParts index : Nat) (part : UpsPartI) : UpsPartI :=
  {part with
    pdep := planDepth terminalDepth terminalParts index
    jm := planMemoryIndex part.kind index}

theorem planDepth_terminal (depth nt k : Nat) (hk : k<nt) : planDepth depth nt k=depth := by
  simp [planDepth,show k+1-nt=0 by omega]

theorem planDepth_upper (depth nt k : Nat) (hk : k<nt+depth) (hu : nt≤k) :
    planDepth depth nt k+(k+1-nt)=depth := by unfold planDepth; omega

theorem planDepth_root (depth nt : Nat) (ht : 0<nt) : planDepth depth nt (nt+depth-1)=0 := by
  unfold planDepth; omega

theorem planMemoryIndex_down (kind k : Nat) (hk : kind=0 ∨ kind=1 ∨ kind=9 ∨ kind=11) :
    planMemoryIndex kind k=k := by simp [planMemoryIndex,hk]

theorem planMemoryIndex_split (k : Nat) : planMemoryIndex 10 k=1 := by simp [planMemoryIndex]

/-- Exact native depth makes all terminal/upper depth conditions hold after allocation. -/
theorem allocated_plan_depth {t : NearSpec.PTrie} {key : List Nat} {v : NearSpec.Bytes}
    {run : TreeRun} (hr : traceUpsert t key v=some run) (k : Nat) (hk : k<run.parts.length)
    (part : UpsPartI) :
    (k<(termPlan run.terminal run.matched).length →
      (withPlanPosition (fdepth t key-1) (termPlan run.terminal run.matched).length k part).pdep=
        fdepth t key-1) ∧
    ((termPlan run.terminal run.matched).length≤k →
      (withPlanPosition (fdepth t key-1) (termPlan run.terminal run.matched).length k part).pdep+
        (k+1-(termPlan run.terminal run.matched).length)=fdepth t key-1) := by
  have hn := traceUpsert_nQ hr
  exact ⟨planDepth_terminal _ _ k,fun hu => planDepth_upper _ _ k (by omega) hu⟩
end ZkFormal.NearV3.Render.UpsGen
