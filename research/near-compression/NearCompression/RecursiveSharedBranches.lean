import NearCompression.RecursiveSharedSource
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def recursiveSharedAddPair (left right a b : Nat) : List (TerminalDAGNode K) :=
  [.binary .add left a,.binary .add right b]

omit [Field K] in
theorem recursive_shared_add_pair_acyclic (start left right a b : Nat)
    (hl : left<start) (hr : right<start) (ha : a<start) (hb : b<start) :
    TerminalDAGAcyclic start (recursiveSharedAddPair (K:=K) left right a b) := by
  simp only [recursiveSharedAddPair,TerminalDAGAcyclic,TerminalNodeBefore,and_true]
  grind

theorem recursive_shared_add_pair_value (start left right a b : Nat) (inputs previous : Nat → K)
    (hl : left<start) (hr : right<start) (ha : a<start) (hb : b<start) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b)
    result start=previous left+previous a ∧ result (start+1)=previous right+previous b := by
  dsimp only
  have ac := recursive_shared_add_pair_acyclic (K:=K) start left right a b hl hr ha hb
  have h0 := terminal_dag_node_equation inputs previous (recursiveSharedAddPair left right a b) start ac 0 (by simp [recursiveSharedAddPair])
  have h1 := terminal_dag_node_equation inputs previous (recursiveSharedAddPair left right a b) start ac 1 (by simp [recursiveSharedAddPair])
  simp only [recursiveSharedAddPair,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero,terminalNodeValue,gkrGateValue] at h0 h1
  have pl := terminal_dag_preserves_earlier inputs previous (recursiveSharedAddPair left right a b) start left hl
  have pr := terminal_dag_preserves_earlier inputs previous (recursiveSharedAddPair left right a b) start right hr
  have pa := terminal_dag_preserves_earlier inputs previous (recursiveSharedAddPair left right a b) start a ha
  have pb := terminal_dag_preserves_earlier inputs previous (recursiveSharedAddPair left right a b) start b hb
  change terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b) start=
    terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b) left+
    terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b) a at h0
  change terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b) (start+1)=
    terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b) right+
    terminalDAGRun inputs start previous (recursiveSharedAddPair left right a b) b at h1
  grind

/-- Projection reuses the selected accumulator index twice; emits no copy node. -/
def recursiveSharedBranchSide (start zeroSlot : Nat) (branch : RecursiveSourceBranch) (side : Bool) : Nat :=
  recursiveSharedLaneIndex start zeroSlot (branch.projection.getD side) branch.laneCount

def recursiveSharedBranchNodes (start zeroSlot even odd : Nat) (branch : RecursiveSourceBranch) : List (TerminalDAGNode K) :=
  recursiveSharedLaneProgram start branch.slotStart zeroSlot zeroSlot branch.laneCount ++
    recursiveSharedAddPair even odd (recursiveSharedBranchSide start zeroSlot branch false)
      (recursiveSharedBranchSide start zeroSlot branch true)

omit [Field K] in
theorem recursive_shared_branch_length (start zeroSlot even odd : Nat) (branch : RecursiveSourceBranch) :
    (recursiveSharedBranchNodes (K:=K) start zeroSlot even odd branch).length=7*branch.laneCount+2 := by
  simp only [recursiveSharedBranchNodes,List.length_append,recursive_shared_lane_program_length,
    recursiveSharedAddPair,List.length_cons,List.length_nil]

theorem recursive_shared_branch_acyclic (start zeroSlot even odd : Nat) (branch : RecursiveSourceBranch)
    (hz : zeroSlot<start) (he : even<start) (ho : odd<start) :
    TerminalDAGAcyclic start (recursiveSharedBranchNodes (K:=K) start zeroSlot even odd branch) := by
  apply recursive_shared_acyclic_append
  · exact recursive_shared_lane_program_acyclic start branch.slotStart zeroSlot zeroSlot branch.laneCount hz hz
  · rw [recursive_shared_lane_program_length]
    apply recursive_shared_add_pair_acyclic
    · omega
    · omega
    · exact recursive_shared_lane_index_bound start zeroSlot branch.laneCount _ hz
    · exact recursive_shared_lane_index_bound start zeroSlot branch.laneCount _ hz

/-- Whole branch, with shared zeroSlot, shared beta, exact projected index reuse,
and two emitted query-accumulator additions. -/
theorem recursive_shared_branch_value (start zeroSlot even odd : Nat) (branch : RecursiveSourceBranch)
    (inputs previous : Nat → K) (hz : zeroSlot<start) (he : even<start) (ho : odd<start)
    (zv : previous zeroSlot=0) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedBranchNodes start zeroSlot even odd branch)
    result (start+7*branch.laneCount)=previous even+recursiveSourceBranchValue inputs branch false ∧
    result (start+7*branch.laneCount+1)=previous odd+recursiveSourceBranchValue inputs branch true := by
  dsimp only
  rw [recursiveSharedBranchNodes,recursive_shared_run_append,recursive_shared_lane_program_length]
  let laneNodes:=recursiveSharedLaneProgram (K:=K) start branch.slotStart zeroSlot zeroSlot branch.laneCount
  let middle:=terminalDAGRun inputs start previous laneNodes
  have lane := recursive_shared_lane_program_value start branch.slotStart zeroSlot zeroSlot branch.laneCount inputs previous hz hz
  dsimp only at lane
  rw [zv] at lane
  have sides (side : Bool) : middle (recursiveSharedBranchSide start zeroSlot branch side)=recursiveSourceBranchValue inputs branch side := by
    unfold recursiveSharedBranchSide recursiveSourceBranchValue
    cases hs : branch.projection.getD side
    · exact lane.1
    · exact lane.2
  have pe : middle even=previous even := terminal_dag_preserves_earlier inputs previous laneNodes start even he
  have po : middle odd=previous odd := terminal_dag_preserves_earlier inputs previous laneNodes start odd ho
  have result := recursive_shared_add_pair_value (start+7*branch.laneCount) even odd
    (recursiveSharedBranchSide start zeroSlot branch false) (recursiveSharedBranchSide start zeroSlot branch true)
    inputs middle (by omega) (by omega)
    (recursive_shared_lane_index_bound start zeroSlot branch.laneCount _ hz)
    (recursive_shared_lane_index_bound start zeroSlot branch.laneCount _ hz)
  dsimp only at result
  rw [pe,po,sides false,sides true] at result
  exact result

def recursiveSharedBranchesCost : List RecursiveSourceBranch → Nat
  | [] => 0
  | branch::rest => 7*branch.laneCount+2+recursiveSharedBranchesCost rest

def recursiveSharedBranchesProgram (start zeroSlot even odd : Nat) : List RecursiveSourceBranch → List (TerminalDAGNode K)
  | [] => []
  | branch::rest => recursiveSharedBranchNodes start zeroSlot even odd branch ++
      recursiveSharedBranchesProgram (start+7*branch.laneCount+2) zeroSlot
        (start+7*branch.laneCount) (start+7*branch.laneCount+1) rest

def recursiveSharedBranchesIndex (start previous : Nat) (side : Bool) : List RecursiveSourceBranch → Nat
  | [] => previous
  | branch::rest => recursiveSharedBranchesIndex (start+7*branch.laneCount+2)
      (start+7*branch.laneCount+(if side then 1 else 0)) side rest

omit [Field K] in
theorem recursive_shared_branches_length (start zeroSlot even odd : Nat) (branches : List RecursiveSourceBranch) :
    (recursiveSharedBranchesProgram (K:=K) start zeroSlot even odd branches).length=recursiveSharedBranchesCost branches := by
  induction branches generalizing start even odd with
  | nil => rfl
  | cons branch rest ih => simp only [recursiveSharedBranchesProgram,List.length_append,recursive_shared_branch_length,ih,recursiveSharedBranchesCost]

theorem recursive_shared_branches_index_bound (start previous : Nat) (side : Bool)
    (branches : List RecursiveSourceBranch) (hp : previous<start) :
    recursiveSharedBranchesIndex start previous side branches<start+recursiveSharedBranchesCost branches := by
  induction branches generalizing start previous with
  | nil => simpa only [recursiveSharedBranchesIndex,recursiveSharedBranchesCost,Nat.add_zero] using hp
  | cons branch rest ih =>
    have h := ih (start+7*branch.laneCount+2) (start+7*branch.laneCount+(if side then 1 else 0)) (by split <;> omega)
    simp only [recursiveSharedBranchesIndex,recursiveSharedBranchesCost]
    omega

theorem recursive_shared_branches_acyclic (start zeroSlot even odd : Nat) (branches : List RecursiveSourceBranch)
    (hz : zeroSlot<start) (he : even<start) (ho : odd<start) :
    TerminalDAGAcyclic start (recursiveSharedBranchesProgram (K:=K) start zeroSlot even odd branches) := by
  induction branches generalizing start even odd with
  | nil => trivial
  | cons branch rest ih =>
    apply recursive_shared_acyclic_append
    · exact recursive_shared_branch_acyclic start zeroSlot even odd branch hz he ho
    · rw [recursive_shared_branch_length]
      simpa only [Nat.add_assoc] using ih (start+7*branch.laneCount+2)
        (start+7*branch.laneCount) (start+7*branch.laneCount+1) (by omega) (by omega) (by omega)

/-- Exact left-associated loop over all branches; projection preserves sharing. -/
theorem recursive_shared_branches_value (start zeroSlot even odd : Nat) (branches : List RecursiveSourceBranch)
    (inputs previous : Nat → K) (hz : zeroSlot<start) (he : even<start) (ho : odd<start)
    (zv : previous zeroSlot=0) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedBranchesProgram start zeroSlot even odd branches)
    result (recursiveSharedBranchesIndex start even false branches)=recursiveSourceQueryValue inputs false (previous even) branches ∧
    result (recursiveSharedBranchesIndex start odd true branches)=recursiveSourceQueryValue inputs true (previous odd) branches := by
  induction branches generalizing start even odd previous with
  | nil => exact ⟨rfl,rfl⟩
  | cons branch rest ih =>
    dsimp only
    rw [recursiveSharedBranchesProgram,recursive_shared_run_append,recursive_shared_branch_length]
    have step := recursive_shared_branch_value start zeroSlot even odd branch inputs previous hz he ho zv
    let middle:=terminalDAGRun inputs start previous (recursiveSharedBranchNodes start zeroSlot even odd branch)
    have mz : middle zeroSlot=0 := by
      unfold middle
      rw [terminal_dag_preserves_earlier inputs previous _ start zeroSlot hz]
      exact zv
    have next := ih (start+7*branch.laneCount+2) (start+7*branch.laneCount)
      (start+7*branch.laneCount+1) middle (by omega) (by omega) (by omega) mz
    dsimp only at step
    dsimp only [middle] at next
    rw [step.1,step.2] at next
    simpa only [recursiveSharedBranchesIndex,recursiveSourceQueryValue,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero,Nat.add_assoc] using next
end NearCompression
