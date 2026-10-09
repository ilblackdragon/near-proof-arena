import ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
import ZkFormal.NearV3.Sched.Complete.MemHonest
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryChains
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem append (g : Gen.Seg) (v w : Nat) (os : List Gen.MOp) (o : Gen.MOp)
    (h : OpsOk g v w os)
    (ho : OpOk g (match os.getLast? with | some a=>a.v | none=>v)
      (match os.getLast? with | some a=>a.w | none=>w) o) :
    OpsOk g v w (os++[o]) := by
  induction os generalizing v w with
  | nil=>exact ⟨ho,True.intro⟩
  | cons a os ih=>
    refine ⟨h.1,ih a.v a.w h.2 ?_⟩
    cases os with
    | nil=>exact ho
    | cons b os=>
      cases he:(b::os).getLast? with
      | none=>simp_all
      | some z=>simpa only [List.getLast?_cons_cons,he] using ho

/-- Per-index chains retain the actual segment metadata and initial values. -/
def Chains (gs : Nat→Gen.Seg) (logs : Array (Array Gen.MOp)) : Prop :=
  ∀i,i<logs.size→OpsOk (gs i) (gs i).v0 (gs i).w0 logs[i]!.toList

theorem modify (gs : Nat→Gen.Seg) (logs : Array (Array Gen.MOp)) (i : Nat) (o : Gen.MOp)
    (h : Chains gs logs)
    (ho : i<logs.size→OpOk (gs i)
      (ProcActualMemoryFinal.lastValue Gen.MOp.v (gs i).v0 logs[i]!)
      (ProcActualMemoryFinal.lastValue Gen.MOp.w (gs i).w0 logs[i]!) o) :
    Chains gs (logs.modify i (·.push o)) := by
  intro j hj
  have hj' : j<logs.size := by simpa using hj
  rw [getElem!_pos (logs.modify i (·.push o)) j hj,Array.getElem_modify]
  split
  · rename_i he
    subst j
    have hh:=append (gs i) (gs i).v0 (gs i).w0 logs[i]!.toList o (h i hj') (ho hj')
    simpa only [getElem!_pos logs i hj',Array.toList_push] using hh
  · simpa only [getElem!_pos logs j hj'] using h j hj'

theorem empty (gs : Nat→Gen.Seg) (n : Nat) : Chains gs (Array.replicate n #[]) := by
  intro i hi
  have hi' : i<n := by simpa using hi
  simp [getElem!_pos (Array.replicate n (#[] : Array Gen.MOp)) i hi,hi',OpsOk]
end ZkFormal.NearV3.Candidates.ProcActualMemoryChains
