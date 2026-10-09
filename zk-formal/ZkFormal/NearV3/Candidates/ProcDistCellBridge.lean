import ZkFormal.NearV3.Candidates.ProcDistShardSuccess
namespace ZkFormal.NearV3.Candidates.ProcDistCellBridge
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor

def event (a:CellAcc) : ProcDistEventRow.Acc := (a.2.2.2.1,a.2.2.1,a.2.2.2.2)
def sender (I:Input)(R:Run)(i:Nat) := (sortByKey (fun s=>if cntS R.n I.allowed s=0 then 0 else R.fin.sb[s]!/cntS R.n I.allowed s) (List.range R.n))[i]!
def receiver (I:Input)(R:Run)(j:Nat) := (sortByKey (fun r=>if cntR R.n I.allowed r=0 then 0 else R.fin.rb[r]!/cntR R.n I.allowed r) (List.range R.n))[j]!

private theorem set_self {α:Type}[Inhabited α](a:Array α)(i:Nat) : a.set! i a[i]! = a := by
  by_cases hi:i<a.size
  · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds_def,hi,getElem!_pos a i hi]
  · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds_def,hi]

theorem step (I:Input)(R:Run)(i j:Nat)(a:CellAcc)(e:ProcDistEventRow.Acc)
    (h:ProcDistEventRow.step R.n I.allowed (sender I R i) (receiver I R j) (event a)=.ok (.yield e)) :
    ∃b,cellStep I R i j a=.ok (.yield b) ∧ event b=e := by
  unfold ProcDistEventRow.step at h
  dsimp only [event] at h
  by_cases ha:I.allowed[sender I R i*R.n+receiver I R j]! = true
  · simp only [ha,ite_true,Bool.true_eq] at h
    split at h
    · cases h
    · rename_i hz
      have hs:1≤a.2.2.2.2.1 ∧ 1≤(a.2.2.2.1[receiver I R j]!).1 := by
        simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at hz
        omega
      simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
      subst e
      unfold cellStep
      dsimp [sender,receiver,ProcDistShardSuccess.order,ProcDistShardSuccess.avg] at ha hs ⊢
      simp only [ha,hs.1,hs.2,check,bind,Except.bind,pure,Except.pure,decide_true,Bool.true_and,Bool.true_eq,ite_true,ite_false,Bool.false_eq_true]
      exact ⟨_,rfl,rfl⟩
  · simp [ha,pure,Except.pure] at h
    subst e
    unfold cellStep
    dsimp [sender,receiver,ProcDistShardSuccess.order,ProcDistShardSuccess.avg] at ha ⊢
    simp only [ha,pure,Except.pure,Bool.false_eq_true,ite_false,Nat.sub_zero]
    refine ⟨_,rfl,?_⟩
    dsimp only [event]
    congr 1
    exact set_self _ _
theorem loop (I:Input)(R:Run)(i:Nat)(xs:List Nat)(a:CellAcc)(e:ProcDistEventRow.Acc)
    (h:ProcDistEventRow.row R.n I.allowed (sender I R i) (xs.map (receiver I R)) (event a)=.ok e) :
    ∃b,forIn xs a (cellStep I R i)=.ok b ∧ event b=e := by
  induction xs generalizing a with
  | nil=>simp only [ProcDistEventRow.row,List.map_nil,List.forIn_nil,pure,Except.pure,Except.ok.injEq] at h
         exact ⟨a,rfl,h⟩
  | cons j xs ih=>
    simp only [ProcDistEventRow.row,List.map_cons,List.forIn_cons] at h
    cases he:ProcDistEventRow.step R.n I.allowed (sender I R i) (receiver I R j) (event a) with
    | error err=>simp only [he,bind,Except.bind] at h;cases h
    | ok o=>
      cases o with
      | done z=>
        unfold ProcDistEventRow.step at he
        simp only [bind,Except.bind,pure,Except.pure] at he
        repeat first | cases he | split at he
      | yield z=>
        obtain ⟨b,hb,hbe⟩:=step I R i j a z he
        simp only [he,bind,Except.bind] at h
        obtain ⟨out,ho,hoe⟩:=ih b (by simpa only [hbe,ProcDistEventRow.row] using h)
        exact ⟨out,by simpa only [List.forIn_cons,hb,bind,Except.bind] using ho,hoe⟩
end ZkFormal.NearV3.Candidates.ProcDistCellBridge
