import ZkFormal.NearV3.Candidates.ProcDistCellBridge
namespace ZkFormal.NearV3.Candidates.ProcDistGridBridge
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistGeneratorFactor ProcDistCellBridge

theorem indexed_list {α:Type}[Inhabited α](xs:List α) :
    (List.range xs.length).map (fun i=>xs[i]!)=xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem?_eq_getElem hi']

def receivers (I:Input)(R:Run) := sortByKey
  (fun r=>if cntR R.n I.allowed r=0 then 0 else R.fin.rb[r]!/cntR R.n I.allowed r) (List.range R.n)
def senders (I:Input)(R:Run) := sortByKey
  (fun s=>if cntS R.n I.allowed s=0 then 0 else R.fin.sb[s]!/cntS R.n I.allowed s) (List.range R.n)

theorem receiver_list (I:Input)(R:Run) : (List.range R.n).map (receiver I R)=receivers I R := by
  have hl:(receivers I R).length=R.n := (sortByKey_perm _ _).length_eq.trans List.length_range
  change (List.range R.n).map (fun i=>(receivers I R)[i]!)=receivers I R
  rw [←hl]
  exact indexed_list _
theorem sender_list (I:Input)(R:Run) : (List.range R.n).map (sender I R)=senders I R := by
  have hl:(senders I R).length=R.n := (sortByKey_perm _ _).length_eq.trans List.length_range
  change (List.range R.n).map (fun i=>(senders I R)[i]!)=senders I R
  rw [←hl]
  exact indexed_list _

def event (a:GridAcc) := (a.2.2.2,a.2.2.1)
def eventStep (I:Input)(R:Run)(s:Nat)(a:Array Endpoint×Array Nat) :
    Except String (ForInStep (Array Endpoint×Array Nat)) := do
  let out ← ProcDistEventRow.row R.n I.allowed s (receivers I R)
    (a.1,a.2,(cntS R.n I.allowed s,R.fin.sb[s]!))
  return .yield (out.1,out.2.1)

def eventOuter (I:Input)(R:Run)(ss:List Nat)(a:Array Endpoint×Array Nat) :=
  forIn ss a (eventStep I R)

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem step (I:Input)(R:Run)(i:Nat)(a:GridAcc)(e:Array Endpoint×Array Nat)
    (h:eventStep I R (sender I R i) (event a)=.ok (.yield e)) :
    ∃b,gridStep I R i a=.ok (.yield b) ∧ event b=e := by
  unfold eventStep at h
  obtain ⟨z,hz,h⟩:=bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
  subst e
  unfold gridStep
  obtain ⟨out,ho,he⟩:=ProcDistCellBridge.loop I R i (List.range R.n)
    (a.1.push (setAll Dist.width [(Dist.act,1),(Dist.kGH,1),(Dist.tau,R.tau),(Dist.nn,R.n),
      (Dist.a,i),(Dist.b,255),(Dist.r,sender I R i),(Dist.N2,cntS R.n I.allowed (sender I R i)),
      (Dist.L2,R.fin.sb[sender I R i]!),(Dist.dlrg,1)]),a.2.1,a.2.2.1,a.2.2.2,(cntS R.n I.allowed (sender I R i),R.fin.sb[sender I R i]!)) z
    (by simpa only [receiver_list,ProcDistCellBridge.event,event] using hz)
  refine ⟨(out.1,out.2.1,out.2.2.1,out.2.2.2.1),?_,?_⟩
  · change (forIn (List.range R.n) _ (cellStep I R i) >>= _)=_
    dsimp only [sender] at ho
    dsimp only
    rw [ho]
    rfl
  · exact congrArg (fun a:ProcDistEventRow.Acc=>(a.1,a.2.1)) he

theorem loop (I:Input)(R:Run)(xs:List Nat)(a:GridAcc)(e:Array Endpoint×Array Nat)
    (h:eventOuter I R (xs.map (sender I R)) (event a)=.ok e) :
    ∃b,forIn xs a (gridStep I R)=.ok b ∧ event b=e := by
  induction xs generalizing a with
  | nil=>simp only [eventOuter,List.map_nil,List.forIn_nil,pure,Except.pure,Except.ok.injEq] at h
         exact ⟨a,rfl,h⟩
  | cons i xs ih=>
    simp only [eventOuter,List.map_cons,List.forIn_cons] at h
    cases hs:eventStep I R (sender I R i) (event a) with
    | error er=>simp only [hs,bind,Except.bind] at h;cases h
    | ok o=>
      cases o with
      | done z=>
        unfold eventStep at hs
        obtain ⟨_,_,hs⟩:=bind_ok hs
        cases hs
      | yield z=>
        obtain ⟨b,hb,he⟩:=step I R i a z hs
        simp only [hs,bind,Except.bind] at h
        obtain ⟨out,ho,hoe⟩:=ih b (by simpa only [eventOuter,he] using h)
        exact ⟨out,by simpa only [List.forIn_cons,hb,bind,Except.bind] using ho,hoe⟩
end ZkFormal.NearV3.Candidates.ProcDistGridBridge
