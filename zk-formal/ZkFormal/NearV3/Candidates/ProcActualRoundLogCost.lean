import ZkFormal.NearV3.Candidates.ProcActualLogCost
namespace ZkFormal.NearV3.Candidates.ProcActualRoundLogCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualLogCost
abbrev EAcc := ProcActualReplayEntry.Acc
abbrev Acc := ProcActualReplayRound.Acc
def entries (a:EAcc) := a.2.2.2.2.2.2.2.2.2.2.size
def logs (a:Acc) := size a.2.2.2.2.1+size a.2.2.2.2.2.1+size a.2.2.2.2.2.2.1
def count (a:Acc) := ((ProcActualRoundTimes.rounds a).toList.map (fun rd=>rd.entries.length)).sum
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem entry_count (I:Input)(cv:Array CReq)(rd:Round)(sh:List Nat)(T x:Nat)
    (a:EAcc)(out:ForInStep EAcc)(h:ProcActualReplayEntry.step I cv rd sh T x a=.ok out) :
    ∃u,out=.yield u ∧ entries u=entries a+1 := by
  rcases a with ⟨sb,rb,aa,gg,l,s,r,p,used,gidx,es⟩
  unfold ProcActualReplayEntry.step at h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  simp only [pure,Except.pure] at h
  split at h <;> exact ⟨_,(Except.ok.inj h).symm,by simp [entries]⟩

theorem loop_count (I:Input)(cv:Array CReq)(rd:Round)(sh:List Nat)(T:Nat)
    (xs:List Nat)(a out:EAcc)(h:forIn xs a (ProcActualReplayEntry.step I cv rd sh T)=.ok out) :
    entries out=entries a+xs.length := by
  induction xs generalizing a with
  | nil=>simp only [List.forIn_nil] at h; cases h; simp
  | cons x xs ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualReplayEntry.step I cv rd sh T x a with
    | error e=>simp [he,bind,Except.bind] at h
    | ok s=>
      obtain ⟨u,rfl,hu⟩:=entry_count I cv rd sh T x a s he
      simp only [he,bind,Except.bind] at h
      rw [ih u h,hu]
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

set_option maxRecDepth 32768 in
theorem round (I:Input)(cv:Array CReq)(key:List Nat)(rd:Round)(a:Acc)(out:ForInStep Acc)
    (h:ProcActualReplayRound.step I cv key rd a=.ok out) :
    ∃u,out=.yield u ∧ logs u≤logs a+3*rd.bucket.length ∧
      count u=count a+rd.bucket.length ∧
      (ProcActualRoundTimes.rounds u).size=(ProcActualRoundTimes.rounds a).size+1 ∧ 1≤rd.bucket.length := by
  rcases a with ⟨sb,rb,aa,gg,l,s,r,p,bs,T,k,K,z,used,rs,idx⟩
  unfold ProcActualReplayRound.step at h
  dsimp only at h
  obtain ⟨_,hcheck,h⟩:=bind_ok h
  obtain ⟨shuffle,hshuffle,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨collected,_,h⟩:=bind_ok h
  obtain ⟨e,he,h⟩:=bind_ok h
  refine ⟨_,(Except.ok.inj h).symm,?_,?_,?_,?_⟩
  · simpa [logs,entrySize] using ProcActualLogCost.entries I cv rd shuffle.1 T (List.range rd.bucket.length) _ e he
  · have hc:=loop_count I cv rd shuffle.1 T (List.range rd.bucket.length) _ e he
    simp only [entries,List.length_range,Array.size_empty,Nat.zero_add] at hc
    simp [count,ProcActualRoundTimes.rounds,Array.toList_push,List.foldr_append,hc]
  · simp [ProcActualRoundTimes.rounds]
  · unfold check at hcheck
    split at hcheck
    · rename_i ht
      simp only [Bool.and_eq_true,decide_eq_true_eq] at ht
      exact ht.1
    · cases hcheck
theorem rounds (I:Input)(cv:Array CReq)(key:List Nat)(rs:List Round)(a out:Acc)
    (h:forIn rs a (ProcActualReplayRound.step I cv key)=.ok out) :
    logs out+3*count a≤logs a+3*count out ∧
    (ProcActualRoundTimes.rounds out).size+count a≤(ProcActualRoundTimes.rounds a).size+count out := by
  induction rs generalizing a with
  | nil=>simp only [List.forIn_nil] at h; cases h; exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | cons rd rs ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualReplayRound.step I cv key rd a with
    | error e=>simp [he,bind,Except.bind] at h
    | ok s=>
      obtain ⟨u,rfl,hl,hc,hr,hpos⟩:=round I cv key rd a s he
      simp only [he,bind,Except.bind] at h
      obtain ⟨hi,hj⟩:=ih u h
      constructor <;> omega

theorem reads (aa gg:Array Nat)(cv:Array CReq)(out:Array (Array Gen.MOp))(n:Nat)
    (h:forIn cv (Array.replicate n #[]) (ProcActualReplayFactor.readStep aa gg)=.ok out) :
    size out≤cv.size := by
  rw [←Array.forIn_toList] at h
  have hc:=ProcCodecComparisonCost.loop_cost _ _ size (fun _=>1) ?_ _ _ h
  · simpa [size,List.map_const',List.sum_replicate_nat] using hc
  · intro c hc s u hu
    exact ⟨_,(Except.ok.inj hu).symm,modify _ _ _⟩

theorem replay (I:Input)(cv:Array CReq)(rs:List Round)(out:Acc)
    (h:ProcActualReplayFactor.replay I cv rs=.ok out) :
    logs out≤cv.size+3*count out ∧ (ProcActualRoundTimes.rounds out).size≤count out := by
  unfold ProcActualReplayFactor.replay at h
  obtain ⟨ops,hop,h⟩:=bind_ok h
  have hr:=reads _ _ cv ops _ hop
  have hh:=rounds I cv _ rs _ out h
  simp [logs,count,ProcActualReplayInitial.initial,ProcActualRoundTimes.rounds,size] at hh hr ⊢
  exact ⟨by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcActualRoundLogCost
