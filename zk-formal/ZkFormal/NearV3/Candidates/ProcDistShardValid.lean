import ZkFormal.NearV3.Candidates.ProcDistGeneratorSuccess
import ZkFormal.NearV3.Sched.Complete.Cmp
namespace ZkFormal.NearV3.Candidates.ProcDistShardValid
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistGeneratorFactor ProcDistShardSuccess Complete

def CmpsOk (cs:List Cmp) := ∀q∈cs,CmpOk q
def Budget (R:Run) := (∀i:Nat,R.fin.sb[i]!≤4500000) ∧ (∀i:Nat,R.fin.rb[i]!≤4500000)
def Inv (s:ShardAcc) := CmpsOk s.2.1 ∧ s.2.2<2^29

theorem append (cs:List Cmp)(x y:Nat)(h:CmpsOk cs)(hx:x<2^29)(hy:y<2^29) :
    CmpsOk (cs++[(x,y,if y≤x then 1 else 0)]) := by
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · exact h q hq
  · have hq:=List.mem_singleton.mp hq
    subst q
    exact ⟨hx,hy,rfl⟩

theorem key_bound (I:Input)(R:Run)(sd i:Nat)(hn:R.n≤64)(hi:i<R.n)(hb:Budget R) :
    key I R sd i+1<2^29 := by
  have hl:(order I R sd).length=R.n:=(sortByKey_perm _ _).length_eq.trans List.length_range
  have hm:(order I R sd)[i]!∈order I R sd := by
    rw [getElem!_pos _ i (by omega)]
    exact List.getElem_mem _
  have hx:(order I R sd)[i]!<R.n:=List.mem_range.mp ((sortByKey_perm _ _).mem_iff.mp hm)
  have hq:avg I R sd (order I R sd)[i]!≤4500000 := by
    unfold avg
    split <;> split
    · omega
    · exact Nat.le_trans (Nat.div_le_self _ _) (hb.1 _)
    · omega
    · exact Nat.le_trans (Nat.div_le_self _ _) (hb.2 _)
  unfold key
  omega

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem step_valid (I:Input)(R:Run)(sd i:Nat)(hn:R.n≤64)(hi:i<R.n)(hb:Budget R)
    (s:ShardAcc)(hs:Inv s)(out:ForInStep ShardAcc)(h:shardStep I R sd i s=.ok out) :
    ExceptLoop.StepInv Inv out := by
  have hk:=key_bound I R sd i hn hi hb
  unfold key order at hk
  unfold avg at hk
  unfold shardStep at h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  constructor
  · apply append _ _ _ hs.1
    · by_cases hd:sd=0 <;> simpa [hd] using (Nat.lt_of_succ_lt hk)
    · exact hs.2
  · by_cases hd:sd=0 <;> simpa [hd] using hk

theorem side_valid (I:Input)(R:Run)(sd:Nat)(hn:R.n≤64)(hb:Budget R)
    (s:Array (Array Nat)×List Cmp)(hs:CmpsOk s.2)(out:ForInStep (Array (Array Nat)×List Cmp))
    (h:shardSide I R sd s=.ok out) : ExceptLoop.StepInv (fun s=>CmpsOk s.2) out := by
  unfold shardSide at h
  obtain ⟨u,hu,h⟩:=bind_ok h
  cases h
  have hi:=ExceptLoop.invariant (List.range R.n) (shardStep I R sd) Inv
    (fun i hi a ha out ho=>step_valid I R sd i hn (List.mem_range.mp hi) hb a ha out ho)
    (s.1,s.2,0) u ⟨hs,show 0<2^29 from by decide⟩ hu
  exact hi.1
end ZkFormal.NearV3.Candidates.ProcDistShardValid
