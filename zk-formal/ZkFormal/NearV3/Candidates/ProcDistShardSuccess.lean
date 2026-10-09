import ZkFormal.NearV3.Candidates.ProcDistGeneratorFactor
namespace ZkFormal.NearV3.Candidates.ProcDistShardSuccess
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor

def avg (I:Input)(R:Run)(sd x:Nat) : Nat :=
  if sd=0 then (if cntS R.n I.allowed x=0 then 0 else R.fin.sb[x]!/cntS R.n I.allowed x)
  else (if cntR R.n I.allowed x=0 then 0 else R.fin.rb[x]!/cntR R.n I.allowed x)
def order (I:Input)(R:Run)(sd:Nat) := sortByKey (avg I R sd) (List.range R.n)
def key (I:Input)(R:Run)(sd i:Nat) :=
  avg I R sd (order I R sd)[i]!*64+(order I R sd)[i]!

theorem step (I:Input)(R:Run)(sd i:Nat)(s:ShardAcc)(h:s.2.2≤key I R sd i) :
    ∃u,shardStep I R sd i s=.ok (.yield u) ∧ u.2.2=key I R sd i+1 := by
  unfold key order avg at h ⊢
  unfold shardStep
  by_cases hd:sd=0
  all_goals simp only [hd,ite_true,ite_false] at h ⊢
  all_goals simp only [check,h,decide_true,ite_true,bind,Except.bind,pure,Except.pure]
  all_goals exact ⟨_,rfl,rfl⟩

theorem loop (I:Input)(R:Run)(sd:Nat)(xs:List Nat)(s:ShardAcc)
    (hord:xs.Pairwise (fun i j=>key I R sd i<key I R sd j))
    (h:∀i∈xs,s.2.2≤key I R sd i) :
    ∃u,forIn xs s (shardStep I R sd)=.ok u := by
  induction xs generalizing s with
  | nil=>exact ⟨s,rfl⟩
  | cons i xs ih=>
    obtain ⟨u,hu,hkey⟩:=step I R sd i s (h i (by simp))
    obtain ⟨out,hout⟩:=ih u (List.pairwise_cons.mp hord).2 (by
      intro j hj
      rw [hkey]
      have hh:=(List.pairwise_cons.mp hord).1 j hj
      omega)
    exact ⟨out,by simpa only [List.forIn_cons,hu,bind,Except.bind] using hout⟩

theorem key_sorted (I:Input)(R:Run)(sd:Nat)(hn:R.n≤64) :
    (List.range R.n).Pairwise (fun i j=>key I R sd i<key I R sd j) := by
  have hs:=sortByKey_range_sorted (avg I R sd) R.n hn
  have hl:(order I R sd).length=R.n := by
    exact (sortByKey_perm _ _).length_eq.trans List.length_range
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hi':i<(order I R sd).length:=by simpa [hl] using hi
  have hj':j<(order I R sd).length:=by simpa [hl] using hj
  have hh:=hs.rel_getElem_of_lt hi' hj' hij
  simpa only [key,List.getElem_range,List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hi',List.getElem?_eq_getElem hj',Option.getD_some,
    KeyLt,sortKey] using hh

theorem side (I:Input)(R:Run)(sd:Nat)(s:Array (Array Nat)×List Cmp)(hn:R.n≤64) :
    ∃u,shardSide I R sd s=.ok (.yield u) := by
  obtain ⟨out,ho⟩:=loop I R sd (List.range R.n) (s.1,s.2,0) (key_sorted I R sd hn)
    (fun _ _=>Nat.zero_le _)
  exact ⟨(out.1,out.2.1),by simp only [shardSide,ho,bind,Except.bind,pure,Except.pure]⟩
end ZkFormal.NearV3.Candidates.ProcDistShardSuccess
