import ZkFormal.NearV3.Candidates.ProcActualMemoryTagSegments
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryComparisonInventory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualMemoryTags
abbrev Cmps:=ProcActualMemoryScan.Cmps

def opRequests (tp : Nat) (o : Gen.MOp) : List (Nat×Nat×Nat) :=
  [(o.t,tp+1,1)] ++ if o.op=OP_GRANT then [(o.vin,o.inc,b2n o.sf)] else []
def requests : Nat→List Gen.MOp→List (Nat×Nat×Nat)
  | _,[]=>[]
  | tp,o::os=>opRequests tp o++requests o.t os
def finalTime : Nat→List Gen.MOp→Nat
  | tp,[]=>tp
  | _,o::os=>finalTime o.t os

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩
private theorem checked (p : Bool) (msg : String) (u : Unit) (h:check p msg=.ok u) : p=true := by
  cases p <;> simp [check] at h ⊢

theorem step (o : Gen.MOp) (s : Cmps×Nat) (out : ForInStep (Cmps×Nat)) (ho:OpTag o)
    (h:ProcActualMemoryScan.actualStep o s=.ok out) :
    ∃u,out=.yield u ∧ u.1.toList=s.1.toList++opRequests s.2 o ∧ u.2=o.t := by
  unfold ProcActualMemoryScan.actualStep at h
  obtain ⟨v,hcheck,h⟩:=bind_ok h
  have ht:s.2<o.t := by simpa using checked _ _ v hcheck
  have hle:s.2+1≤o.t := by omega
  simp only [pure,Except.pure] at h
  split at h
  · rename_i hg
    have hg':o.op=OP_GRANT := by simpa using hg
    refine ⟨_,(Except.ok.inj h).symm,?_,rfl⟩
    simp [opRequests,hg',hle,ho.2 hg',List.append_assoc]
  · rename_i hg
    have hg':o.op≠OP_GRANT := by simpa using hg
    refine ⟨_,(Except.ok.inj h).symm,?_,rfl⟩
    simp [opRequests,hg',hle]

theorem ops (os : List Gen.MOp) (s out : Cmps×Nat) (ho:∀o∈os,OpTag o)
    (h:forIn os s ProcActualMemoryScan.actualStep=.ok out) :
    out.1.toList=s.1.toList++requests s.2 os ∧ out.2=finalTime s.2 os := by
  induction os generalizing s with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp [requests,finalTime]
  | cons o os ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualMemoryScan.actualStep o s with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok u=>
      obtain ⟨u,rfl,hu,ht⟩:=step o s u (ho o (by simp)) he
      simp only [he,bind,Except.bind] at h
      obtain ⟨hc,hf⟩:=ih u (fun x hx=>ho x (by simp [hx])) h
      simp [hc,hf,hu,ht,requests,finalTime,List.append_assoc]

theorem segment (g : Gen.Seg) (cs : Cmps) (out : ForInStep Cmps)
    (hg:ProcActualMemoryTagSegments.SegTag g) (h:ProcActualMemoryScan.segmentStep g cs=.ok out) :
    ∃u,out=.yield u ∧ u.toList=cs.toList++requests 0 g.ops := by
  rw [ProcActualMemoryScan.segment_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  exact ⟨s.1,(Except.ok.inj h).symm,(ops g.ops (cs,0) s hg hs).1⟩

theorem segments (gs : List Gen.Seg) (cs out : Cmps) (hg:∀g∈gs,ProcActualMemoryTagSegments.SegTag g)
    (h:forIn gs cs ProcActualMemoryScan.segmentStep=.ok out) :
    out.toList=cs.toList++gs.flatMap (fun g=>requests 0 g.ops) := by
  induction gs generalizing cs with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp
  | cons g gs ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualMemoryScan.segmentStep g cs with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok u=>
      obtain ⟨u,rfl,hu⟩:=segment g cs u (hg g (by simp)) he
      simp only [he,bind,Except.bind] at h
      rw [ih u (fun x hx=>hg x (by simp [hx])) h,hu]
      simp [List.append_assoc]
end ZkFormal.NearV3.Candidates.ProcActualMemoryComparisonInventory
