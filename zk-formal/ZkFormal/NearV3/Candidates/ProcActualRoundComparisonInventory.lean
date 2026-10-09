import ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
namespace ZkFormal.NearV3.Candidates.ProcActualRoundComparisonInventory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev Cmps:=ProcActualMemoryScan.Cmps

def entryRequest (rd : Gen.RoundD) (i : Nat) : Nat×Nat×Nat :=
  (if i+1=rd.entries.length then rd.T else rd.entries[i+1]!.ts,rd.entries[i]!.ts+1,1)
def requests (rd : Gen.RoundD) : List (Nat×Nat×Nat) :=
  (if rd.K≠0 then [(rd.Kq,rd.K+1,1)] else [])++(List.range rd.entries.length).map (entryRequest rd)

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩
private theorem checked (p : Bool) (msg : String) (u : Unit) (h:check p msg=.ok u) : p=true := by
  cases p <;> simp [check] at h ⊢

theorem entry (rd : Gen.RoundD) (i : Nat) (cs : Cmps) (out : ForInStep Cmps)
    (h:ProcActualBucketComparisons.step rd i cs=.ok out) :
    ∃u,out=.yield u ∧ u.toList=cs.toList++[entryRequest rd i] := by
  unfold ProcActualBucketComparisons.step at h
  dsimp only at h
  obtain ⟨v,hcheck,h⟩:=bind_ok h
  have ht:=checked _ _ v hcheck
  have hle:rd.entries.toArray[i]!.ts+1≤(if i+1=rd.entries.toArray.size then rd.T else rd.entries.toArray[i+1]!.ts) := by
    have hlt:=of_decide_eq_true ht
    omega
  refine ⟨_,(Except.ok.inj h).symm,?_⟩
  simp [entryRequest]
  simpa using hle

theorem entries (rd : Gen.RoundD) (xs : List Nat) (cs out : Cmps)
    (h:forIn xs cs (ProcActualBucketComparisons.step rd)=.ok out) :
    out.toList=cs.toList++xs.map (entryRequest rd) := by
  induction xs generalizing cs with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp
  | cons i xs ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualBucketComparisons.step rd i cs with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok u=>
      obtain ⟨u,rfl,hu⟩:=entry rd i cs u he
      simp only [he,bind,Except.bind] at h
      rw [ih u h,hu]
      simp [List.append_assoc]

theorem round (rd : Gen.RoundD) (cs : Cmps) (out : ForInStep Cmps)
    (h:ProcActualComparisonFactor.roundStep rd cs=.ok out) :
    ∃u,out=.yield u ∧ u.toList=cs.toList++requests rd := by
  unfold ProcActualComparisonFactor.roundStep at h
  split at h
  · rename_i hk
    obtain ⟨v,hcheck,h⟩:=bind_ok h
    have ht:rd.K<rd.Kq:=by simpa using checked _ _ v hcheck
    have hle:rd.K+1≤rd.Kq:=by omega
    have hk':rd.K≠0:=by simpa using hk
    obtain ⟨s,hs,h⟩:=bind_ok h
    refine ⟨s,(Except.ok.inj h).symm,?_⟩
    rw [entries _ _ _ s hs]
    simp [requests,hk',hle,List.append_assoc]
  · rename_i hk
    have hk':rd.K=0:=by simpa using hk
    obtain ⟨s,hs,h⟩:=bind_ok h
    refine ⟨s,(Except.ok.inj h).symm,?_⟩
    rw [entries _ _ _ s hs]
    simp [requests,hk']

theorem rounds (rs : List Gen.RoundD) (cs out : Cmps)
    (h:forIn rs cs ProcActualComparisonFactor.roundStep=.ok out) :
    out.toList=cs.toList++rs.flatMap requests := by
  induction rs generalizing cs with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp
  | cons rd rs ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualComparisonFactor.roundStep rd cs with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok u=>
      obtain ⟨u,rfl,hu⟩:=round rd cs u he
      simp only [he,bind,Except.bind] at h
      rw [ih u h,hu]
      simp [List.append_assoc]
end ZkFormal.NearV3.Candidates.ProcActualRoundComparisonInventory
