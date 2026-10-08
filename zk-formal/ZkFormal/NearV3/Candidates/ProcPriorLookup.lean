import ZkFormal.NearV3.Candidates.ProcActualInput
namespace ZkFormal.NearV3.Candidates.ProcPriorLookup
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler ZkFormal.NearV3.Sched
open ProcActualInput

/-- The actual native destination, retaining first-occurrence ID lookup. -/
def target (ids : List Nat) (r : LinkAllowance) : Option Nat :=
  match indexOf ids r.sender, indexOf ids r.receiver with
  | some s, some t => some (s*ids.length+t)
  | _, _ => none

/-- Only recognized records become writes; list order is original byte order. -/
def writes (ids : List Nat) (rs : List LinkAllowance) : List (Nat×Nat) :=
  rs.filterMap fun r => (target ids r).map fun l => (l,r.allowance)

theorem index_go_first (s : Nat) (xs : List Nat) (start j : Nat)
    (h : indexOf.go s xs start=some j) :
    ∃ pre post, xs=pre++s::post ∧ j=start+pre.length ∧ s∉pre := by
  induction xs generalizing start with
  | nil => simp [indexOf.go] at h
  | cons x xs ih =>
    simp only [indexOf.go] at h
    split at h
    next hx =>
      subst x
      cases h
      exact ⟨[],xs,by simp⟩
    next hx =>
      obtain ⟨pre,post,he,hj,hno⟩:=ih (start+1) h
      refine ⟨x::pre,post,?_,?_,?_⟩
      · simp [he]
      · simp only [List.length_cons]; omega
      · simpa [hx,Ne.symm hx] using hno

theorem index_first (ids : List Nat) (s j : Nat) (h : indexOf ids s=some j) :
    ∃ pre post, ids=pre++s::post ∧ j=pre.length ∧ s∉pre := by
  simpa using index_go_first s ids 0 j h

theorem target_lt (ids : List Nat) (r : LinkAllowance) (l : Nat)
    (h : target ids r=some l) : l<ids.length*ids.length := by
  unfold target at h
  cases hs:indexOf ids r.sender <;> cases ht:indexOf ids r.receiver <;> simp [hs,ht] at h
  next s t =>
    obtain ⟨pre,post,he,hj,-⟩:=index_first ids r.sender s hs
    have hsl:s<ids.length := by simp [he,hj]
    obtain ⟨pre,post,he,hj,-⟩:=index_first ids r.receiver t ht
    have htl:t<ids.length := by simp [he,hj]
    have hmul:=Nat.mul_le_mul_right ids.length hsl
    rw [Nat.succ_mul] at hmul
    omega

theorem fold_writes (ids : List Nat) (rs : List LinkAllowance) (a : Array Nat) :
    rs.foldl (allowStep ids) a = (writes ids rs).foldl (fun a p=>a.set! p.1 p.2) a := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldl_cons,writes,List.filterMap_cons]
    unfold target allowStep
    cases indexOf ids r.sender <;> cases indexOf ids r.receiver <;> simp only [Option.map_none,Option.map_some,List.foldl_cons] <;> exact ih _

theorem writes_bound (ids : List Nat) (rs : List LinkAllowance) (p : Nat×Nat)
    (hp : p∈writes ids rs) : p.1<ids.length*ids.length := by
  obtain ⟨r,_,hr⟩:=List.mem_filterMap.mp hp
  cases ht:target ids r with
  | none => simp [ht] at hr
  | some l =>
    simp only [ht,Option.map_some,Option.some.injEq] at hr
    subst p
    exact target_lt ids r l ht

/-- Exact last-write characterization, including the no-write default. -/
theorem allowance_last (ids : List Nat) (prev : State) (l : Nat)
    (hl : l<ids.length*ids.length) :
    (allowances ids prev)[l]? =
      some (((writes ids prev.links).filter fun p=>p.1==l).getLast?.map Prod.snd |>.getD 0) := by
  unfold allowances
  rw [fold_writes,foldl_set _ _ (fun p hp=>by simpa using writes_bound ids prev.links p hp)]
  cases ((writes ids prev.links).filter fun p=>p.1==l).getLast? <;> simp [hl]

theorem unknown_ignored (ids : List Nat) (r : LinkAllowance) (a : Array Nat)
    (h : indexOf ids r.sender=none ∨ indexOf ids r.receiver=none) : allowStep ids a r=a := by
  rcases h with h|h <;> simp [allowStep,h] <;> split <;> rfl

end ZkFormal.NearV3.Candidates.ProcPriorLookup
