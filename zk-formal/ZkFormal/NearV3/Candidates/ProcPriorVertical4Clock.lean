import ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockCases
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical4Clock
open ZkFormal.Air ZkFormal.Algebra ProcPriorVertical4ClockCases

/-- Absolute cuts partition the physical table; the final stage absorbs padding. -/
def stageAt (a b c j : Nat) : Nat:=if j<a then 0 else if j<b then 1 else if j<c then 2 else 3
def firstAt (a b c j : Nat) : Bool:=decide (j=0 ∨ j=a ∨ j=b ∨ j=c)
def lastAt (a b c n j : Nat) : Bool:=decide (j+1=a ∨ j+1=b ∨ j+1=c ∨ j+1=n)

theorem stage_bound (a b c j : Nat) : stageAt a b c j<4 := by
  unfold stageAt
  repeat (first | split | decide +kernel)

theorem first_next (a b c n j : Nat) (hj:j+1<n) :
    firstAt a b c (j+1)=lastAt a b c n j := by
  have hz:j+1≠0:=by omega
  have hn:j+1≠n:=by omega
  simp [firstAt,lastAt,hz,hn]

theorem stage_next (a b c n j : Nat) (ha:0<a) (hab:a<b) (hbc:b<c) (hcn:c<n)
    (hj:j+1<n) :
    if lastAt a b c n j then stageAt a b c j<3 ∧ stageAt a b c (j+1)=stageAt a b c j+1
    else stageAt a b c (j+1)=stageAt a b c j := by
  by_cases he:j+1=a ∨ j+1=b ∨ j+1=c ∨ j+1=n
  · simp only [lastAt,he,decide_true,ite_true]
    unfold stageAt
    repeat (first | split | omega)
  · simp [lastAt,he]
    unfold stageAt
    repeat (first | split | omega)

theorem valid (a b c n j : Nat) (ha:0<a) (hab:a<b) (hbc:b<c) (hcn:c<n) (hj:j<n) :
    Valid (stageAt a b c j) (stageAt a b c ((j+1)%n))
      (firstAt a b c j) (lastAt a b c n j) (firstAt a b c ((j+1)%n))
      (decide (j=0)) (decide (j+1=n)) := by
  refine ⟨?_,?_,?_⟩
  · intro h
    have h0:j=0:=of_decide_eq_true h
    subst j
    simp [stageAt,firstAt,ha]
  · intro h
    have he:j+1=n:=of_decide_eq_true h
    have hja:¬j<a:=by omega
    have hjb:¬j<b:=by omega
    have hjc:¬j<c:=by omega
    simp [stageAt,hja,hjb,hjc,lastAt,he]
  · intro h
    have hne:j+1≠n:=of_decide_eq_false h
    have hlt:j+1<n:=by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact ⟨first_next a b c n j hlt,stage_next a b c n j ha hab hbc hcn hlt⟩

theorem constraints (a b c n j : Nat) (ha:0<a) (hab:a<b) (hbc:b<c) (hcn:c<n) (hj:j<n) :
    ∀e∈ProcPriorVertical4Linear.windows,
      e.evalWith (markerEnv (stageAt a b c j) (stageAt a b c ((j+1)%n))
        (firstAt a b c j) (lastAt a b c n j) (firstAt a b c ((j+1)%n))
        (decide (j=0)) (decide (j+1=n)))=0 :=
  marker_constraints _ _ (stage_bound a b c j) (stage_bound a b c ((j+1)%n)) _ _ _ _ _
    (valid a b c n j ha hab hbc hcn hj)
end ZkFormal.NearV3.Candidates.ProcPriorVertical4Clock
