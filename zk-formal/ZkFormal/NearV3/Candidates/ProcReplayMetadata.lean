import ZkFormal.NearV3.Candidates.ProcReplayChain
namespace ZkFormal.NearV3.Candidates.ProcReplayMetadata
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcReplayChain

theorem empty_cursor {T kp Kq zq : Nat} {rs : List RoundD} (h : Stamped T kp Kq zq rs) (he : rs=[]) :
    T=T0 ∧ kp=0 ∧ Kq=Proc.KSENT ∧ zq=0 := by
  cases h with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | snoc h K z L kend es => simp at he

theorem initial {T kp Kq zq : Nat} {rs : List RoundD} (h : Stamped T kp Kq zq rs) :
    ∀rd rest,rs=rd::rest → ProcHeaderKeys.Initial rd := by
  induction h with
  | nil => simp
  | @snoc T kp Kq zq rs h K z L kend es ih =>
    intro rd rest he
    cases rs with
    | nil =>
      have hc := empty_cursor h rfl
      simp only [List.nil_append,List.cons.injEq] at he
      rcases he with ⟨rfl,_⟩
      exact ⟨hc.2.1,hc.1,hc.2.2.1,hc.2.2.2⟩
    | cons r rs =>
      simp only [List.cons_append,List.cons.injEq] at he
      rcases he with ⟨rfl,_⟩
      exact ih r rs rfl

theorem last_cursor {T kp Kq zq : Nat} {rs : List RoundD} (h : Stamped T kp Kq zq rs)
    (pre : List RoundD) (rd : RoundD) (he : rs=pre++[rd]) :
    T=rd.T+rd.Lr ∧ kp=rd.kend ∧ Kq=rd.K ∧ zq=rd.z := by
  cases h with
  | nil =>
    have : pre++[rd]≠[] := by simp
    exact False.elim (this he.symm)
  | snoc h K z L kend es =>
    have hl := congrArg List.getLast? he
    simp only [List.getLast?_append,List.getLast?_singleton] at hl
    have hr := Option.some.inj hl
    subst rd
    exact ⟨rfl,rfl,rfl,rfl⟩

def Adjacent {α : Type} (f : α → α → Prop) (xs : List α) : Prop :=
  ∀pre a b post,xs=pre++a::b::post → f a b

theorem adjacent_snoc {α : Type} (f : α → α → Prop) (xs : List α) (x : α)
    (ha : Adjacent f xs) (hl : ∀pre a,xs=pre++[a] → f a x) : Adjacent f (xs++[x]) := by
  induction xs with
  | nil =>
    intro pre a b post he
    have hh := congrArg List.length he
    simp at hh
    omega
  | cons y ys ih =>
    intro pre a b post he
    cases pre with
    | nil =>
      simp only [List.nil_append,List.cons_append,List.cons.injEq] at he
      rcases he with ⟨rfl,he⟩
      cases ys with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at he
        rcases he with ⟨rfl,hp⟩
        exact hl [] y rfl
      | cons z zs =>
        simp only [List.cons_append,List.cons.injEq] at he
        rcases he with ⟨rfl,hp⟩
        exact ha [] y z zs rfl
    | cons p ps =>
      simp only [List.cons_append,List.cons.injEq] at he
      rcases he with ⟨rfl,he⟩
      apply ih ?_ ?_ ps a b post he
      · intro pre c d post hh
        exact ha (y::pre) c d post (by simp [hh])
      · intro pre c hh
        exact hl (y::pre) c (by simp [hh])

theorem follows {T kp Kq zq : Nat} {rs : List RoundD} (h : Stamped T kp Kq zq rs) :
    Adjacent ProcHeaderContinue.Follows rs := by
  induction h with
  | nil =>
    intro pre a b post he
    have : pre++a::b::post≠[] := by simp
    exact False.elim (this he.symm)
  | @snoc T kp Kq zq rs h K z L kend es ih =>
    apply adjacent_snoc _ _ _ ih
    intro pre rd he
    have hc := last_cursor h pre rd he
    exact ⟨hc.2.1,hc.1,hc.2.2.1,hc.2.2.2⟩

/-- Native success discharges both inter-round metadata clauses of RunData.
Per-round entry and zero-ordinal semantics are proved separately. -/
theorem run_metadata (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    (∀rd rest,R.rounds=rd::rest → ProcHeaderKeys.Initial rd) ∧
    (∀pre rd next rest,R.rounds=pre++rd::next::rest → ProcHeaderContinue.Follows rd next) := by
  rcases run_stamped I tau R h with ⟨T,kp,Kq,zq,hs⟩
  exact ⟨initial hs,follows hs⟩
end ZkFormal.NearV3.Candidates.ProcReplayMetadata
