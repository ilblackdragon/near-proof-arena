import ZkFormal.NearV3.Assembly.DecodedShapes
import ZkFormal.NearV3.Rcpt.Link.OwnIntervals

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- Decoder validation applies to every boundary; no relation between boundary
count and shard-id count is assumed. -/
theorem decodeLayout_boundaries {raw : Bytes} {L : Layout}
    (h : decodeLayout raw=.ok L) : ∀ b∈L.boundaries, AccountId.valid b=true := by
  unfold decodeLayout at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    exact pVec_property (pAccountId "boundary") (fun b => AccountId.valid b=true)
      (fun _ _ _ hb => V3.pAccountId_valid hb) (by assumption)

theorem walkD0_boundaries {cb : Bytes} {k : WalkD0} (h : walkD0 cb=.ok k) :
    ∀ b∈k.L.boundaries,AccountId.valid b=true := by
  unfold walkD0 at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    exact decodeLayout_boundaries (by assumption)

private theorem max_valid (a b : Bytes) (ha : AccountId.valid a=true)
    (hb : AccountId.valid b=true) : AccountId.valid (lexMax a b)=true := by
  unfold lexMax
  split <;> assumption

private theorem fold_valid (xs : List Bytes) (acc : Option Bytes)
    (ha : ∀ b,acc=some b → AccountId.valid b=true)
    (hx : ∀ b∈xs,AccountId.valid b=true) :
    ∀ b,xs.foldl (fun acc b => some (match acc with | none => b | some a => lexMax a b)) acc=some b →
      AccountId.valid b=true := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    apply ih
    · cases acc with
      | none => intro b hb; cases hb; exact hx x (by simp)
      | some a =>
        intro b hb
        cases hb
        exact max_valid a x (ha a rfl) (hx x (by simp))
    · intro b hb
      exact hx b (by simp [hb])

/-- Both endpoints of every native ownership interval are validated account ids
when present, including prefix maxima in unsorted layouts. -/
theorem ownIntervals_endpoints (L : Layout) (own : Nat)
    (h : ∀ b∈L.boundaries,AccountId.valid b=true)
    {iv : Option Bytes × Option Bytes} (hi : iv∈ownIntervals L own) :
    (∀ b,iv.1=some b → AccountId.valid b=true) ∧
    (∀ b,iv.2=some b → AccountId.valid b=true) := by
  obtain ⟨i,_,he⟩ := List.mem_filterMap.mp hi
  unfold ownIntervals at hi
  split at he
  · cases he
    constructor
    · exact fold_valid _ none (by simp) (fun b hb => h b (List.mem_of_mem_take hb))
    · intro b hb
      exact h b (List.mem_of_getElem? hb)
  · cases he

end ZkFormal.NearV3.Assembly
