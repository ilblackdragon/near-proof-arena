import NearSpecV3.PrepD0

namespace ZkFormal.NearV3.RcptLink
open NearSpec NearSpecV3

theorem lexLe_trans : ∀ a b c : Bytes,lexLe a b=true → lexLe b c=true → lexLe a c=true
  | [],b,c,_,_ => by simp [lexLe]
  | a::as,[],c,h,_ => by simp [lexLe] at h
  | a::as,b::bs,[],_,h => by simp [lexLe] at h
  | a::as,b::bs,c::cs,hab,hbc => by
    simp only [lexLe,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hab hbc ⊢
    rcases hab with hab|⟨rfl,hab⟩ <;> rcases hbc with hbc|⟨rfl,hbc⟩
    · apply Or.inl
      simp only [UInt8.lt_iff_toNat_lt] at *
      omega
    · exact Or.inl hab
    · exact Or.inl hbc
    · exact Or.inr ⟨rfl,lexLe_trans as bs cs hab hbc⟩

theorem lexLe_reverse : ∀ a b : Bytes,lexLe a b=false → lexLe b a=true
  | [],_,h => by simp [lexLe] at h
  | a::as,[],_ => rfl
  | a::as,b::bs,h => by
    simp only [lexLe,Bool.or_eq_false_iff,decide_eq_false_iff_not,Bool.and_eq_false_imp,beq_iff_eq] at h
    simp only [lexLe,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    by_cases he : a=b
    · subst b
      exact Or.inr ⟨rfl,lexLe_reverse as bs (h.2 rfl)⟩
    · apply Or.inl
      have hh := h.1
      simp only [UInt8.lt_iff_toNat_lt] at hh ⊢
      have hn : a.toNat≠b.toNat := fun ha => he (UInt8.toNat_inj.mp ha)
      omega

theorem lexMax_le (a b z : Bytes) : lexLe (lexMax a b) z=true ↔ lexLe a z=true ∧ lexLe b z=true := by
  unfold lexMax
  cases h : lexLe a b
  · simp only [Bool.false_eq_true,ite_false]
    exact ⟨fun ha => ⟨ha,lexLe_trans b a z (lexLe_reverse a b h) ha⟩,fun h => h.1⟩
  · simp only [ite_true]
    exact ⟨fun hb => ⟨lexLe_trans a b z h hb,hb⟩,fun h => h.2⟩

private def optBelow (o : Option Bytes) (z : Bytes) : Prop :=
  ∀ a,o=some a → lexLe a z=true

private theorem max_fold_below (xs : List Bytes) (acc : Option Bytes) (z : Bytes) :
    optBelow (xs.foldl (fun acc b => some (match acc with | none => b | some a => lexMax a b)) acc) z ↔
      optBelow acc z ∧ ∀ a∈xs,lexLe a z=true := by
  induction xs generalizing acc with
  | nil => simp [optBelow]
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    cases acc <;> simp [optBelow,lexMax_le,and_assoc]

theorem lexMaxOpt_le (xs : List Bytes) (z : Bytes) :
    (match lexMaxOpt xs with | none => true | some a => lexLe a z)=true ↔
      ∀ a∈xs,lexLe a z=true := by
  have hh := max_fold_below xs none z
  change optBelow (lexMaxOpt xs) z ↔ _ at hh
  cases he : lexMaxOpt xs <;> simpa [optBelow,he] using hh

theorem partitionPoint_of_prefix (xs : List Bytes) (a : Bytes) (k : Nat)
    (hk : k≤xs.length) (hprev : ∀ b∈xs.take k,lexLe b a=true)
    (hnext : (match xs[k]? with | none => true | some b => !lexLe b a)=true) :
    partitionPoint a xs=k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      have hh : lexLe b a=false := by simpa using hnext
      simp [partitionPoint,hh]
  | succ k ih =>
    cases xs with
    | nil => simp at hk
    | cons b bs =>
      have hb : lexLe b a=true := hprev b (by simp)
      have ht := ih bs (by simp at hk; omega)
        (fun x hx => hprev x (by simp [hx])) (by simpa using hnext)
      simp [partitionPoint,hb,ht,Nat.add_comm]

/-- Actual native routing from the prepared ownership intervals. No sorted-boundary
or unique-shard assumption is needed: lexMaxOpt checks every preceding boundary. -/
theorem ownIntervals_sound (L : Layout) (own : Nat) (a : Bytes)
    {iv : Option Bytes × Option Bytes} (hi : iv∈ownIntervals L own)
    (ha : inInterval a iv=true) : L.shardOf a=own := by
  obtain ⟨k,hk,hi⟩ := List.mem_filterMap.mp hi
  have hkl : k≤L.boundaries.length := by have := List.mem_range.mp hk; omega
  split at hi
  · rename_i hown
    obtain rfl := Option.some.inj hi
    simp only [inInterval,Bool.and_eq_true] at ha
    have hp := partitionPoint_of_prefix L.boundaries a k hkl ((lexMaxOpt_le _ _).mp ha.1) ha.2
    simpa only [Layout.shardOf,hp,beq_iff_eq] using hown
  · cases hi

theorem inIntervals_sound (L : Layout) (own : Nat) (a : Bytes)
    (h : inIntervals (ownIntervals L own) a=true) : L.shardOf a=own := by
  obtain ⟨iv,hi,ha⟩ := List.any_eq_true.mp h
  exact ownIntervals_sound L own a hi ha

theorem partitionPoint_spec (xs : List Bytes) (a : Bytes) :
    let k := partitionPoint a xs
    k≤xs.length ∧ (∀ b∈xs.take k,lexLe b a=true) ∧
      (match xs[k]? with | none => true | some b => !lexLe b a)=true := by
  induction xs with
  | nil => simp [partitionPoint]
  | cons b bs ih =>
    cases h : lexLe b a
    · simp [partitionPoint,h]
    · simp only [partitionPoint,h,ite_true]
      obtain ⟨hk,hp,hn⟩ := ih
      refine ⟨by simp; omega,?_,?_⟩
      · intro x hx
        have hm : x=b ∨ x∈bs.take (partitionPoint a bs) := by
          simpa only [Nat.add_comm 1,List.take_succ_cons,List.mem_cons] using hx
        rcases hm with rfl|hm
        · exact h
        · exact hp x hm
      · simpa only [Nat.add_comm 1,List.getElem?_cons_succ] using hn

/-- Conversely every native-routed account belongs to one prepared interval,
including repeated shard IDs and unsorted native boundary lists. -/
theorem inIntervals_complete (L : Layout) (own : Nat) (a : Bytes)
    (h : L.shardOf a=own) : inIntervals (ownIntervals L own) a=true := by
  let k := partitionPoint a L.boundaries
  obtain ⟨hk,hprev,hnext⟩ := partitionPoint_spec L.boundaries a
  apply List.any_eq_true.mpr
  refine ⟨(lexMaxOpt (L.boundaries.take k),L.boundaries[k]?),?_,?_⟩
  · apply List.mem_filterMap.mpr
    refine ⟨k,List.mem_range.mpr (by dsimp only [k]; omega),?_⟩
    have hh : L.shardIds.getD k 0 == own := by simpa only [Layout.shardOf,beq_iff_eq] using h
    simp only [hh,ite_true]
  · simp only [inInterval,Bool.and_eq_true]
    exact ⟨(lexMaxOpt_le _ _).mpr hprev,hnext⟩

theorem inIntervals_iff (L : Layout) (own : Nat) (a : Bytes) :
    inIntervals (ownIntervals L own) a=true ↔ L.shardOf a=own :=
  ⟨inIntervals_sound L own a,inIntervals_complete L own a⟩

end ZkFormal.NearV3.RcptLink
