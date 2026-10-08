import ZkFormal.NearV3.Rcpt.Candidates.SourceShaFourPacking

namespace ZkFormal.NearV3.Rcpt.Candidates

/-- Split only between jobs. The original object is retained unchanged. -/
def splitJobs {α : Type} (weight : α→Nat) : Nat→List α→List α×List α
  | _,[] => ([],[])
  | cap,x::xs => if weight x≤cap then
      let p := splitJobs weight (cap-weight x) xs
      (x::p.1,p.2)
    else ([],x::xs)

theorem splitJobs_reconstruct {α : Type} (weight : α→Nat) (cap : Nat) (xs : List α) :
    (splitJobs weight cap xs).1++(splitJobs weight cap xs).2=xs := by
  induction xs generalizing cap with
  | nil => rfl
  | cons x xs ih =>
    simp only [splitJobs]
    split
    · simp only [List.cons_append,ih]
    · rfl

theorem splitJobs_weights {α : Type} (weight : α→Nat) (cap : Nat) (xs : List α) :
    ((splitJobs weight cap xs).1.map weight,(splitJobs weight cap xs).2.map weight)=
      splitBudget cap (xs.map weight) := by
  induction xs generalizing cap with
  | nil => rfl
  | cons x xs ih =>
    simp only [splitJobs,splitBudget,List.map_cons]
    split
    · have hh := ih (cap-weight x)
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      dsimp only at h1 h2
      simp only [List.map_cons,h1,h2]
    · rfl

def fourShaJobBins {α : Type} (weight : α→Nat) (scheduler native receipt source : List α) :
    List (List α) :=
  let p0 := splitJobs weight (2^22-(scheduler.map weight).sum) source
  let p1 := splitJobs weight (2^22-(native.map weight).sum) p0.2
  let p2 := splitJobs weight (2^22-(receipt.map weight).sum) p1.2
  [scheduler++p0.1,native++p1.1,receipt++p2.1,p2.2]

theorem fourShaJobBins_weights {α : Type} (weight : α→Nat) (scheduler native receipt source : List α) :
    (fourShaJobBins weight scheduler native receipt source).map (List.map weight)=
      fourShaBins (scheduler.map weight) (native.map weight) (receipt.map weight) (source.map weight) := by
  have he1 : ∀cap xs,(splitJobs weight cap xs).1.map weight=(splitBudget cap (xs.map weight)).1 :=
    fun cap xs => congrArg Prod.fst (splitJobs_weights weight cap xs)
  have he2 : ∀cap xs,(splitJobs weight cap xs).2.map weight=(splitBudget cap (xs.map weight)).2 :=
    fun cap xs => congrArg Prod.snd (splitJobs_weights weight cap xs)
  simp only [fourShaJobBins,fourShaBins,List.map_cons,List.map_nil,List.map_append,he1,he2]

private theorem regroup {α : Type} (a b c p q r s : List α) :
    (a++p++b++q++c++r++s).Perm (a++b++c++(p++q++r++s)) := by
  have h1 := (List.perm_append_comm (l₁:=p) (l₂:=b)).append_right (q++c++r++s)
  have h2 := (List.perm_append_comm (l₁:=p++q) (l₂:=c)).append_right (r++s)
  have hh1 : (a++p++b++q++c++r++s).Perm (a++b++p++q++c++r++s) := by
    simpa only [List.append_assoc] using h1.append_left a
  have hh2 : (a++b++p++q++c++r++s).Perm (a++b++c++(p++q++r++s)) := by
    simpa only [List.append_assoc] using h2.append_left (a++b)
  exact hh1.trans hh2

/-- Exact multiset preservation of full job objects, including identifiers,
bytes, and digest multiplicity flags carried by the caller's job type. -/
theorem fourShaJobBins_preserve {α : Type} (weight : α→Nat) (scheduler native receipt source : List α) :
    (fourShaJobBins weight scheduler native receipt source).flatten.Perm
      (scheduler++native++receipt++source) := by
  dsimp only [fourShaJobBins]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  have he0 := splitJobs_reconstruct weight (2^22-(scheduler.map weight).sum) source
  have he1 := splitJobs_reconstruct weight (2^22-(native.map weight).sum)
    (splitJobs weight (2^22-(scheduler.map weight).sum) source).2
  have he2 := splitJobs_reconstruct weight (2^22-(receipt.map weight).sum)
    (splitJobs weight (2^22-(native.map weight).sum)
      (splitJobs weight (2^22-(scheduler.map weight).sum) source).2).2
  have hr := regroup scheduler native receipt
    (splitJobs weight (2^22-(scheduler.map weight).sum) source).1
    (splitJobs weight (2^22-(native.map weight).sum)
      (splitJobs weight (2^22-(scheduler.map weight).sum) source).2).1
    (splitJobs weight (2^22-(receipt.map weight).sum)
      (splitJobs weight (2^22-(native.map weight).sum)
        (splitJobs weight (2^22-(scheduler.map weight).sum) source).2).2).1
    (splitJobs weight (2^22-(receipt.map weight).sum)
      (splitJobs weight (2^22-(native.map weight).sum)
        (splitJobs weight (2^22-(scheduler.map weight).sum) source).2).2).2
  simp only [List.append_assoc] at hr ⊢
  rw [he2,he1,he0] at hr
  simpa only [he2] using hr

theorem fourShaJobBins_fit {α : Type} (weight : α→Nat) (scheduler native receipt source : List α)
    (hs : (scheduler.map weight).sum≤1663260) (hn : (native.map weight).sum≤2925275)
    (hr : (receipt.map weight).sum≤1373299) (hsrc : (source.map weight).sum≤8932712)
    (hmax : ∀x∈source,weight x≤35) :
    (fourShaJobBins weight scheduler native receipt source).length=4 ∧
    ∀bin∈fourShaJobBins weight scheduler native receipt source,(bin.map weight).sum≤2^22 := by
  have hweights := fourShaJobBins_weights weight scheduler native receipt source
  have hm : ∀x∈source.map weight,x≤35 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hmax y hy
  have hfit := fourShaBins_fit _ _ _ _ hs hn hr hsrc hm
  refine ⟨rfl,?_⟩
  intro bin hb
  apply hfit.2 (bin.map weight)
  rw [←hweights]
  exact List.mem_map.mpr ⟨bin,hb,rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates
