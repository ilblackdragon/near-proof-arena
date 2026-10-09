import ZkFormal.NearV3.Candidates.ProcDistGridAgreement
namespace ZkFormal.NearV3.Candidates.ProcDistGrantBounds
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcDistGridAgreement

def Bound (n : Nat) (sb : Array Nat) (g : Array (Option Nat)) : Prop :=
  ∀l,(g[l]!).getD 0≤sb[l/n]!

theorem set_bound (n : Nat) (sb : Array Nat) (g : Array (Option Nat))
    (hg : Bound n sb g) (l b : Nat) (hb : b≤sb[l/n]!) :
    Bound n sb (g.set! l (some b)) := by
  intro k
  by_cases hk : l=k
  · subst k
    rw [getElem!_set!_self]
    split
    · exact hb
    · exact hg l
  · rw [getElem!_set!_ne _ _ hk]
    exact hg k

/-- Each grid cell is bounded by the sender's original residual budget. -/
theorem row_bound (n : Nat) (hn : 0<n) (allowed : Array Bool) (sb : Array Nat) (s : Nat) :
    ∀(rs : List Nat) (se : Endpoint) (ri : Array Endpoint) (g : Array (Option Nat)),
      (∀r∈rs,r<n) → se.2≤sb[s]! → Bound n sb g →
      Bound n sb (gridRow n allowed s rs se ri g).2.2 ∧
      (gridRow n allowed s rs se ri g).2.2.size=g.size
  | [],se,ri,g,_,_,hg => ⟨hg,rfl⟩
  | r::rs,se,ri,g,hrs,hse,hg => by
    by_cases ha : allowed[s*n+r]! = true
    · simp only [gridRow,ha,Bool.not_true,Bool.false_eq_true,ite_false]
      have hr : r<n := hrs r (by simp)
      have hl : (s*n+r)/n=s := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]
      have hb : Nat.min (se.2/se.1) ((ri[r]!).2/(ri[r]!).1)≤sb[(s*n+r)/n]! := by
        rw [hl]
        exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans (Nat.div_le_self _ _) hse)
      let b := Nat.min (se.2/se.1) ((ri[r]!).2/(ri[r]!).1)
      obtain ⟨hbound,hsize⟩ := row_bound n hn allowed sb s rs
        (se.1-1,se.2-b) (ri.set! r ((ri[r]!).1-1,(ri[r]!).2-b)) (g.set! (s*n+r) (some b))
        (fun r hr => hrs r (by simp [hr])) (by exact Nat.le_trans (Nat.sub_le _ _) hse) (set_bound n sb g hg _ _ hb)
      exact ⟨hbound,hsize.trans (by simp)⟩
    · have hf : allowed[s*n+r]! = false := by simpa using ha
      simpa only [gridRow,hf,Bool.not_false,ite_true] using
        row_bound n hn allowed sb s rs se ri g (fun r hr => hrs r (by simp [hr])) hse hg
theorem fold_bound (n : Nat) (hn : 0<n) (allowed : Array Bool) (sb cs : Array Nat)
    (rord : List Nat) (hr : ∀r∈rord,r<n) (L : List Nat)
    (ri : Array Endpoint) (g : Array (Option Nat)) (hg : Bound n sb g) :
    Bound n sb (nativeFold n allowed sb cs rord L ri g).2 ∧
    (nativeFold n allowed sb cs rord L ri g).2.size=g.size := by
  induction L generalizing ri g with
  | nil => exact ⟨hg,rfl⟩
  | cons s L ih =>
    have hrow := row_bound n hn allowed sb s rord (cs[s]!,sb[s]!) ri g hr (Nat.le_refl _) hg
    have htail := ih (gridRow n allowed s rord (cs[s]!,sb[s]!) ri g).2.1 _ hrow.1
    exact ⟨htail.1,htail.2.trans hrow.2⟩

/-- Every native distribution grant fits its sender's residual budget. -/
theorem grid_bound (n : Nat) (hn : 0<n) (allowed : Array Bool) (sb rb : Array Nat) :
    Bound n sb (gridGrants n allowed sb rb (sordOf n allowed sb) (rordOf n allowed rb)) ∧
    (gridGrants n allowed sb rb (sordOf n allowed sb) (rordOf n allowed rb)).size=n*n := by
  let cs := ((List.range n).map (cntS n allowed)).toArray
  let cr := ((List.range n).map (cntR n allowed)).toArray
  rw [←nativeFold_grants n allowed sb rb cs cr (sordOf n allowed sb) (rordOf n allowed rb)
    (fun s hs => (mem_sortByKey_range _ n s).mp hs)
    (fun s hs => getElem!_toArray_map_range n _ hs)
    (fun r hr => getElem!_toArray_map_range n _ hr)]
  have hg : Bound n sb (Array.replicate (n*n) none) := by
    intro l
    by_cases hl : l<n*n <;> simp [getElem!_def,hl]
    exact Nat.zero_le _
  have h := fold_bound n hn allowed sb cs (rordOf n allowed rb)
    (fun r hr => (mem_sortByKey_range _ n r).mp hr) (sordOf n allowed sb)
    ((List.range n).toArray.map (fun r => (cr[r]!,rb[r]!))) (Array.replicate (n*n) none) hg
  exact ⟨h.1,h.2.trans (by simp)⟩

/-- The process budget invariant rules out native saturating-add overflow. -/
theorem granted_eq_add (n M : Nat) (hn : 0<n) (hM : M≤u64Max)
    (allowed : Array Bool) (st : St) (hinv : GInv n M st)
    (hs : st.senderBudget.size=n) (hr : st.receiverBudget.size=n)
    (ha : allowed.size=n*n) (hg : st.granted.size=n*n)
    (l : Nat) (hl : l<n*n) :
    (distribute n allowed st).granted[l]! =st.granted[l]!+
      ((gridGrants n allowed st.senderBudget st.receiverBudget
        (sordOf n allowed st.senderBudget) (rordOf n allowed st.receiverBudget))[l]!).getD 0 := by
  have hb := grid_bound n hn allowed st.senderBudget st.receiverBudget
  rw [distribute_eq_grid n allowed st hs hr ha,applyGrants_granted n st _ l hl hg hb.2]
  have hbudget := hinv l
  have hgrant := hb.1 l
  cases he : (gridGrants n allowed st.senderBudget st.receiverBudget
      (sordOf n allowed st.senderBudget) (rordOf n allowed st.receiverBudget))[l]! with
  | none => simp
  | some b =>
    simp only [he,Option.getD_some] at hgrant
    have hadd : st.granted[l]!+b≤u64Max := by omega
    simp [hadd]

theorem numerical_get (g : Array (Option Nat)) (l : Nat) (hl : l<g.size) :
    (numerical g)[l]! = (g[l]!).getD 0 := by
  simp [numerical,hl]

/-- Event distribution grants, added to process grants, equal native distribution. -/
theorem event_granted (n M : Nat) (hn : 0<n) (hM : M≤u64Max)
    (p : Params) (allowed : Array Bool) (a0 : Array Nat) (st : St)
    (hinv : GInv n M st) (hs : st.senderBudget.size=n) (hr : st.receiverBudget.size=n)
    (ha : allowed.size=n*n) (hg : st.granted.size=n*n)
    (gd : Array Nat) (sord rord : List Nat)
    (he : distributeEv n allowed st.senderBudget st.receiverBudget
      (linkPass n p allowed a0).cntS (linkPass n p allowed a0).cntR=.ok (gd,sord,rord))
    (l : Nat) (hl : l<n*n) :
    (distribute n allowed st).granted[l]! = st.granted[l]!+gd[l]! := by
  rw [link_pass_grid] at he
  have hgd := congrArg (fun x : Array Nat × List Nat × List Nat => x.1) (Except.ok.inj he)
  dsimp only at hgd
  rw [←hgd,numerical_get _ l (by rw [(grid_bound n hn allowed st.senderBudget st.receiverBudget).2]; exact hl)]
  exact granted_eq_add n M hn hM allowed st hinv hs hr ha hg l hl

end ZkFormal.NearV3.Candidates.ProcDistGrantBounds
