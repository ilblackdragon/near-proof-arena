import ZkFormal.NearV3.Candidates.ProcDistEventTotal
namespace ZkFormal.NearV3.Candidates.ProcDistGridAgreement
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcDistEventRow

def numerical (g : Array (Option Nat)) : Array Nat := g.map (fun x => x.getD 0)

theorem numerical_set (g : Array (Option Nat)) (l b : Nat) :
    numerical (g.set! l (some b))=(numerical g).set! l b := by
  simp [numerical,Array.set!_eq_setIfInBounds]

/-- Numerical event grants are the native optional grid with absent grants zeroed.
Both endpoint states agree exactly, including residual budgets and link counts. -/
theorem grid_agrees (n : Nat) (allowed : Array Bool) (s : Nat) :
    ∀ (rs : List Nat) (ri : Array Endpoint) (g : Array (Option Nat)) (se : Endpoint),
      grid n allowed s rs (ri,numerical g,se)=
        let out := gridRow n allowed s rs se ri g
        (out.2.1,numerical out.2.2,out.1)
  | [],ri,g,se => rfl
  | r::rs,ri,g,se => by
    cases ha : allowed[s*n+r]!
    · simpa only [grid,gridRow,ha,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
        using grid_agrees n allowed s rs ri g se
    · simp only [grid,gridRow,ha,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
      rw [←numerical_set]
      exact grid_agrees n allowed s rs _ _ _

/-- The checked event receiver loop computes the native grid row. -/
theorem row_agrees (n : Nat) (allowed : Array Bool) (s : Nat)
    (rs : List Nat) (ri : Array Endpoint) (g : Array (Option Nat)) (se : Endpoint)
    (hnd : rs.Nodup) (hse : se.1=(rs.filter fun r => allowed[s*n+r]!).length)
    (hri : ∀r∈rs,allowed[s*n+r]! = true → 1≤(ri[r]!).1) :
    row n allowed s rs (ri,numerical g,se)=.ok
      (let out := gridRow n allowed s rs se ri g
       (out.2.1,numerical out.2.2,out.1)) := by
  rw [row_eq_grid n allowed s rs ri (numerical g) se hnd hse hri,grid_agrees]
def nativeFold (n : Nat) (allowed : Array Bool) (sb cs : Array Nat) (rord L : List Nat)
    (ri : Array Endpoint) (g : Array (Option Nat)) : Array Endpoint × Array (Option Nat) :=
  L.foldl (fun acc s =>
    let out := gridRow n allowed s rord (cs[s]!,sb[s]!) acc.1 acc.2
    (out.2.1,out.2.2)) (ri,g)

/-- All sender rows preserve exact correspondence with native grid grants. -/
theorem outer_agrees (n : Nat) (allowed : Array Bool) (sb cs : Array Nat)
    (rord : List Nat) (hrnd : rord.Nodup) :
    ∀ (L : List Nat) (ri : Array Endpoint) (g : Array (Option Nat)),
      (∀s∈L,cs[s]! = (rord.filter fun r => allowed[s*n+r]!).length) →
      (∀r∈rord,(ri[r]!).1=(L.filter fun s => allowed[s*n+r]!).length) →
      ProcDistEventTotal.outer n allowed sb cs rord L ri (numerical g)=.ok
        (let out := nativeFold n allowed sb cs rord L ri g
         (out.1,numerical out.2))
  | [],ri,g,_,_ => rfl
  | s::L,ri,g,hcs,hri => by
    have hp : ∀r∈rord,allowed[s*n+r]! = true → 1≤(ri[r]!).1 := by
      intro r hr ha
      rw [hri r hr]
      simp [ha]
    have he := row_agrees n allowed s rord ri g (cs[s]!,sb[s]!) hrnd (hcs s (by simp)) hp
    let out := gridRow n allowed s rord (cs[s]!,sb[s]!) ri g
    have hi : ∀r∈rord,(out.2.1[r]!).1=(L.filter fun s => allowed[s*n+r]!).length := by
      intro r hr
      rw [gridRow_ri_fst n allowed s rord _ ri g hrnd r,hri r hr]
      cases ha : allowed[s*n+r]! <;> simp [hr,ha]
    have ih := outer_agrees n allowed sb cs rord hrnd L out.2.1 out.2.2
      (fun s hs => hcs s (by simp [hs])) hi
    simpa only [ProcDistEventTotal.outer,List.forIn_cons,he,bind,Except.bind,pure,Except.pure,
      nativeFold,List.foldl_cons] using ih

theorem distribute_agrees (n : Nat) (allowed : Array Bool) (sb rb cs cr : Array Nat)
    (hcs : ∀s<n,cs[s]! = cntS n allowed s)
    (hcr : ∀r<n,cr[r]! = cntR n allowed r) :
    distributeEv n allowed sb rb cs cr=.ok
      (let sord := sortedBy (fun s => avgOf cs[s]! sb[s]!) n
       let rord := sortedBy (fun r => avgOf cr[r]! rb[r]!) n
       let ri := (List.range n).toArray.map (fun r => (cr[r]!,rb[r]!))
       (numerical (nativeFold n allowed sb cs rord sord ri (Array.replicate (n*n) none)).2,
        sord,rord)) := by
  let sord := sortedBy (fun s => avgOf cs[s]! sb[s]!) n
  let rord := sortedBy (fun r => avgOf cr[r]! rb[r]!) n
  have hsperm : sord.Perm (List.range n) := sortByKey_perm _ _
  have hrperm : rord.Perm (List.range n) := sortByKey_perm _ _
  have hrnd : rord.Nodup := hrperm.nodup_iff.2 List.nodup_range
  have hsender : ∀s∈sord,cs[s]! = (rord.filter fun r => allowed[s*n+r]!).length := by
    intro s hs
    rw [hcs s (List.mem_range.mp (hsperm.mem_iff.mp hs))]
    exact (filter_length_perm _ hrperm).symm
  have hreceiver : ∀r∈rord,
      ((((List.range n).toArray.map (fun r => (cr[r]!,rb[r]!)))[r]!).1)=
        (sord.filter fun s => allowed[s*n+r]!).length := by
    intro r hr
    have hlt := List.mem_range.mp (hrperm.mem_iff.mp hr)
    rw [List.map_toArray]
    rw [getElem!_toArray_map_range n _ hlt]
    rw [hcr r hlt]
    exact (filter_length_perm _ hsperm).symm
  have ho := outer_agrees n allowed sb cs rord hrnd sord _
    (Array.replicate (n*n) none) hsender hreceiver
  have hz : numerical (Array.replicate (n*n) none)=Array.replicate (n*n) 0 := by
    simp [numerical]
  rw [hz] at ho
  rw [distribute_refactor]
  change (do let acc ← ProcDistEventTotal.outer n allowed sb cs rord sord _ _
             pure (acc.2,sord,rord))=.ok _
  simp only [ho,bind,Except.bind,pure,Except.pure]
  rfl

theorem nativeFold_endpoints (n : Nat) (allowed : Array Bool) (sb cs : Array Nat)
    (rord L : List Nat) (si ri : Array Endpoint) (g : Array (Option Nat))
    (hsi : ∀s∈L,si[s]! = (cs[s]!,sb[s]!)) :
    nativeFold n allowed sb cs rord L ri g =
      L.foldl (fun acc s =>
        let out := gridRow n allowed s rord si[s]! acc.1 acc.2
        (out.2.1,out.2.2)) (ri,g) := by
  induction L generalizing ri g with
  | nil => rfl
  | cons s L ih =>
    simp only [nativeFold,List.foldl_cons,hsi s (by simp)]
    exact ih _ _ (fun s hs => hsi s (by simp [hs]))

theorem nativeFold_grants (n : Nat) (allowed : Array Bool) (sb rb cs cr : Array Nat)
    (sord rord : List Nat) (hsord : ∀s∈sord,s<n)
    (hcs : ∀s<n,cs[s]! = cntS n allowed s)
    (hcr : ∀r<n,cr[r]! = cntR n allowed r) :
    (nativeFold n allowed sb cs rord sord
      ((List.range n).toArray.map (fun r => (cr[r]!,rb[r]!)))
      (Array.replicate (n*n) none)).2=gridGrants n allowed sb rb sord rord := by
  rw [nativeFold_endpoints n allowed sb cs rord sord
    (((List.range n).map fun s => (cntS n allowed s,sb[s]!)).toArray)]
  · unfold gridGrants
    have hi : (List.range n).toArray.map (fun r => (cr[r]!,rb[r]!))=
        ((List.range n).map fun r => (cntR n allowed r,rb[r]!)).toArray := by
      rw [List.map_toArray]
      congr 1
      apply List.map_congr_left
      intro r hr
      rw [hcr r (List.mem_range.mp hr)]
    rw [hi]
  · intro s hs
    rw [getElem!_toArray_map_range n _ (hsord s hs),hcs s (hsord s hs)]

/-- Full event distribution returns exactly the native grid's numerical grants. -/
theorem distribute_grid (n : Nat) (allowed : Array Bool) (sb rb cs cr : Array Nat)
    (hcs : ∀s<n,cs[s]! = cntS n allowed s)
    (hcr : ∀r<n,cr[r]! = cntR n allowed r) :
    distributeEv n allowed sb rb cs cr=.ok
      (numerical (gridGrants n allowed sb rb (sordOf n allowed sb) (rordOf n allowed rb)),
        sordOf n allowed sb,rordOf n allowed rb) := by
  have hs : sortedBy (fun s => avgOf cs[s]! sb[s]!) n=sordOf n allowed sb := by
    apply sortByKey_congr
    intro s hs
    rw [hcs s (List.mem_range.mp hs)]
    rfl
  have hr : sortedBy (fun r => avgOf cr[r]! rb[r]!) n=rordOf n allowed rb := by
    apply sortByKey_congr
    intro r hr
    rw [hcr r (List.mem_range.mp hr)]
    rfl
  rw [distribute_agrees n allowed sb rb cs cr hcs hcr]
  dsimp only
  rw [hs,hr,nativeFold_grants n allowed sb rb cs cr (sordOf n allowed sb) (rordOf n allowed rb)
    (fun s hs => (mem_sortByKey_range _ n s).mp hs) hcs hcr]

theorem link_pass_grid (n : Nat) (p : Params) (allowed : Array Bool)
    (a0 sb rb : Array Nat) :
    distributeEv n allowed sb rb (linkPass n p allowed a0).cntS
      (linkPass n p allowed a0).cntR=.ok
      (numerical (gridGrants n allowed sb rb (sordOf n allowed sb) (rordOf n allowed rb)),
        sordOf n allowed sb,rordOf n allowed rb) := by
  apply distribute_grid
  · intro s hs
    exact getElem!_toArray_map_range n _ hs
  · intro r hr
    exact getElem!_toArray_map_range n _ hr

end ZkFormal.NearV3.Candidates.ProcDistGridAgreement
