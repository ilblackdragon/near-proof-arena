import ZkFormal.NearV3.Candidates.ProcDistEventRow
namespace ZkFormal.NearV3.Candidates.ProcDistEventTotal
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcDistEventRow

def outer (n : Nat) (allowed : Array Bool) (sb cs : Array Nat) (rord : List Nat)
    (L : List Nat) (ri : Array Endpoint) (g : Array Nat) : Except String (Array Endpoint × Array Nat) :=
  forIn L (ri,g) (fun s acc => do
    let out ← row n allowed s rord (acc.1,acc.2,(cs[s]!,sb[s]!))
    return .yield (out.1,out.2.1))

theorem outer_exists (n : Nat) (allowed : Array Bool) (sb cs : Array Nat)
    (rord : List Nat) (hrnd : rord.Nodup) :
    ∀ (L : List Nat) (ri : Array Endpoint) (g : Array Nat),
      (∀s∈L, cs[s]! = (rord.filter fun r => allowed[s*n+r]!).length) →
      (∀r∈rord, (ri[r]!).1=(L.filter fun s => allowed[s*n+r]!).length) →
      ∃out,outer n allowed sb cs rord L ri g=.ok out
  | [],ri,g,_,_ => ⟨(ri,g),rfl⟩
  | s::L,ri,g,hcs,hri => by
    have hp : ∀r∈rord, allowed[s*n+r]! = true → 1≤(ri[r]!).1 := by
      intro r hr ha
      rw [hri r hr]
      simp [ha]
    have he := row_eq_grid n allowed s rord ri g (cs[s]!,sb[s]!) hrnd (hcs s (by simp)) hp
    let out := grid n allowed s rord (ri,g,(cs[s]!,sb[s]!))
    have hi : ∀r∈rord,(out.1[r]!).1=(L.filter fun s => allowed[s*n+r]!).length := by
      intro r hr
      rw [grid_receiver_count n allowed s rord _ ri g hrnd r,hri r hr]
      cases ha : allowed[s*n+r]! <;> simp [hr,ha]
    obtain ⟨final,hfinal⟩ := outer_exists n allowed sb cs rord hrnd L out.1 out.2.1 (fun s hs => hcs s (by simp [hs])) hi
    refine ⟨final,?_⟩
    simpa only [outer,List.forIn_cons,he,bind,Except.bind,pure,Except.pure] using hfinal
/-- Canonical link counts guarantee total event distribution for arbitrary budgets. -/
theorem distribute_exists (n : Nat) (allowed : Array Bool) (sb rb cs cr : Array Nat)
    (hcs : ∀s<n,cs[s]! = cntS n allowed s)
    (hcr : ∀r<n,cr[r]! = cntR n allowed r) :
    ∃out,distributeEv n allowed sb rb cs cr=.ok out := by
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
  obtain ⟨out,ho⟩ := outer_exists n allowed sb cs rord hrnd sord _
    (Array.replicate (n*n) 0) hsender hreceiver
  refine ⟨(out.2,sord,rord),?_⟩
  rw [distribute_refactor]
  change (do let acc ← outer n allowed sb cs rord sord _ _
             pure (acc.2,sord,rord))=.ok _
  simp only [ho,bind,Except.bind,pure,Except.pure]

/-- The actual link pass supplies the counts required by event distribution. -/
theorem link_pass_exists (n : Nat) (p : Params) (allowed : Array Bool)
    (a0 sb rb : Array Nat) :
    ∃out,distributeEv n allowed sb rb (linkPass n p allowed a0).cntS
      (linkPass n p allowed a0).cntR=.ok out := by
  apply distribute_exists
  · intro s hs
    exact getElem!_toArray_map_range n _ hs
  · intro r hr
    exact getElem!_toArray_map_range n _ hr

end ZkFormal.NearV3.Candidates.ProcDistEventTotal
