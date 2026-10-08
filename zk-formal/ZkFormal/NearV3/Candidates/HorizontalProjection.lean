import ZkFormal.NearV3.Candidates.HorizontalTraffic
namespace ZkFormal.NearV3.Candidates.HorizontalProjection
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace HorizontalTraffic

/-- Original table identities paired with their physical column projection. -/
def split (tr : Trace Fp) (off : Nat) : List Air.Table → List (Air.Table × Trace Fp)
  | [] => []
  | T::ts => (T,project off tr)::split tr (off+T.width) ts

theorem shifted_count (T : Air.Table) (tr : Trace Fp) (off t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (shifted off T).interactions tr t pub bus send msg=
      tableBusCount T.interactions (project off tr) t pub bus send msg := by
  have hm : mapI (expression off)=interaction off := rfl
  simpa only [hm,shifted] using count_map (expression off) T.interactions tr (project off tr)
    t pub bus send msg rfl (by intro r i hi e he; exact HorizontalTrace.expression_eval tr t r off pub e)

theorem layout_count (ts : List Air.Table) (tr : Trace Fp) (off t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount ((layout off ts).flatMap (·.interactions)) tr t pub bus send msg=
      ((split tr off ts).map (fun x=>tableBusCount x.1.interactions x.2 t pub bus send msg)).sum := by
  induction ts generalizing off with
  | nil =>
    simp only [layout,List.flatMap_nil,split,List.map_nil,List.sum_nil,table_sum,rowCount]
    have hz : ∀ rs : List Nat,(rs.map (fun _=>0)).sum=0 := by
      intro rs
      induction rs <;> simp_all
    exact hz _
  | cons T ts ih =>
    simp only [layout,List.flatMap_cons,count_append,shifted_count,ih,
      split,List.map_cons,List.sum_cons]

theorem fused_count (ts : List Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (fuse ts).interactions tr t pub bus send msg=
      ((split tr 0 ts).map (fun x=>tableBusCount x.1.interactions x.2 t pub bus send msg)).sum :=
  layout_count ts tr 0 t pub bus send msg

theorem split_location (ts : List Air.Table) (tr : Trace Fp) (off : Nat)
    {x : Air.Table × Trace Fp} (hx : x∈split tr off ts) :
    ∃ k, shifted k x.1∈layout off ts ∧ x.2=project k tr := by
  induction ts generalizing off with
  | nil => simp [split] at hx
  | cons T ts ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨off,by simp [layout],rfl⟩
    · obtain ⟨k,hk,he⟩ := ih (off+T.width) hx
      exact ⟨k,List.mem_cons_of_mem _ hk,he⟩

theorem split_tables (ts : List Air.Table) (tr : Trace Fp) (off : Nat) :
    (split tr off ts).map Prod.fst=ts := by
  induction ts generalizing off with
  | nil => rfl
  | cons T ts ih => simp [split,ih]

theorem fused_local (ts : List Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hc : ∀T∈ts,T.maxLog=22) (h : TableLocal (fuse ts) tr t pub) :
    ∀x∈split tr 0 ts,TableLocal x.1 x.2 t pub := by
  intro x hx
  obtain ⟨k,hk,he⟩ := split_location ts tr 0 hx
  have hm : x.1∈ts := by
    rw [← split_tables ts tr 0]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  rw [he]
  exact project_local hk (hc x.1 hm) h
end ZkFormal.NearV3.Candidates.HorizontalProjection
