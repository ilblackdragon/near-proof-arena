import ZkFormal.NearV3.Qv.Extract.ShardCountFilter

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

private theorem selected_length {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    (l.flatMap (fun x => if p x then [f x] else [])).length=(l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

private theorem unique_length {α : Type} (l : List α) (hn : l.Nodup)
    (hu : ∀ x∈l,∀ y∈l,x=y) : l.length≤1 := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne := (List.pairwise_cons.mp hn).1 y (by simp)
      exact False.elim (hne (hu x (by simp) y (by simp)))

/-- Prefix count filtering is exactly the actual physical count-gate selection. -/
theorem walk_count_filter {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) :
    ((List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false)).filter isShardCount=
    (List.range (segEnd 0 q.segs)).flatMap (fun r =>
      if tr.cell tt r countRead=1 then
        [[tr.cell tt r Candidates.ValueTable.tau,0,8,tr.cell tt r Candidates.ValueTable.count]] else []) := by
  rw [List.filter_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr
  have hpre := List.mem_range.mp hr
  have hm : r∈List.range' 0 (segEnd 0 q.segs) := by simpa only [←List.range_eq_range'] using hr
  have he := range'_segs q.segs 0 q.consecutive
  simp only [Nat.sub_zero] at he
  rw [he] at hm
  obtain ⟨p,hp,hrow⟩ := List.mem_flatMap.mp hm
  have hb := List.mem_range'.mp hrow
  have hend := seg_le_end q.segs 0 q.consecutive p hp
  exact physical_shard_count_filter hL (Nat.le_trans hend.2 q.fits) (q.valid p hp) (by omega) (by omega)

/-- Across the entire receiving prefix, at most one count packet exists. -/
theorem walk_count_capacity {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) :
    (((List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false)).filter isShardCount).length≤1 := by
  rw [walk_count_filter hL q]
  let pred := fun r => decide (tr.cell tt r countRead=1)
  have he := selected_length (List.range (segEnd 0 q.segs)) pred
    (fun r => [tr.cell tt r Candidates.ValueTable.tau,0,8,tr.cell tt r Candidates.ValueTable.count])
  simp only [pred,decide_eq_true_eq] at he
  rw [he]
  apply unique_length
  · exact List.Pairwise.filter _ List.nodup_range
  · intro r hr s hs
    obtain ⟨hr,hc⟩ := List.mem_filter.mp hr
    obtain ⟨hs,hd⟩ := List.mem_filter.mp hs
    have hr' := List.mem_range.mp hr
    have hs' := List.mem_range.mp hs
    exact count_request_unique hL q (by have := q.fits; omega) (by have := q.fits; omega)
      (by simpa using hc) (by simpa using hd)

/-- Exact native-stream balance permits at most one buffered parser record. -/
theorem buffered_provider_capacity {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (ps : List (Nat × Nat)) (ss : Nat × Nat → List Nat)
    (hp : ((List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false)).Perm
      (ps.flatMap (fun p => if tr.cell tt p.1 Candidates.ValueTable.mBuffer=1 then
        Parser.nativeShardMessages (tr.cell tt p.1 Candidates.ValueTable.tau) (ss p) else []))) :
    (ps.filter (fun p => decide (tr.cell tt p.1 Candidates.ValueTable.mBuffer=1))).length≤1 := by
  have hf := (hp.filter isShardCount).length_eq
  have he : (ps.flatMap (fun p => if tr.cell tt p.1 Candidates.ValueTable.mBuffer=1 then
      Parser.nativeShardMessages (tr.cell tt p.1 Candidates.ValueTable.tau) (ss p) else [])).filter isShardCount=
      ps.flatMap (fun p => if tr.cell tt p.1 Candidates.ValueTable.mBuffer=1 then
        [[tr.cell tt p.1 Candidates.ValueTable.tau,0,8,((ss p).length:Fp)]] else []) := by
    rw [List.filter_flatMap]
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp'
    by_cases hm : tr.cell tt p.1 Candidates.ValueTable.mBuffer=1
    · simp only [hm,ite_true,native_shard_count_filter]
    · simp only [hm,ite_false,List.filter_nil]
  rw [he] at hf
  have hs := selected_length ps (fun p => decide (tr.cell tt p.1 Candidates.ValueTable.mBuffer=1))
    (fun p => [tr.cell tt p.1 Candidates.ValueTable.tau,0,8,((ss p).length:Fp)])
  simp only [decide_eq_true_eq] at hs
  rw [hs] at hf
  rw [←hf]
  exact walk_count_capacity hL q

/-- Any two buffered providers in a balanced native stream are the same record. -/
theorem buffered_provider_unique {tr : Trace Fp} {tt : Nat} {ps : List (Nat × Nat)}
    (hcap : (ps.filter (fun p => decide (tr.cell tt p.1 Candidates.ValueTable.mBuffer=1))).length≤1)
    {p p' : Nat × Nat} (hp : p∈ps) (hp' : p'∈ps)
    (hm : tr.cell tt p.1 Candidates.ValueTable.mBuffer=1)
    (hm' : tr.cell tt p'.1 Candidates.ValueTable.mBuffer=1) : p=p' := by
  have hx : p∈ps.filter (fun p => decide (tr.cell tt p.1 Candidates.ValueTable.mBuffer=1)) :=
    List.mem_filter.mpr ⟨hp,by simp [hm]⟩
  have hy : p'∈ps.filter (fun p => decide (tr.cell tt p.1 Candidates.ValueTable.mBuffer=1)) :=
    List.mem_filter.mpr ⟨hp',by simp [hm']⟩
  generalize ps.filter (fun p => decide (tr.cell tt p.1 Candidates.ValueTable.mBuffer=1))=l at hcap hx hy
  cases l with
  | nil => simp at hx
  | cons x xs =>
    cases xs with
    | nil => simpa using (List.mem_singleton.mp hx).trans (List.mem_singleton.mp hy).symm
    | cons y ys => simp at hcap

end ZkFormal.NearV3.Qv.Extract
