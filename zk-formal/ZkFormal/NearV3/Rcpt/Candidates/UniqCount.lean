import ZkFormal.NearV3.Rcpt.Candidates.UniqRepresentatives

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 Link3

private theorem digs_count (s : NodeS3) :
    (digsOf s).length=32*(s.v.revealed.length+(vparMsg s).length) := by
  unfold digsOf vparMsg
  rw [List.length_append,len_flatMap_eq _ 32 (by simp)]
  cases hv : s.v.value with
  | none => simp [hv]
  | some v => rcases v with ⟨i,l,pre,po,w⟩; simp [hv]; omega

private theorem nodes_digs_count (xs : List (NodeS3×Nat)) :
    (xs.flatMap (fun x => digsOf x.1)).length=
      32*((xs.flatMap (fun x => x.1.v.revealed.map fun v =>
        [v.1,x.1.tau,x.1.depth+1,v.2.1,v.2.2.1])).length+
        (xs.flatMap fun x => vparMsg x.1).length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map]
    rw [digs_count,ih]
    omega

/-- DIGS/PARENT/VPARENT exact balances determine uniqueness-row cardinality.
This is equality, not the earlier coarse row-cap bound. -/
theorem uniq_count_exact {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE}
    (hb : ParentBal vs hs) (hv : VParentBal vs es) (hd : DigsBal vs hs us) :
    us.length=vs.length+es.length := by
  have hp := (List.perm_iff_count.mpr hb).length_eq
  have hval := (List.perm_iff_count.mpr hv).length_eq
  have hdig := hd.length_eq
  simp only [List.length_map,List.length_append,parentR,headS,List.length_map,
    List.length_zip,List.length_range,Nat.min_self] at hp
  simp only [List.length_map,vparentR,List.length_map] at hval
  have hn := nodes_digs_count (vs.zip (List.range vs.length))
  rw [←digsN,←parentS,←vparentS] at hn
  have hh : (headSends hs B_DIGS).length=32*hs.length := by
    rw [digsHs]
    exact len_flatMap_eq _ 32 (by simp [digsH]) hs
  have hu : (uniqRecvs us B_DIGS).length=32*us.length := by
    rw [digsR]
    exact len_flatMap_eq _ 32 (by simp) us
  simp only [List.length_map,List.length_append,hn,hh,hu] at hdig
  omega

private theorem node_dup_count (xs : List (NodeS3×Nat)) :
    (xs.filterMap (fun (s,n) => if s.dup then some [eidN n,s.repE] else none)).length=
      ((xs.map Prod.fst).filter NodeS3.dup).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨s,n⟩
    cases h : s.dup <;> simp [h,ih]

private theorem val_dup_count (es : List ValE) :
    (es.flatMap (fun e => if e.dup then [[eidV e,e.repE]] else [])).length=
      (es.filter ValE.dup).length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases h : e.dup <;> simp [h,ih]

private theorem filter_complement {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length+(xs.filter (fun x => !p x)).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

/-- Actual DUP multiplicity fixes the exact number of skipped node/value
records; field-message collisions do not affect this cardinality identity. -/
theorem duplicate_count_exact {vs : List NodeS3} {es : List ValE} {us : List UniqE}
    (hd : DupBal us vs es) :
    (us.filter (fun e => e.eq==1)).length=
      (vs.filter NodeS3.dup).length+(es.filter ValE.dup).length := by
  have hh := hd.length_eq
  rw [dupS,dupR] at hh
  simp only [List.length_map,List.length_append,node_dup_count,val_dup_count,
    List.map_fst_zip (show vs.length≤(List.range vs.length).length by simp)] at hh
  exact hh

/-- The number of nonduplicate uniqueness representatives equals the counts
that the candidate Node/Val tables charge, with empty values included. -/
theorem nondup_count_exact {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE}
    (hu : UniqWf us) (hb : ParentBal vs hs) (hv : VParentBal vs es)
    (hg : DigsBal vs hs us) (hd : DupBal us vs es) :
    (us.filter (fun e => e.eq==0)).length=
      (vs.filter (fun s => !s.dup)).length+(es.filter (fun e => !e.dup)).length := by
  have ht := uniq_count_exact hb hv hg
  have hdup := duplicate_count_exact hd
  have hn := filter_complement vs NodeS3.dup
  have he := filter_complement es ValE.dup
  have hz := filter_complement us (fun e => e.eq==1)
  have hp : us.filter (fun e => !(e.eq==1))=us.filter (fun e => e.eq==0) := by
    apply List.filter_congr
    intro e hem
    have hh := (hu.canon e hem).2.2.2.2.1
    have hc : e.eq=0 ∨ e.eq=1 := by omega
    rcases hc with hc|hc <;> simp [hc]
  rw [hp] at hz
  omega

end ZkFormal.NearV3.Rcpt.Candidates
