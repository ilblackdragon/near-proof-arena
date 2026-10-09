import ZkFormal.NearV3.Rcpt.Candidates.UniqWeightedTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec Link3

private theorem node_dup_mass (W : Fp → Nat) (xs : List (NodeS3×Nat)) :
    eidMass W (xs.filterMap (fun (s,n) => if s.dup then some [eidN n,s.repE] else none))=
      ((xs.filter fun x => x.1.dup).map fun x => W (Fp.ofNat (eidN x.2))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨s,n⟩
    cases hd : s.dup <;> simp only [List.filterMap_cons,List.filter_cons,hd,ite_true,ite_false,
      Bool.false_eq_true,Option.toList_some,Option.toList_none,List.map_cons,List.sum_cons,
      List.nil_append,List.singleton_append]
    · exact ih
    · simpa only [eidMass,List.map_cons,List.map_nil,Msg.toFp,List.getD_cons_zero,List.sum_cons] using
        congrArg (W (Fp.ofNat (eidN n))+·) ih

private theorem val_dup_mass (W : Fp → Nat) (es : List ValE) :
    eidMass W (es.flatMap fun e => if e.dup then [[eidV e,e.repE]] else [])=
      ((es.filter ValE.dup).map fun e => W (Fp.ofNat (eidV e))).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases hd : e.dup <;> simp only [List.flatMap_cons,List.filter_cons,hd,ite_true,ite_false,
      Bool.false_eq_true,List.nil_append,List.singleton_append,List.map_cons,List.sum_cons]
    · exact ih
    · simpa only [eidMass,List.map_cons,List.map_nil,Msg.toFp,List.getD_cons_zero,List.sum_cons] using
        congrArg (W (Fp.ofNat (eidV e))+·) ih

theorem duplicate_weight_exact (W : Fp → Nat)
    {vs : List NodeS3} {es : List ValE} {us : List UniqE} (hd : DupBal us vs es) :
    ((us.filter fun e => e.eq==1).map fun e => W (Fp.ofNat e.eid)).sum=
      (((vs.zip (List.range vs.length)).filter fun x => x.1.dup).map
        (fun x => W (Fp.ofNat (eidN x.2)))).sum+
      ((es.filter ValE.dup).map fun e => W (Fp.ofNat (eidV e))).sum := by
  have hh := eidMass_perm W hd
  rw [dupS,dupR,eidMass_append,node_dup_mass,val_dup_mass] at hh
  simpa only [eidMass,List.map_map,Function.comp_def,Msg.toFp,List.map_cons,List.map_nil,
    List.getD_cons_zero] using hh

private theorem split_weight {α : Type} (xs : List α) (p : α → Bool) (W : α → Nat) :
    ((xs.filter p).map W).sum+((xs.filter fun x => !p x).map W).sum=(xs.map W).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp] <;> omega

/-- Actual global DIGS/PARENT/VPARENT/DUP balances preserve arbitrary weights
on nonduplicate representatives, not just their cardinality. -/
theorem nonduplicate_weight_exact (W : Fp → Nat)
    {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE}
    (hu : UniqWf us) (hb : ParentBal vs hs) (hv : VParentBal vs es)
    (hd : DigsBal vs hs us) (hdup : DupBal us vs es) :
    ((us.filter fun e => e.eq==0).map fun e => W (Fp.ofNat e.eid)).sum=
      (((vs.zip (List.range vs.length)).filter fun x => !x.1.dup).map
        (fun x => W (Fp.ofNat (eidN x.2)))).sum+
      ((es.filter fun e => !e.dup).map fun e => W (Fp.ofNat (eidV e))).sum := by
  have hall := uniq_weight_exact W hb hv hd
  have hdu := duplicate_weight_exact W hdup
  have hn := split_weight (vs.zip (List.range vs.length)) (fun x => x.1.dup)
    (fun x => W (Fp.ofNat (eidN x.2)))
  have hvv := split_weight es ValE.dup (fun e => W (Fp.ofNat (eidV e)))
  have huu := split_weight us (fun e => e.eq==1) (fun e => W (Fp.ofNat e.eid))
  have he : us.filter (fun e => !(e.eq==1))=us.filter (fun e => e.eq==0) := by
    apply List.filter_congr
    intro e he
    have hc := (hu.canon e he).2.2.2.2.1
    have hh : e.eq=0 ∨ e.eq=1 := by omega
    rcases hh with hh|hh <;> simp [hh]
  rw [he] at huu
  omega

end ZkFormal.NearV3.Rcpt.Candidates
