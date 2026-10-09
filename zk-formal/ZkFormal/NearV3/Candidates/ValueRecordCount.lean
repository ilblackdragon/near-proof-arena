import ZkFormal.NearV3.Candidates.TrieCountTraffic

namespace ZkFormal.NearV3.Candidates.ValueRecordCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open Rcpt.Candidates.SizeCount
set_option maxHeartbeats 400000
set_option maxRecDepth 32768

def weight (es : List ValE) (tp : Nat×Nat) : Nat :=
  if tp.2=0 ∧ (ValGen.ent es tp.1).dup=false then 1 else 0

private theorem keep_sum (es : List ValE) :
    (es.map (fun e=>if e.dup then 0 else 1)).sum=(es.filter (fun e=>!e.dup)).length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases he : e.dup <;> simp [he,ih] <;> omega

/-- Every nonduplicate record contributes once, including an empty value. -/
theorem record_count (es : List ValE) (ok : ValOk es) :
    ((ValGen.recs es).map (weight es)).sum=(es.filter (fun e=>!e.dup)).length := by
  rw [ValGen.recs,ValGen.sum_flatMap']
  have hm : (List.range es.length).map (fun t=>
      (((List.range (ValGen.nOf (ValGen.ent es t))).map (fun p=>(t,p))).map (weight es)).sum)=
      (List.range es.length).map (fun t=>if (ValGen.ent es t).dup then 0 else 1) := by
    apply List.map_congr_left
    intro t ht
    have hn := ValGen.nOf_pos ok (List.mem_range.mp ht)
    obtain ⟨n,he⟩ : ∃n,ValGen.nOf (ValGen.ent es t)=n+1 := ⟨ValGen.nOf (ValGen.ent es t)-1,by omega⟩
    rw [he,List.range_succ_eq_map]
    cases hd : (ValGen.ent es t).dup <;>
      simp [weight,hd,List.map_map,Function.comp_def,ValProof.sum_map_zero']
  rw [hm]
  change ((List.range es.length).map (fun t=>(fun e : ValE=>if e.dup then 0 else 1) (es.getD t default))).sum=_
  rw [ValGen.map_getD default (fun e : ValE=>if e.dup then 0 else 1) es,keep_sum]

/-- Physical increment at every actual record row. -/
theorem increment (es : List ValE) (t r : Nat) (pub : List Fp) (hr : r<ValGen.R es) :
    valIncrement.eval (TrieHeight.value es) t r pub=
      Fp.ofNat (weight es ((ValGen.recs es).getD r default)) := by
  change Fp.ofNat (ValGen.cell es (2^22) r ValV3.vf)*
    (Fp.ofNat 1+ -Fp.ofNat (ValGen.cell es (2^22) r ValV3.dup))=_
  simp only [ValGen.cell,ValV3.vf,ValV3.dup,Nat.reduceEqDiff,ite_false,if_pos hr,
    ValGen.recCell,weight]
  split <;> split <;> simp_all <;> decide

private theorem field_sum (ns : List Nat) : (ns.map Fp.ofNat).sum=Fp.ofNat ns.sum := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons,List.sum_cons,ih,ofNat_add']

/-- The honest added count column at the actual SUM row contains the exact
number of stored value records, not the byte count or nonempty count. -/
theorem value_counter (es : List ValE) (ok : ValOk es) (t : Nat) (pub : List Fp) :
    (TrieCountHeight.value es pub).cell t (ValGen.R es) valCount=
      Fp.ofNat (es.filter (fun e=>!e.dup)).length := by
  change CountLift.tally (TrieHeight.value es) valIncrement t (ValGen.R es) pub=_
  unfold CountLift.tally
  have hm : (List.range (ValGen.R es)).map (fun r=>valIncrement.eval (TrieHeight.value es) t r pub)=
      (List.range (ValGen.R es)).map (fun r=>Fp.ofNat (weight es ((ValGen.recs es).getD r default))) := by
    apply List.map_congr_left
    intro r hr
    exact increment es t r pub (List.mem_range.mp hr)
  rw [hm,←ValGen.recs_length es]
  rw [ValGen.map_getD default (fun tp=>Fp.ofNat (weight es tp))]
  have hs := field_sum ((ValGen.recs es).map (weight es))
  simp only [List.map_map,Function.comp_def] at hs
  rw [hs,record_count es ok]

theorem record_count_bound (es : List ValE) (ok : ValOk es) :
    (es.filter (fun e=>!e.dup)).length≤ValGen.R es := by
  have hb : ∀xs : List (Nat×Nat),(xs.map (weight es)).sum≤xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hw : weight es x≤1 := by unfold weight; split <;> omega
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  have h := hb (ValGen.recs es)
  rwa [record_count es ok,ValGen.recs_length] at h

/-- The natural count is below the field modulus: the SIZE count is not merely
a congruence that could hide additional records. -/
theorem value_counter_nat (es : List ValE) (ok : ValOk es) (t : Nat) (pub : List Fp) :
    ((TrieCountHeight.value es pub).cell t (ValGen.R es) valCount).toNat=
      (es.filter (fun e=>!e.dup)).length := by
  rw [value_counter es ok,Fp.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb := record_count_bound es ok
  have hr := ok.wf.rows
  change ValGen.R es+1≤2^22 at hr
  unfold ZkFormal.Algebra.P
  omega

end ZkFormal.NearV3.Candidates.ValueRecordCount
