import ZkFormal.NearV3.Candidates.TrieCountTraffic

namespace ZkFormal.NearV3.Candidates.NodeRecordCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open Rcpt.Candidates.SizeCount
set_option maxHeartbeats 400000
set_option maxRecDepth 32768

def weight (es : List NodeS3) (r : NodeGen3.NRec) : Nat :=
  if r.pos=0 ∧ (NodeGen3.rec es r.n).dup=false then 1 else 0

private theorem keep_sum (es : List NodeS3) :
    (es.map (fun e=>if e.dup then 0 else 1)).sum=(es.filter (fun e=>!e.dup)).length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases he : e.dup <;> simp [he,ih] <;> omega

/-- Every nonduplicate node contributes exactly one record. -/
theorem record_count (es : List NodeS3) :
    ((NodeGen3.recsOf es).map (weight es)).sum=(es.filter (fun e=>!e.dup)).length := by
  rw [NodeGen3.recsOf,ValGen.sum_flatMap']
  have hm : (List.range es.length).map (fun t=>((NodeGen3.nodeRecs es t).map (weight es)).sum)=
      (List.range es.length).map (fun t=>if (NodeGen3.rec es t).dup then 0 else 1) := by
    apply List.map_congr_left
    intro t ht
    have hn : 0<(NodeGen3.layN es t).length := NodeGen3.lay_pos _
    obtain ⟨n,he⟩ : ∃n,(NodeGen3.layN es t).length=n+1 := ⟨(NodeGen3.layN es t).length-1,by omega⟩
    rw [NodeGen3.nodeRecs,he,List.range_succ_eq_map]
    cases hd : (NodeGen3.rec es t).dup <;>
      simp [weight,NodeGen3.mkR,hd,List.map_map,Function.comp_def,ValProof.sum_map_zero']
  rw [hm]
  change ((List.range es.length).map (fun t=>(fun e : NodeS3=>if e.dup then 0 else 1) (es.getD t default))).sum=_
  rw [ValGen.map_getD default (fun e : NodeS3=>if e.dup then 0 else 1) es,keep_sum]

/-- Physical increment at every actual record row. -/
theorem increment (es : List NodeS3) (t r : Nat) (pub : List Fp) (hr : r<NodeGen3.R es) :
    nodeIncrement.eval (TrieHeight.node es) t r pub=
      Fp.ofNat (weight es ((NodeGen3.recsOf es).getD r default)) := by
  change Fp.ofNat (NodeGen3.cell es (2^22) r NodeV3.nf)*
    (Fp.ofNat 1+ -Fp.ofNat (NodeGen3.cell es (2^22) r NodeV3.dup))=_
  rw [NodeGen3.cell_node hr]
  simp only [NodeV3.nf,NodeV3.dup,NodeGen3.Rc.c1,NodeGen3.Rc.c170,weight,NodeGen.b2n]
  split <;> split <;> simp_all <;> decide

private theorem field_sum (ns : List Nat) : (ns.map Fp.ofNat).sum=Fp.ofNat ns.sum := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons,List.sum_cons,ih,ofNat_add']

/-- The honest added count column at the actual SUM row contains the exact
number of stored node records, not the byte count. -/
theorem node_counter (es : List NodeS3) (t : Nat) (pub : List Fp) :
    (TrieCountHeight.node es pub).cell t (NodeGen3.R es) nodeCount=
      Fp.ofNat (es.filter (fun e=>!e.dup)).length := by
  change CountLift.tally (TrieHeight.node es) nodeIncrement t (NodeGen3.R es) pub=_
  unfold CountLift.tally
  have hm : (List.range (NodeGen3.R es)).map (fun r=>nodeIncrement.eval (TrieHeight.node es) t r pub)=
      (List.range (NodeGen3.R es)).map (fun r=>Fp.ofNat (weight es ((NodeGen3.recsOf es).getD r default))) := by
    apply List.map_congr_left
    intro r hr
    exact increment es t r pub (List.mem_range.mp hr)
  rw [hm,←show (NodeGen3.recsOf es).length=NodeGen3.R es from rfl]
  rw [ValGen.map_getD default (fun tp=>Fp.ofNat (weight es tp))]
  have hs := field_sum ((NodeGen3.recsOf es).map (weight es))
  simp only [List.map_map,Function.comp_def] at hs
  rw [hs,record_count es]

theorem record_count_bound (es : List NodeS3) :
    (es.filter (fun e=>!e.dup)).length≤NodeGen3.R es := by
  have hb : ∀xs : List NodeGen3.NRec,(xs.map (weight es)).sum≤xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hw : weight es x≤1 := by unfold weight; split <;> omega
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  have h := hb (NodeGen3.recsOf es)
  rwa [record_count es,show (NodeGen3.recsOf es).length=NodeGen3.R es from rfl] at h

/-- The natural count is below the field modulus: the SIZE count is not merely
a congruence that could hide additional records. -/
theorem node_counter_nat (es : List NodeS3) (ok : NodeOk es) (t : Nat) (pub : List Fp) :
    ((TrieCountHeight.node es pub).cell t (NodeGen3.R es) nodeCount).toNat=
      (es.filter (fun e=>!e.dup)).length := by
  rw [node_counter es,Fp.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb := record_count_bound es
  have hr := ok.wf.rows
  rw [←NodeGen3.R_eq ok] at hr
  unfold ZkFormal.Algebra.P
  omega

end ZkFormal.NearV3.Candidates.NodeRecordCount
