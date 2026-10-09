import ZkFormal.NearV3.Candidates.SizeRecordMessages
namespace ZkFormal.NearV3.Candidates.SizeRecordTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open Rcpt.Candidates.SizeCount SizeRecordMessages HorizontalTraffic
set_option maxHeartbeats 400000
set_option maxRecDepth 32768

theorem node_filter : nodeTable.interactions.filter (fun i=>i.bus==B_SIZE)=[nodeInteraction] := rfl
theorem value_filter : valTable.interactions.filter (fun i=>i.bus==B_SIZE)=[valueInteraction] := rfl

private theorem filter_row (is : List Interaction) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (b : Nat) (sd : Bool) (m : List Fp) :
    rowCount is tr t r pub b sd m=
      rowCount (is.filter (fun i=>i.bus==b)) tr t r pub b sd m := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases h : i.bus=b
    · simpa [rowCount,h] using congrArg (fun n=>(if i.send=sd ∧ i.msgVal tr t r pub=m then i.multNat tr t r pub else 0)+n) ih
    · simpa [rowCount,h] using ih

theorem node_off (es : List NodeS3) (t r : Nat) (pub : List Fp) (hr : r≠NodeGen3.R es) :
    nodeInteraction.multNat (TrieCountHeight.node es pub) t r pub=0 := by
  have h : (TrieCountHeight.node es pub).cell t r NodeV3.sumr=0 := by
    change (if NodeV3.sumr=nodeCount then CountLift.tally (TrieHeight.node es) nodeIncrement t r pub else Fp.ofNat (NodeGen3.cell es (2^22) r NodeV3.sumr))=0
    rw [if_neg (by decide)]
    by_cases hl : r<NodeGen3.R es
    · rw [NodeGen3.cell_node hl]
      change Fp.ofNat (NodeGen3.rowCell es ((NodeGen3.recsOf es).getD r default) 3)=0
      rw [NodeGen3.Rc.c3]; rfl
    · rw [NodeGen3.cell_pad (by omega)]
      rfl
  change (if (TrieCountHeight.node es pub).cell t r NodeV3.sumr=1 then 1 else 0)+0=0
  rw [h]; decide

theorem value_off (es : List ValE) (t r : Nat) (pub : List Fp) (hr : r≠ValGen.R es) :
    valueInteraction.multNat (TrieCountHeight.value es pub) t r pub=0 := by
  have h : (TrieCountHeight.value es pub).cell t r ValV3.sumr=0 := by
    change (if ValV3.sumr=valCount then CountLift.tally (TrieHeight.value es) valIncrement t r pub else Fp.ofNat (ValGen.cell es (2^22) r ValV3.sumr))=0
    rw [if_neg (by decide)]
    simp [ValGen.cell,ValV3.sumr,hr,ValGen.recCell]
    rfl
  change (if (TrieCountHeight.value es pub).cell t r ValV3.sumr=1 then 1 else 0)+0=0
  rw [h]; decide

private theorem single_row (i : Interaction) (is : List Interaction) (hf : is.filter (fun j=>j.bus==B_SIZE)=[i])
    (hb : i.bus=B_SIZE) (hs : i.send=true) (tr : Trace Fp) (t r q : Nat) (pub : List Fp)
    (sd : Bool) (m msg : List Fp)
    (hm : i.msgVal tr t q pub=msg) (hon : i.multNat tr t q pub=1)
    (hoff : r≠q → i.multNat tr t r pub=0) :
    rowCount is tr t r pub B_SIZE sd m=if r=q ∧ sd=true ∧ msg=m then 1 else 0 := by
  rw [filter_row,hf]
  by_cases h : r=q
  · subst r
    simp [rowCount,hb,hs,hm,hon,and_comm]
  · simp [rowCount,hb,hs,h,hoff h]

private theorem delta_sum (q H : Nat) (hq : q<H) (p : Prop) [Decidable p] :
    ((List.range H).map (fun r=>if r=q ∧ p then 1 else 0)).sum=if p then 1 else 0 := by
  induction H with
  | zero => omega
  | succ H ih =>
    rw [List.range_succ,List.map_append,List.sum_append]
    by_cases h : q<H
    · rw [ih h]
      simp [show H≠q by omega]
    · have he : q=H := by omega
      subst q
      have hz : ((List.range H).map (fun r=>if r=H ∧ p then 1 else 0)).sum=0 := by
        have hm : (List.range H).map (fun r=>if r=H ∧ p then 1 else 0)=(List.range H).map (fun _=>0) := by
          apply List.map_congr_left
          intro r hr
          simp [show r≠H by have := List.mem_range.mp hr; omega]
        rw [hm]
        exact ValProof.sum_map_zero' _
      rw [hz]
      simp

def nodeMessage (es : List NodeS3) : List Fp :=
  [Fp.ofNat 0,Fp.ofNat (((es.filter fun e=>!e.dup).map fun e=>(e.v.ser false).length).sum),
   Fp.ofNat (es.filter fun e=>!e.dup).length]
def valueMessage (es : List ValE) : List Fp :=
  [Fp.ofNat 1,Fp.ofNat (((es.filter fun e=>!e.vz && !e.dup).map ValE.len).sum),
   Fp.ofNat (es.filter fun e=>!e.dup).length]

theorem node_traffic (es : List NodeS3) (ok : NodeOk es) (t : Nat) (pub : List Fp)
    (sd : Bool) (m : List Fp) :
    tableBusCount nodeTable.interactions (TrieCountHeight.node es pub) t pub B_SIZE sd m=
      if sd=true ∧ nodeMessage es=m then 1 else 0 := by
  rw [table_sum]
  have hr : NodeGen3.R es<(TrieCountHeight.node es pub).height t := by
    have h := ok.rows
    rw [←NodeGen3.R_eq ok] at h
    change NodeGen3.R es<2^22
    omega
  have he : ∀r,rowCount nodeTable.interactions (TrieCountHeight.node es pub) t r pub B_SIZE sd m=
      if r=NodeGen3.R es ∧ sd=true ∧ nodeMessage es=m then 1 else 0 := by
    intro r
    exact single_row nodeInteraction _ node_filter rfl rfl _ t r _ pub sd m _
      (node_message es t pub) (node_multiplicity es t pub) (node_off es t r pub)
  simp only [he]
  exact delta_sum _ _ hr _

theorem value_traffic (es : List ValE) (ok : ValOk es) (t : Nat) (pub : List Fp)
    (sd : Bool) (m : List Fp) :
    tableBusCount valTable.interactions (TrieCountHeight.value es pub) t pub B_SIZE sd m=
      if sd=true ∧ valueMessage es=m then 1 else 0 := by
  rw [table_sum]
  have hr : ValGen.R es<(TrieCountHeight.value es pub).height t := by
    have h := ok.wf.rows
    change ValGen.R es+1≤2^22 at h
    change ValGen.R es<2^22
    omega
  have he : ∀r,rowCount valTable.interactions (TrieCountHeight.value es pub) t r pub B_SIZE sd m=
      if r=ValGen.R es ∧ sd=true ∧ valueMessage es=m then 1 else 0 := by
    intro r
    exact single_row valueInteraction _ value_filter rfl rfl _ t r _ pub sd m _
      (value_message es ok t pub) (value_multiplicity es t pub) (value_off es t r pub)
  simp only [he]
  exact delta_sum _ _ hr _
end ZkFormal.NearV3.Candidates.SizeRecordTraffic
