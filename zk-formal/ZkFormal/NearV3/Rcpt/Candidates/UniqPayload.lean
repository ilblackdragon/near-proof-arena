import ZkFormal.NearV3.Rcpt.Candidates.UniqWeightedNondup
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNodeSender
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountValComplete

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec Link3

private theorem value_payload (es : List ValE) (hw : ValWf es) :
    ((es.filter fun e => !e.dup).map fun e => e.bytes.length).sum=SizeCount.valPayload es := by
  have hs := hw.shape
  clear hw
  unfold SizeCount.valPayload
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := hs e (by simp)
    have ht := ih (fun x hx => hs x (by simp [hx]))
    cases hz : e.vz <;> cases hd : e.dup
    · have hh := (he.2 hz).1; simp [hz,hd,hh,ht]
    · simp [hz,hd,ht]
    · have hh := (he.1 hz).2; simp [hz,hd,hh,ht]
    · simp [hz,hd,ht]

/-- Exact byte-weight equality between nonduplicate uniqueness representatives
and the payload totals of the actual node/value SIZE views. -/
theorem nondup_payload_exact
    {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE}
    (hn : NodeWf3 vs) (hval : ValWf es) (hu : UniqWf us)
    (hb : ParentBal vs hs) (hv : VParentBal vs es)
    (hd : DigsBal vs hs us) (hdup : DupBal us vs es) :
    ((us.filter fun e => e.eq==0).map fun e => (bOf vs es e.eid).length).sum=
      SizeCount.nodePayload vs+SizeCount.valPayload es := by
  let W : Fp → Nat := fun E => (bOf vs es E.toNat).length
  have hall := nonduplicate_weight_exact W hu hb hv hd hdup
  have hU : ((us.filter fun e => e.eq==0).map fun e => W (Fp.ofNat e.eid))=
      ((us.filter fun e => e.eq==0).map fun e => (bOf vs es e.eid).length) := by
    apply List.map_congr_left
    intro e he
    have hc := (hu.canon e (List.mem_filter.mp he).1).1
    simp only [W,Fp.toNat_ofNat,Nat.mod_eq_of_lt hc]
  have hN : (((vs.zip (List.range vs.length)).filter fun x => !x.1.dup).map
      (fun x => W (Fp.ofNat (eidN x.2))))=
      (((vs.zip (List.range vs.length)).filter fun x => !x.1.dup).map
        fun x => (x.1.v.ser false).length) := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨hi,he⟩ := mem_zip_range (List.mem_filter.mp hx).1
    rcases x with ⟨s,n⟩
    dsimp only at hi he ⊢
    subst s
    have hid := nid_lt hn hi K_NPRE (by decide)
    simp only [W,eidN,Fp.toNat_ofNat,Nat.mod_eq_of_lt hid,bOf,bN_node vs es hi,toB,List.length_map]
  have hN' : ((((vs.zip (List.range vs.length)).filter fun x => !x.1.dup).map
      fun x => (x.1.v.ser false).length)).sum=SizeCount.nodePayload vs := by
    have hf := List.map_fst_zip (show vs.length≤(List.range vs.length).length by simp)
    conv => rhs; rw [←hf]
    simp [SizeCount.nodePayload,List.filter_map,List.map_map,Function.comp_def]
  have hV : ((es.filter fun e => !e.dup).map fun e => W (Fp.ofNat (eidV e)))=
      ((es.filter fun e => !e.dup).map fun e => e.bytes.length) := by
    apply List.map_congr_left
    intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp (List.mem_filter.mp he).1
    have hv := vid_small hval hi
    have hl := vlen_le hval
    have hid : eidV es[i]<P := by unfold eidV msgId K_VPRE P; rw [hv]; omega
    simp only [W,Fp.toNat_ofNat,Nat.mod_eq_of_lt hid]
    simp only [bOf,eidV,hv,bN_val vs es hi,toB,List.length_map]
  rw [hU,hN,hN',hV,value_payload es hval] at hall
  exact hall

end ZkFormal.NearV3.Rcpt.Candidates
