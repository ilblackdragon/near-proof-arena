import ZkFormal.NearV3.Rcpt.Candidates.UniqCount

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec Link3

/-- A natural weight on the field-valued entry identifier. No canonical-cast
assumption is needed while transporting the weight across exact buses. -/
def eidMass (W : Fp → Nat) (ms : List Msg) : Nat :=
  ((ms.map Msg.toFp).map fun m => W (m.getD 0 0)).sum

theorem eidMass_perm (W : Fp → Nat) {xs ys : List Msg}
    (h : (xs.map Msg.toFp).Perm (ys.map Msg.toFp)) : eidMass W xs=eidMass W ys :=
  (h.map (fun (m : List Fp) => W (m.getD 0 0))).sum_nat

theorem eidMass_append (W : Fp → Nat) (xs ys : List Msg) :
    eidMass W (xs++ys)=eidMass W xs+eidMass W ys := by
  simp [eidMass,List.map_append,List.sum_append]

private theorem sum_flat {α : Type} (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum=(xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.sum_append,ih]

theorem eidMass_flat {α : Type} (W : Fp → Nat) (xs : List α) (f : α → List Msg) :
    eidMass W (xs.flatMap f)=(xs.map fun x => eidMass W (f x)).sum := by
  simp only [eidMass,List.map_flatMap,sum_flat]

private theorem sum_mul {α : Type} (xs : List α) (f : α → Nat) (n : Nat) :
    (xs.map fun x => n*f x).sum=n*(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,Nat.mul_add]

private theorem sum_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x+g x).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem cast_msgId (kind n : Nat) : (Fp.ofNat (msgId kind n))=(kind:Fp)+16*(n:Fp) := by
  unfold msgId
  rw [←natCast_eq, natCast_add,natCast_mul]
  rfl

/-- A digest's 32 byte rows all carry the same entry weight. -/
theorem digest_mass (W : Fp → Nat) (E tau : Nat) (bytes : List Nat) :
    eidMass W ((List.range 32).map fun j => [E,tau,j,bytes.getD j 0])=32*W (Fp.ofNat E) := by
  simp only [eidMass,List.map_map,Function.comp_def,Msg.toFp,List.map_cons,List.map_nil,List.getD_cons_zero]
  rw [List.map_const',List.sum_replicate_nat,List.length_range]

theorem digs_node_mass (W : Fp → Nat) (s : NodeS3) :
    eidMass W (digsOf s)=32*(
      eidMass (fun e => W ((K_NPRE:Fp)+16*e))
        (s.v.revealed.map fun v => [v.1,s.tau,s.depth+1,v.2.1,v.2.2.1])+
      eidMass (fun e => W ((K_VPRE:Fp)+16*e)) (vparMsg s)) := by
  rw [digsOf,eidMass_append,eidMass_flat]
  have hn : (s.v.revealed.map fun v => eidMass W
      ((List.range 32).map fun i => [msgId K_NPRE v.1,s.tau,i,v.2.2.2.1.getD i 0])).sum=
      32*eidMass (fun e => W ((K_NPRE:Fp)+16*e))
        (s.v.revealed.map fun v => [v.1,s.tau,s.depth+1,v.2.1,v.2.2.1]) := by
    simp only [digest_mass,cast_msgId,sum_mul]
    simp only [eidMass,List.map_map,Msg.toFp,
      List.map_cons,List.map_nil,List.getD_cons_zero,Function.comp_def,natCast_eq]
  rw [hn]
  cases hv : s.v.value with
  | none => simp [hv,vparMsg,eidMass,Nat.mul_add]
  | some v =>
    rcases v with ⟨i,l,pre,po,w⟩
    simp only [hv,digest_mass,cast_msgId]
    simp only [vparMsg,hv,eidMass,List.map_cons,List.map_nil,
      Msg.toFp,List.getD_cons_zero,List.sum_cons,List.sum_nil,Nat.add_zero,natCast_eq]
    rw [Nat.mul_add]

theorem digs_all_mass (W : Fp → Nat) (vs : List NodeS3) (hs : List HeadE) :
    eidMass W (nodeSends3 vs B_DIGS++headSends hs B_DIGS)=
      32*(eidMass (fun e => W ((K_NPRE:Fp)+16*e))
        (nodeSends3 vs B_PARENT++headSends hs B_PARENT)+
        eidMass (fun e => W ((K_VPRE:Fp)+16*e)) (nodeSends3 vs B_VPARENT)) := by
  rw [digsS,parentS,headS,vparentS]
  simp only [eidMass_append,eidMass_flat,digs_node_mass,digsH,digest_mass,
    sum_mul,sum_add,cast_msgId]
  have hh : (hs.map fun h => W ((K_NPRE:Fp)+16*(h.rid:Fp))).sum=
      eidMass (fun e => W ((K_NPRE:Fp)+16*e))
        (hs.map fun h => [h.rid,h.tau,0,h.rlen,h.rres]) := by
    simp only [eidMass,List.map_map,Function.comp_def,Msg.toFp,List.map_cons,
      List.map_nil,List.getD_cons_zero,natCast_eq]
  rw [hh]
  let nw := ((vs.zip (List.range vs.length)).map fun x =>
    eidMass (fun e => W ((K_NPRE:Fp)+16*e))
      (x.1.v.revealed.map fun v => [v.1,x.1.tau,x.1.depth+1,v.2.1,v.2.2.1])).sum
  let vw := ((vs.zip (List.range vs.length)).map fun x =>
    eidMass (fun e => W ((K_VPRE:Fp)+16*e)) (vparMsg x.1)).sum
  let hw := eidMass (fun e => W ((K_NPRE:Fp)+16*e))
    (hs.map fun h => [h.rid,h.tau,0,h.rlen,h.rres])
  change 32*(nw+vw)+32*hw=32*((nw+hw)+vw)
  omega

theorem uniq_weight_exact (W : Fp → Nat)
    {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE}
    (hb : ParentBal vs hs) (hv : VParentBal vs es) (hd : DigsBal vs hs us) :
    (us.map fun e => W (Fp.ofNat e.eid)).sum=
      ((vs.zip (List.range vs.length)).map fun x => W (Fp.ofNat (eidN x.2))).sum+
      (es.map fun e => W (Fp.ofNat (eidV e))).sum := by
  have hp := eidMass_perm (fun e => W ((K_NPRE:Fp)+16*e)) (List.perm_iff_count.mpr hb)
  have hval := eidMass_perm (fun e => W ((K_VPRE:Fp)+16*e)) (List.perm_iff_count.mpr hv)
  have hdig := eidMass_perm W hd
  rw [digs_all_mass,hp,hval,digsR,eidMass_flat] at hdig
  simp only [digest_mass,sum_mul] at hdig
  rw [parentR,vparentR] at hdig
  simp only [eidMass,List.map_map,Function.comp_def,Msg.toFp,List.map_cons,List.map_nil,
    List.getD_cons_zero] at hdig
  have hn : ((vs.zip (List.range vs.length)).map fun x => W (Fp.ofNat (eidN x.2))).sum=
      ((vs.zip (List.range vs.length)).map fun x => W ((K_NPRE:Fp)+16*Fp.ofNat x.2)).sum := by
    simp only [eidN,cast_msgId,natCast_eq]
  have he : (es.map fun e => W (Fp.ofNat (eidV e))).sum=
      (es.map fun e => W ((K_VPRE:Fp)+16*Fp.ofNat e.vid)).sum := by
    simp only [eidV,cast_msgId,natCast_eq]
  rw [hn,he]
  omega

end ZkFormal.NearV3.Rcpt.Candidates
