import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueMessages
import ZkFormal.NearV3.Render.ValRender
namespace ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl Render

/-- The only new message is a fixed empty digest on enabled empty-value rows. -/
theorem row (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic [emptyInteraction] tr t r pub bus sd=
      if bus=B_DIGEST ∧ sd=true ∧ tr.cell t r ValV3.vz=1 then
        [[(K_VPRE : Fp)+16*tr.cell t r ValV3.vid,0]++emptyHash.map Fp.ofNat] else [] := by
  simp only [rowTraffic,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    emptyInteraction,send,Interaction.multNat,Interaction.multNat.go,eval_c,
    Nat.pow_zero,Nat.add_zero,Interaction.msgVal,List.map_append,List.map_cons,List.map_nil,
    List.map_map]
  by_cases hb:bus=B_DIGEST ∧ sd=true
  · have hx:B_DIGEST=bus ∧ true=sd:=⟨hb.1.symm,hb.2.symm⟩
    simp only [hx,ite_true]
    by_cases hv:tr.cell t r ValV3.vz=1
    · simp only [hb,hv,ite_true,List.replicate_one]
      simp only [mid,smul,eval_add,eval_mul,eval_k,List.map_map,Function.comp_def,natCast_eq]
      simp only [and_self,ite_true]
      rfl
    · simp [hb,hv]
  · have hx:¬(B_DIGEST=bus ∧ true=sd):=fun h=>hb ⟨h.1.symm,h.2.symm⟩
    by_cases hbb:bus=B_DIGEST
    · have hs:sd=false:=by cases sd <;> simp_all
      simp [hs]
    · simp [hbb,Ne.symm hbb]

theorem row_other (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (h:bus≠B_DIGEST ∨ sd=false) : rowTraffic [emptyInteraction] tr t r pub bus sd=[] := by
  rw [row]
  rcases h with h|h <;> simp [h]

theorem row_append (T : Air.Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic (T.interactions++[emptyInteraction]) tr t r pub bus sd=
      rowTraffic T.interactions tr t r pub bus sd++rowTraffic [emptyInteraction] tr t r pub bus sd := by
  simp only [rowTraffic,List.flatMap_append]

/-- Every other bus, including all SIZE/length announcements and all receives,
retains precisely the old physical multiplicities. -/
theorem other_counts (T : Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (msg : List Fp) (h:bus≠B_DIGEST ∨ sd=false) :
    tableBusCount (T.interactions++[emptyInteraction]) tr t pub bus sd msg=
      tableBusCount T.interactions tr t pub bus sd msg := by
  simp only [tableBusCount_eq,row_append,row_other tr _ _ pub bus sd h,List.append_nil]

/-- Exact contribution of one honest record row. -/
theorem generated_row (es : List ValE) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ x, x<15 → tr.cell t r x=Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    rowTraffic [emptyInteraction] tr t r pub B_DIGEST true=
      if r<ValGen.R es then
        let e:=ValGen.ent es ((ValGen.recs es).getD r default).1
        (if e.vz then [emptyMsg e.vid] else []).map Msg.toFp
      else [] := by
  rw [row]
  rw [hc ValV3.vz (by decide),hc ValV3.vid (by decide)]
  by_cases hr:r<ValGen.R es
  · simp only [ValGen.cell,ValV3.vz,ValV3.vid,hr,ite_true,
      show (7:Nat)≠11 by decide,show (3:Nat)≠11 by decide,ite_false,ValGen.recCell]
    generalize ValGen.ent es ((ValGen.recs es).getD r default).1=e
    cases he:e.vz <;>
      simp [he,Render.UniqLocal.ofNat0,Render.UniqLocal.ofNat1,emptyMsg,digMsg,
        Msg.toFp,ValTraffic.eid_eq,eidV,natCast_eq]
    exact ValTraffic.eid_eq _
  · simp [ValGen.cell,ValV3.vz,ValV3.vid,hr,Render.UniqLocal.ofNat0]

/-- Every empty record contributes exactly one message; a nonempty record
contributes none even if its byte sequence contains zero bytes. -/
theorem record_rows (e : ValE) :
    ((List.range (ValGen.nOf e)).flatMap (fun _=>if e.vz then [emptyMsg e.vid] else []))=
      (if e.vz then [emptyMsg e.vid] else []) := by
  cases he:e.vz <;> simp [he,ValGen.nOf,List.range_succ]

open ZkFormal.Near.Render in
theorem generated_messages (es : List ValE) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hcap : ValGen.R es≤tr.height t)
    (hc : ∀ r x,r<tr.height t → x<15 →
      tr.cell t r x=Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    (List.range (tr.height t)).flatMap (fun r=>rowTraffic [emptyInteraction] tr t r pub B_DIGEST true)=
      (es.flatMap (fun e=>if e.vz then [emptyMsg e.vid] else [])).map Msg.toFp := by
  have ha : (List.range (ValGen.R es)).flatMap (fun r=>rowTraffic [emptyInteraction] tr t r pub B_DIGEST true)=
      (es.flatMap (fun e=>if e.vz then [emptyMsg e.vid] else [])).map Msg.toFp := by
    rw [flatMap_congr' (g:=fun r=>
      (if (ValGen.ent es ((ValGen.recs es).getD r default).1).vz then
        [emptyMsg (ValGen.ent es ((ValGen.recs es).getD r default).1).vid] else []).map Msg.toFp)
      (by intro r hr;rw [generated_row es tr t r pub (by intro x hx;exact hc r x (by have :=List.mem_range.mp hr;omega) hx)];simp [List.mem_range.mp hr]),
      ←ValGen.recs_length,←flatMap_getD default (ValGen.recs es) (fun p=>
        (if (ValGen.ent es p.1).vz then [emptyMsg (ValGen.ent es p.1).vid] else []).map Msg.toFp)]
    simp only [ValGen.recs,List.flatMap_assoc,List.flatMap_map,←List.map_flatMap]
    rw [flatMap_congr' (g:=fun j=>if (ValGen.ent es j).vz then [emptyMsg (ValGen.ent es j).vid] else [])
      (by intro j hj;exact record_rows _)]
    congr 1
    exact (flatMap_getD default es (fun e=>if e.vz then [emptyMsg e.vid] else [])).symm
  rw [range_split hcap,List.flatMap_append,ha]
  have hz : (List.map (fun x=>ValGen.R es+x) (List.range (tr.height t-ValGen.R es))).flatMap
      (fun r=>rowTraffic [emptyInteraction] tr t r pub B_DIGEST true)=[] := by
    apply flatMap_nil'
    intro r hr
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hr
    rw [generated_row es tr t _ pub (by intro col hcol;exact hc _ col (by have :=List.mem_range.mp hx;omega) hcol)]
    simp [show ¬ValGen.R es+x<ValGen.R es by omega]
  rw [hz,List.append_nil]

private theorem count_split {α β : Type} [BEq β] [LawfulBEq β]
    (xs : List α) (f g : α→List β) (m : β) :
    (xs.flatMap (fun x=>f x++g x)).count m=(xs.flatMap f).count m+(xs.flatMap g).count m := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.flatMap_cons,List.count_append] at *;omega

theorem append_counts (T : Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount (T.interactions++[emptyInteraction]) tr t pub bus sd msg=
      tableBusCount T.interactions tr t pub bus sd msg+
      tableBusCount [emptyInteraction] tr t pub bus sd msg := by
  simp only [tableBusCount_eq,row_append]
  exact count_split _ _ _ _

theorem generated_count (es : List ValE) (hw : ValWf es) (tr : Trace Fp) (t : Nat)
    (pub msg : List Fp) (hcap : ValGen.R es≤tr.height t)
    (hc : ∀ r x,r<tr.height t → x<15 →
      tr.cell t r x=Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    tableBusCount [emptyInteraction] tr t pub B_DIGEST true msg=
      ((emptyMessages es).map Msg.toFp).count msg := by
  rw [tableBusCount_eq,generated_messages es tr t pub hcap hc]
  congr 2
  apply ZkFormal.Near.Render.flatMap_congr'
  intro e he
  have hs:=hw.shape e he
  cases hz:e.vz
  · have hb:e.bytes≠[]:=by intro h;have hh:=hs.2 hz;simp [h] at hh;omega
    simp [hz,hb]
  · simp [hz,(hs.1 hz).2]

end ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
