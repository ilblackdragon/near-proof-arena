import ZkFormal.NearV3.Candidates.ProcRawRecordPhysical
import ZkFormal.NearV3.Candidates.ProcCodecSanityTraffic
namespace ZkFormal.NearV3.Candidates.ProcRawSanityTraffic
open ProcPriorLookup ProcPriorDecode
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

theorem row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75) tr t r pub 74 true=
      List.replicate (if tr.cell t r ProcPriorRawFrame.hash=1 then 1 else 0)
        [tr.cell t r ProcPriorRawFrame.tau,tr.cell t r ProcPriorRawFrame.offset,tr.cell t r ProcPriorRawFrame.byte] := by
  simp [rowTraffic,ProcPriorRawFrame.interactions,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,B_VBYTES]

theorem encoded_hash (st : State) (g : Nat) :
    st.encode.getD (5+24*st.links.length+g) 0=st.sanityHash.getD g 0 := by
  have all (rs : List LinkAllowance):(concatAll (rs.map LinkAllowance.encode)).length=24*rs.length:=by
    induction rs with
    | nil=>rfl
    | cons r rs ih=>simp only [List.map_cons,NearSpec.concatAll,List.length_append,ProcPriorBytes.link_length,List.length_cons,ih];omega
  have hl:=all st.links
  have hh:(([0]++u32 st.links.length)++concatAll (st.links.map LinkAllowance.encode)).length=
      5+24*st.links.length:=by simp [hl,u32,canon_leN_length];omega
  change ((([0]++u32 st.links.length)++concatAll (st.links.map LinkAllowance.encode))++st.sanityHash).getD _ 0=_
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),hh]
  simp only [Nat.add_sub_cancel_left]
  rfl

theorem header_silent (b : NativeBlock) (g : Nat) (hg:g<5) :
    ProcRawConcatTraffic.messages (blockCell b g) 74 true=[] := by
  change rowTraffic _ _ _ _ _ _ _=[]
  rw [row]
  simp [blockCell,ProcRawConcatBoundary.stamp,ProcPriorRawGen.trace,
    ProcPriorRawSlots.header _ _ hg,ProcPriorRawGen.cells,ProcPriorRawGen.isHash,
    ProcPriorCells.bit,ProcPriorRawFrame.hash,ProcPriorRawFrame.tau]

theorem record_silent (b : NativeBlock) (j g : Nat) (hj:j<b.old.links.length) (hg:g<24) :
    ProcRawConcatTraffic.messages (blockCell b (5+24*j+g)) 74 true=[] := by
  change rowTraffic _ _ _ _ _ _ _=[]
  rw [row]
  simp [blockCell,ProcRawConcatBoundary.stamp,ProcPriorRawGen.trace,
    ProcPriorRawSlots.record _ _ _ hj hg,ProcPriorRawGen.cells,ProcPriorRawGen.isHash,
    ProcPriorCells.bit,ProcPriorRawFrame.hash,ProcPriorRawFrame.tau]

theorem hash_message (b : NativeBlock) (g : Nat) (hg:g<32) :
    ProcRawConcatTraffic.messages (blockCell b (5+24*b.old.links.length+g)) 74 true=
    [[Fp.ofNat b.run.tau,Fp.ofNat g,Fp.ofNat (b.old.sanityHash.getD g 0).toNat]] := by
  change rowTraffic _ _ _ _ _ _ _=_
  rw [row]
  simp [blockCell,ProcRawConcatBoundary.stamp,ProcPriorRawGen.trace,
    ProcPriorRawSlots.hash _ _ hg,ProcPriorRawGen.cells,ProcPriorRawGen.isHash,
    ProcPriorRawGen.offset,ProcPriorCells.bit,ProcPriorRawFrame.hash,ProcPriorRawFrame.tau,
    ProcPriorRawFrame.offset,ProcPriorRawFrame.byte]
  exact congrArg (fun x : UInt8=>Fp.ofNat x.toNat) (encoded_hash b.old g)

theorem block (b : NativeBlock) :
    (blockRows b).flatMap (fun row=>ProcRawConcatTraffic.messages row 74 true)=
      (List.range 32).map (fun g=>[Fp.ofNat b.run.tau,Fp.ofNat g,Fp.ofNat (b.old.sanityHash.getD g 0).toNat]) := by
  simp only [blockRows,List.flatMap_map]
  rw [show blockLength b=5+(24*b.old.links.length+32) by
    unfold blockLength ProcPriorRawSlots.length;omega]
  rw [List.range_add,List.flatMap_append,List.flatMap_map]
  have hh:(List.range 5).flatMap (fun g=>ProcRawConcatTraffic.messages (blockCell b g) 74 true)=[]:=by
    apply List.flatMap_eq_nil_iff.mpr
    intro g hg
    exact header_silent b g (List.mem_range.mp hg)
  rw [hh,List.nil_append,List.range_add,List.flatMap_append,List.flatMap_map]
  have hr:(List.range (24*b.old.links.length)).flatMap
      (fun g=>ProcRawConcatTraffic.messages (blockCell b (5+g)) 74 true)=[]:=by
    apply List.flatMap_eq_nil_iff.mpr
    intro g hg
    have hg:=List.mem_range.mp hg
    have he:5+g=5+24*(g/24)+g%24:=by omega
    rw [he]
    exact record_silent b _ _ (by omega) (by omega)
  rw [hr,List.nil_append,List.map_eq_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro g hg
  simpa only [Nat.add_assoc] using hash_message b g (List.mem_range.mp hg)

theorem physical (bs : List NativeBlock) (hcap:(rows bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75) (trace bs) t r pub 74 true)=
    bs.flatMap (fun b=>(List.range 32).map
      (fun g=>[Fp.ofNat b.run.tau,Fp.ofNat g,Fp.ofNat (b.old.sanityHash.getD g 0).toNat])) := by
  rw [ProcRawConcatTraffic.physical bs hcap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  exact block b
end ZkFormal.NearV3.Candidates.ProcRawSanityTraffic
