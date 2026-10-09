import ZkFormal.NearV3.Candidates.ProcRawNativeBytesList
namespace ZkFormal.NearV3.Candidates.ProcRawRecordTraffic
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

theorem row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      tr t r pub 75 true=List.replicate (if tr.cell t r ProcPriorRawFrame.rec=1 then 1 else 0)
      [tr.cell t r ProcPriorRawFrame.tau,tr.cell t r ProcPriorRawFrame.record,
       tr.cell t r ProcPriorRawFrame.offset,tr.cell t r ProcPriorRawFrame.byte] := by
  simp [rowTraffic,ProcPriorRawFrame.interactions,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,B_VBYTES]

theorem encoded_byte (raw : Bytes) (st : State) (hd:State.decode raw=some st)
    (j g : Nat) (r : LinkAllowance) (hj:st.links[j]?=some r) (hg:g<24) :
    st.encode.getD (5+24*j+g) 0=r.encode.getD g 0 := by
  have hs:=ProcPriorBytes.decoded_record_slice raw st hd j r hj
  have he:raw=st.encode:=(ProcPriorDecode.decode_exact raw st hd).2.2.2
  have h:=congrArg (fun xs:Bytes=>xs.getD g 0) hs
  rw [he] at h
  simpa only [List.getD,List.getElem?_take_of_lt hg,List.getElem?_drop] using h

theorem native_record (b : NativeBlock) (hb:b.Valid) (j g : Nat) (r : LinkAllowance)
    (hj:b.old.links[j]?=some r) (hg:g<24) :
    ProcRawConcatTraffic.messages (blockCell b (5+24*j+g)) 75 true=
      [[Fp.ofNat b.run.tau,Fp.ofNat j,Fp.ofNat g,Fp.ofNat (r.encode.getD g 0).toNat]] := by
  have hji:j<b.old.links.length:=List.getElem?_eq_some_iff.mp hj |>.1
  have hi:5+24*j+g<blockLength b:=by unfold blockLength ProcPriorRawSlots.length; omega
  rw [ProcRawPresenceList.active_cell b _ hi,←ProcRawConcatTraffic.row_messages _ 0 _ [] 75 true,row]
  have hd:=hb.2.2.2.1
  have he:b.old.encode.getD (5+24*j+g) 0=r.encode.getD g 0 := by
    cases hp:b.prior with
    | none =>
      rw [hp] at hd
      have hz:b.old=State.initial:=(Option.some.inj hd).symm
      simp [hz,State.initial] at hj
    | some raw =>
      rw [hp] at hd
      exact encoded_byte raw b.old hd j g r hj hg
  simp [ProcRawInstancePresence.traceAt,ProcPriorRawGen.trace,
    ProcPriorRawSlots.record _ _ _ hji hg,ProcPriorRawGen.cells,
    ProcPriorRawGen.isRecord,ProcPriorRawGen.record,ProcPriorRawGen.offset,
    ProcPriorCells.bit,ProcPriorRawFrame.rec,ProcPriorRawFrame.tau,
    ProcPriorRawFrame.record,ProcPriorRawFrame.offset,ProcPriorRawFrame.byte,
    ProcPriorRawFrame.act,he]
  all_goals grind
end ZkFormal.NearV3.Candidates.ProcRawRecordTraffic
