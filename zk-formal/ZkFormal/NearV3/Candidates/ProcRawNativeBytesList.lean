import ZkFormal.NearV3.Candidates.ProcRawPresenceList
namespace ZkFormal.NearV3.Candidates.ProcRawNativeBytesList
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

def priorMessages (b : NativeBlock) : List Msg :=
  match b.prior with
  | none => []
  | some raw => emitAt b.vid 0 (raw.map UInt8.toNat)

theorem block_messages (b : NativeBlock) (hb : b.Valid) :
    (blockRows b).flatMap (fun row=>ProcRawConcatTraffic.messages row B_VBYTES true)=
      (priorMessages b).map Msg.toFp := by
  simp only [blockRows,List.flatMap_map]
  have he:(List.range (blockLength b)).flatMap
      (fun i=>ProcRawConcatTraffic.messages (blockCell b i) B_VBYTES true)=
      (List.range (blockLength b)).flatMap (fun i=>if b.prior.isSome then
        [[Fp.ofNat b.vid,Fp.ofNat i,Fp.ofNat (b.old.encode.getD i 0).toNat]] else []) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    rw [ProcRawPresenceList.active_cell b i (List.mem_range.mp hi)]
    rw [←ProcRawConcatTraffic.row_messages _ 0 i [] B_VBYTES true,
      ProcRawInstancePresence.bytes_row]
    exact ProcPriorRawByteTraffic.active_row b.old b.vid 0 i b.prior.isSome [] (List.mem_range.mp hi)
  rw [he]
  unfold priorMessages
  cases hp:b.prior with
  | none => simp
  | some raw =>
    have hd:=hb.2.2.2.1
    rw [hp] at hd
    have hl:=ProcPriorDecode.decode_length raw b.old hd
    have henc:raw=b.old.encode:=(ProcPriorDecode.decode_exact raw b.old hd).2.2.2
    simp only [Option.isSome_some,ite_true,←List.map_eq_flatMap,
      emitAt,List.length_map,List.map_map,Nat.zero_add]
    rw [show blockLength b=raw.length by exact hl.symm]
    apply List.map_congr_left
    intro i hi
    have hir:i<raw.length:=List.mem_range.mp hi
    simp only [Function.comp_def,Msg.toFp,List.map_cons,List.map_nil]
    rw [←henc]
    simp [List.getD,List.getElem?_eq_getElem hir]

theorem physical (bs : List NativeBlock) (hb:∀b∈bs,b.Valid)
    (hcap:(rows bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace bs) t r pub B_VBYTES true)=
      (bs.flatMap priorMessages).map Msg.toFp := by
  rw [ProcRawConcatTraffic.physical bs hcap]
  rw [List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b h
  exact block_messages b (hb b h)

theorem count (bs : List NativeBlock) (hb:∀b∈bs,b.Valid)
    (hcap:(rows bs).length≤2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace bs) t pub B_VBYTES true msg=cnt (bs.flatMap priorMessages) msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical bs hb hcap t pub)
end ZkFormal.NearV3.Candidates.ProcRawNativeBytesList
