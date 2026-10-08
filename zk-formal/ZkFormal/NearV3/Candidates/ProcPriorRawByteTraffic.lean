import ZkFormal.NearV3.Candidates.ProcPriorRawChecks
import ZkFormal.NearV3.Candidates.NativeValueByteInventory

namespace ZkFormal.NearV3.Candidates.ProcPriorRawByteTraffic
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorRawGen ProcPriorRawSlots

/-- The selected raw parser's byte bus contains exactly its byte interaction.
Presence and length requests and the two parser streams cannot add byte sends. -/
theorem row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      tr t r pub B_VBYTES true =
    List.replicate (if tr.cell t r ProcPriorRawFrame.byteGate=1 then 1 else 0)
      [tr.cell t r ProcPriorRawFrame.vid,tr.cell t r ProcPriorRawFrame.pos,
       tr.cell t r ProcPriorRawFrame.byte] := by
  simp [rowTraffic,ProcPriorRawFrame.interactions,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    Sched.B_SPOST,B_VBYTES]

/-- Each active parser row supplies its actual encoded byte iff the original
value exists. Missing values do not supply synthetic initial-state bytes. -/
theorem active_row (st : State) (vid t r : Nat) (present : Bool)
    (pub : List Fp) (hr:r<ProcPriorRawSlots.length st.links.length) :
    rowTraffic (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t r pub B_VBYTES true =
    if present then [[Fp.ofNat vid,Fp.ofNat r,Fp.ofNat (st.encode.getD r 0).toNat]] else [] := by
  rw [row]
  rcases coverage st.links.length r hr with ⟨g,hg,_,he⟩|⟨j,g,hj,hg,_,he⟩|⟨g,hg,_,he⟩
  all_goals cases present <;>
    simp [trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.byteGate,
      ProcPriorRawFrame.vid,ProcPriorRawFrame.pos,ProcPriorRawFrame.byte]

theorem padding_row (st : State) (vid t r : Nat) (present : Bool)
    (pub : List Fp) (hr:ProcPriorRawSlots.length st.links.length≤r) :
    rowTraffic (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t r pub B_VBYTES true = [] := by
  rw [row]
  simp [trace,ProcPriorRawSlots.padding _ _ hr,padding_cells]

/-- Complete physical byte inventory, including all padding rows. Capacity is
stated against the original record count, not the current scheduler grid. -/
theorem physical (st : State) (vid t : Nat) (present : Bool) (pub : List Fp)
    (hfit:ProcPriorRawSlots.length st.links.length≤2^22) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t r pub B_VBYTES true) =
    if present then (List.range (ProcPriorRawSlots.length st.links.length)).map
      (fun r=>[Fp.ofNat vid,Fp.ofNat r,Fp.ofNat (st.encode.getD r 0).toNat]) else [] := by
  have he:2^22=ProcPriorRawSlots.length st.links.length+
      (2^22-ProcPriorRawSlots.length st.links.length):=by omega
  have hs:=congrArg List.range he
  rw [List.range_add] at hs
  rw [hs,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-ProcPriorRawSlots.length st.links.length)).flatMap
      (fun j=>rowTraffic (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
        (trace st vid present) t (ProcPriorRawSlots.length st.links.length+j) pub B_VBYTES true)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    exact padding_row st vid t _ present pub (by omega)
  rw [hz,List.append_nil]
  have hp:(List.range (ProcPriorRawSlots.length st.links.length)).flatMap
      (fun r=>rowTraffic (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
        (trace st vid present) t r pub B_VBYTES true)=
      (List.range (ProcPriorRawSlots.length st.links.length)).flatMap
        (fun r=>if present then [[Fp.ofNat vid,Fp.ofNat r,Fp.ofNat (st.encode.getD r 0).toNat]] else []) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro r hr
    exact active_row st vid t r present pub (List.mem_range.mp hr)
  rw [hp]
  cases present <;> simp [←List.map_eq_flatMap]

/-- Successful decoding connects the physical provider to the exact original
bytes, not merely to a same-length replacement encoding. -/
theorem decoded (bs : Bytes) (st : State) (vid t : Nat) (pub : List Fp)
    (hd:State.decode bs=some st) (hfit:bs.length≤2^22) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (trace st vid true) t r pub B_VBYTES true) =
      (emitAt vid 0 (bs.map UInt8.toNat)).map Msg.toFp := by
  have hl:=ProcPriorDecode.decode_length bs st hd
  have he:bs=st.encode:=(ProcPriorDecode.decode_exact bs st hd).2.2.2
  rw [physical st vid t true pub (by unfold ProcPriorRawSlots.length; omega)]
  simp only [ite_true,emitAt,List.length_map,List.map_map,Nat.zero_add]
  rw [show ProcPriorRawSlots.length st.links.length=bs.length by exact hl.symm]
  apply List.map_congr_left
  intro r hr
  have hb:r<bs.length:=List.mem_range.mp hr
  simp only [Function.comp_def,Msg.toFp,List.map_cons,List.map_nil]
  rw [←he]
  simp [List.getD,List.getElem?_eq_getElem hb]

theorem decoded_count (bs : Bytes) (st : State) (vid t : Nat) (pub msg : List Fp)
    (hd:State.decode bs=some st) (hfit:bs.length≤2^22) :
    tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (trace st vid true) t pub B_VBYTES true msg=
      cnt (emitAt vid 0 (bs.map UInt8.toNat)) msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [decoded bs st vid t pub hd hfit]
  rfl

end ZkFormal.NearV3.Candidates.ProcPriorRawByteTraffic
