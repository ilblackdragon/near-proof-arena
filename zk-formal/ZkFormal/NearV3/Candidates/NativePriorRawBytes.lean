import ZkFormal.NearV3.Candidates.ProcPriorRawByteTraffic
import ZkFormal.NearV3.Candidates.NativeQueueIds
import ZkFormal.NearV3.Assembly.ReadUnfoldBound

namespace ZkFormal.NearV3.Candidates.NativePriorRawBytes
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Assembly

/-- A successful present read chooses the actual value occurrence. The parser
supplies its original bytes at that occurrence's forest-offset VID. -/
theorem present {tree : PTrie} {bs : Bytes} {old : Bandwidth.State}
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok (some bs))
    (hd:Bandwidth.State.decode bs=some old) (hfit:bs.length≤2^22)
    (offset t : Nat) (pub : List Fp) :
    ∃i,valueIndex tree keyBwState=some i ∧ (NearSpecV3.valsOf tree)[i]?=some bs ∧
      ∀msg,tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
        (ProcPriorRawGen.trace old (offset+i) true) t pub B_VBYTES true msg=
        cnt (emitAt (offset+i) 0 (bs.map UInt8.toNat)) msg := by
  have hf:tree.find keyBwState=some (some bs):=by
    cases he:tree.find keyBwState <;> simp [readKey,he] at hr
    simpa [hr] using he
  obtain ⟨i,hi,hb⟩:=valueIndex_complete tree keyBwState bs hf
  exact ⟨i,hi,hb,fun msg=>ProcPriorRawByteTraffic.decoded_count bs old (offset+i) t pub msg hd hfit⟩

/-- Missing prior state has no occurrence and sends no value bytes, even
though its parser represents the scheduler's initial state. -/
theorem absent {tree : PTrie}
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok none)
    (offset t : Nat) (pub msg : List Fp) :
    valueIndex tree keyBwState=none ∧
      tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
        (ProcPriorRawGen.trace Bandwidth.State.initial offset false) t pub B_VBYTES true msg=0 := by
  have hf:tree.find keyBwState=some none:=by
    cases he:tree.find keyBwState <;> simp [readKey,he] at hr
    simpa [hr] using he
  have hp:=NativeQueueIds.find_presence tree keyBwState none hf
  have hi:valueIndex tree keyBwState=none:=by
    cases he:valueIndex tree keyBwState <;> simp_all
  refine ⟨hi,?_⟩
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=0
  rw [ProcPriorRawByteTraffic.physical _ offset t false pub (by decide)]
  rfl

/-- The accepted forest byte budget discharges parser capacity for the actual
read; no record-count or parser-size premise is added to acceptance. -/
theorem accepted_present {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hc:checkD0a B0 cb wb=.ok ())
    (hm:m.NativeValid k w)
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {tree : PTrie} (ht:tree∈m.pre::steps.map ImplicitStepV3.pre)
    {bs : Bytes} {old : Bandwidth.State}
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok (some bs))
    (hd:Bandwidth.State.decode bs=some old)
    (offset t : Nat) (pub : List Fp) :
    ∃i,valueIndex tree keyBwState=some i ∧ (NearSpecV3.valsOf tree)[i]?=some bs ∧
      ∀msg,tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
        (ProcPriorRawGen.trace old (offset+i) true) t pub B_VBYTES true msg=
        cnt (emitAt (offset+i) 0 (bs.map UInt8.toNat)) msg := by
  have hf:tree.find keyBwState=some (some bs):=by
    cases he:tree.find keyBwState <;> simp [readKey,he] at hr
    simpa [hr] using he
  have hb:=checkD0a_read_bound hk hw hc hm hv ht hf
  apply present hr hd (by unfold B0 at hb; omega) offset t pub

/-- Forest offsets preserve the exact native occurrence, even when equal
byte strings occur elsewhere in this or another tree. -/
theorem forest_slot (before after : List PTrie) {tree : PTrie} {i : Nat} {bs : Bytes}
    (hi:(NearSpecV3.valsOf tree)[i]?=some bs) :
    (forestBytes (before++tree::after))[(forestBytes before).length+i]?=some bs := by
  have hb:i<(NearSpecV3.valsOf tree).length := (List.getElem?_eq_some_iff.mp hi).1
  have he:forestBytes (before++tree::after)=
      forestBytes before++(NearSpecV3.valsOf tree++forestBytes after):=by
    simp only [forestBytes,List.flatMap_append,List.flatMap_cons]
    rw [native_valsOf_eq]
  rw [he,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hb]
  exact hi

end ZkFormal.NearV3.Candidates.NativePriorRawBytes
