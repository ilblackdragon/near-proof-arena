import ZkFormal.NearV3.Candidates.ProcPriorRawPhysical
import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorRawLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec.Bandwidth
open ProcPriorRawGen

theorem native_local (st : State) (vid : Nat) (present : Bool)
    (hc:ProcPriorRawSlots.length st.links.length<2^22)
    (hp:present=false→st=State.initial) (tt pb lb bb sb rb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRawFrame.table pb lb bb sb rb) (trace st vid present) tt pub := by
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro j hj e he
    exact ProcPriorRawPhysical.constraints st vid tt j present hc hp hj pub e he
  · intro j hj i hi e he
    exact ProcPriorRawChecks.trace_bits st vid present tt j pub pb lb bb sb rb i hi e he

/-- The successful native decoder and ordinary source-byte bound discharge
all framing capacity premises, while retaining the original record order. -/
theorem decoded_local (bytes : NearSpec.Bytes) (st : State)
    (hd:State.decode bytes=some st) (hb:bytes.length≤2000000)
    (vid tt pb lb bb sb rb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRawFrame.table pb lb bb sb rb) (trace st vid true) tt pub := by
  have hl:=ProcPriorDecode.decode_length bytes st hd
  apply native_local st vid true
  · unfold ProcPriorRawSlots.length
    omega
  · simp

theorem absent_local (vid tt pb lb bb sb rb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRawFrame.table pb lb bb sb rb)
      (trace State.initial vid false) tt pub := by
  apply native_local State.initial vid false
  · decide +kernel
  · intro _; rfl

end ZkFormal.NearV3.Candidates.ProcPriorRawLocal
