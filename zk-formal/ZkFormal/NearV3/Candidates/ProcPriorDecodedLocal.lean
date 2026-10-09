import ZkFormal.NearV3.Candidates.ProcPriorTraceLocal
import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorDecodedLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpec.Bandwidth
open ProcPriorRows ProcPriorTrace ProcPriorTraceLocal

theorem row_capacity (ids : List Nat) (bytes : Bytes) (st : State)
    (hd:State.decode bytes=some st) (hn:ids.length≤64) (hb:bytes.length≤2000000) :
    (rows ids st.links).length<2^22 := by
  have hc:=ProcPriorDecode.decode_length bytes st hd
  have hr:=rows_length ids st.links
  have hh:ids.length*ids.length≤64*64:=Nat.mul_le_mul hn hn
  omega

/-- Decoded original records give the complete executable degree-reduced
memory trace; no AIR equality or proposed query-result premise is supplied. -/
theorem decoded_local (ids : List Nat) (bytes : Bytes) (st : State)
    (hd:State.decode bytes=some st) (hn:ids.length≤64) (hb:bytes.length≤2000000)
    (t tt wb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorMemoryGated.table wb rb cb)
      (ProcPriorMemoryGated.liftTrace (trace (rows ids st.links) t) tt pub) tt pub := by
  exact native_gated_local ids st.links hn (row_capacity ids bytes st hd hn hb) t tt wb rb cb pub

end ZkFormal.NearV3.Candidates.ProcPriorDecodedLocal
