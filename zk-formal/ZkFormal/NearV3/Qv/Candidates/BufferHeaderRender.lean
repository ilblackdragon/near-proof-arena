import ZkFormal.NearV3.Qv.Candidates.BufferLocal

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

/-- All local constraints on the actual buffered generator's four header rows.
Entry rows and padding are separate obligations. -/
theorem bufferGeneratedTrace_header_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) (hn : es.length<16777216)
    (hb : 4+24*es.length ≤ 2^log) {r : Nat} (hr : r<4) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferGeneratedTrace (F:=F) log vid tau users es) 0 r [] = 0 := by
  rw [bufferGeneratedTrace_eq log vid tau users es hs]
  exact bufferTrace_header_local log vid tau users es hn hb hr

end ZkFormal.NearV3.Qv.Candidates.ValueGen
