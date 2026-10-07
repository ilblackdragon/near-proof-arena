import ZkFormal.NearV3.Qv.Candidates.BufferHeaderRender
import ZkFormal.NearV3.Qv.Candidates.BufferEntryLocal
import ZkFormal.NearV3.Qv.Candidates.BufferEntryEnd
import ZkFormal.NearV3.Qv.Candidates.BufferPadding

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

/-- All buffered-parser local polynomials, for every row including padding. -/
theorem bufferTrace_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hn : es.length<16777216) (hb : 4+24*es.length ≤ 2^log)
    {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 r [] = 0 := by
  by_cases h4 : r<4
  · exact bufferTrace_header_local log vid tau users es hn hb h4
  · by_cases hl : r<4+24*es.length
    · have hi : (r-4)/24<es.length := by omega
      have hj : (r-4)%24<24 := by omega
      have hd : 4+24*((r-4)/24)+(r-4)%24=r := by omega
      by_cases hj23 : (r-4)%24<23
      · simpa only [hd] using
          bufferTrace_entry_interior_local (F:=F) log vid tau users es hb
            ((r-4)/24) ((r-4)%24) hi hj23
      · have he : 4+24*((r-4)/24)+23=r := by omega
        simpa only [he] using
          bufferTrace_entry_end_local (F:=F) log vid tau users es hb ((r-4)/24) hi
    · exact bufferTrace_padding_local log vid tau users es hr (by omega)

/-- Honest local validity of the executable buffered row generator.
The count bound is an explicit completeness premise, not a domain restriction;
assembly must derive it from the authenticated value-byte budget. -/
theorem bufferGeneratedTrace_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) (hn : es.length<16777216)
    (hb : 4+24*es.length ≤ 2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferGeneratedTrace (F:=F) log vid tau users es) 0 r [] = 0 := by
  rw [bufferGeneratedTrace_eq log vid tau users es hs]
  exact bufferTrace_local log vid tau users es hn hb hr

end ZkFormal.NearV3.Qv.Candidates.ValueGen
