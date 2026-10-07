import ZkFormal.NearV3.Qv.Candidates.BufferRows

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

/-- Direct buffered parser trace, including zero padding. -/
def bufferTrace (log vid tau users : Nat) (es : List ByteBuffer) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      ((bufferRowAt vid tau users es r).getD c 0) }

/-- The trace emitted by the executable buffered row generator. -/
def bufferGeneratedTrace (log vid tau users : Nat) (es : List ByteBuffer) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      (((bufferRows vid tau users es).getD r []).getD c 0) }

theorem bufferGeneratedTrace_eq (log vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) :
    bufferGeneratedTrace (F:=F) log vid tau users es = bufferTrace log vid tau users es := by
  unfold bufferGeneratedTrace bufferTrace
  congr 1
  funext t r c
  rw [bufferRows_get vid tau users es hs r]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
