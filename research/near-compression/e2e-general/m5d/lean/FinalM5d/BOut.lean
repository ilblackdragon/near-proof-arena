import FinalM5d.Decode
import FinalM5d.HeaderLink
import NearSpecV3.E2E.ViewSer
import NearSpec.ClaimCodec
import NearSpecV3.Logged.TrieHash

/-!
# FinalM5d.BOut — the `done` boundary's component commitments (G-5: lane E's view encodings)

Lane E's view (`NearSpecV3.E2E.ViewE.viewE`) commits `done H o` (phase 4) through
`ctxDE (.header H) = bdigest (3 ‖ Ser.enc H)` (the `ctxRoot` field) and
`outDE (.done o) = (bdigest (Ser.enc o), [], bdigest [], bdigest [2])` (the four accumulator
fields), with `ViewSer`'s serialisers. G-5 (lanes E ∧ G, coordinator decision I2b): `Ser ChunkInner`
and `Ser Outputs` are the fixed-width, prefix-free forms of `ViewSer` (`natW`, `hashW`), and the
FINAL template recomputes exactly these bytes (`Final.Fin.hdrBytes` = `encHdr H`, 389 B on class F1;
`Final.Fin.outBytes` = `encOut o`, 304 B) and exposes the two digests as public values 30..44,
44..58; lane D assembles `h(B_out)` from them, the two clear counters (58..82) and the view's
constants. G-2's own encodings (`0x04 ‖ chunk_inner`, `0x05 ‖ encOutputsF1 o`) are gone.
-/

namespace FinalM5d.BOut

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Enc FinalM5d FinalM5d.Decode

/-- The preimage of `ctxDE (.header H)`: `3 ‖ Ser.enc H`. -/
def encHdr (H : ChunkInner) : Bytes := 3 :: Ser.enc H

/-- **`ctxD (.header H)`** (lane E's view, `ViewSer` instances). -/
def ctxHeaderD (H : ChunkInner) : Bytes := Bnd.bdigest (encHdr H)

theorem ctxHeaderD_view (lB : Bytes → Nat) (H : ChunkInner) :
    ViewE.ctxDE lB (.header H) = ctxHeaderD H := rfl

/-- The preimage of `outDE (.done o)`'s first component. -/
def encOut (o : Outputs) : Bytes := Ser.enc o

/-- **`outD (.done o)`** (lane E's view). -/
def outDoneD (o : Outputs) : Bytes × List Bytes × Bytes × Bytes := ViewE.outDE (.done o)

theorem outDoneD_fst (o : Outputs) : (outDoneD o).1 = Bnd.bdigest (encOut o) := rfl

end FinalM5d.BOut
