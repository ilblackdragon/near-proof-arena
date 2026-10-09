import ZkFormal.NearV3.Candidates.ProcCodecBoundaryLocal
import ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest

theorem pair (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (I' : Input) (R' : Run) (present' : Bool) (vid' : Nat)
    (gb' : Array Nat) (fwd' : List (Nat×Nat)) (out' : CodecOut)
    (h':ProcPriorCodecGen.codecRows I' R' present' vid' gb' fwd'=.ok out')
    (ht:R.tau<P) :
    ∀e∈ProcPriorCodecActual.constraints,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat out.rows[out.rows.size-1]![c]!)
      (fun c=>Fp.ofNat out'.rows[0]![c]!) 0 0 1)=0 := by
  have hl:=generated_length I R present vid gb fwd out h
  rw [show out.rows.size-1=5+24*(R.n*R.n)+32+31 by omega,
    ProcCodecSuffixCells.ash_cell I R present vid gb fwd out h 31 (by decide),
    ProcCodecHeaderKind.header_cell I' R' present' vid' gb' fwd' out' h' 0 (by decide)]
  exact ProcCodecBoundaryLocal.ash_to_header I R present vid (5+24*(R.n*R.n)) I' R' present' vid' ht 1

/-- Physical singleton Local supplies exact active-row equations; this helper
is used before changing block placement and handling the real boundary pair. -/
theorem active_of_local (rows : Array (Array Nat)) (hcap:rows.size<2^22)
    (hlocal:ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace rows codecPad) 0 []) :
    ∀r,r<rows.size→∀e∈ProcPriorCodecActual.constraints,
      e.evalWith (ProcCodecPhysicalRows.rowEnvAt rows r)=0 := by
  intro r hr e he
  have hp:e.pubBound=0 := (by decide +kernel : ∀e∈ProcPriorCodecActual.constraints,e.pubBound=0) e he
  rw [←ProcCodecPhysicalRows.generated_eval rows hcap 0 r hr [] e hp]
  exact hlocal.constr r (by change r<2^22;omega) e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedBoundary
