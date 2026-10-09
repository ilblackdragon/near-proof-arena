import ZkFormal.NearV3.Candidates.ProcCodecRecordFullKind
import ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
import ZkFormal.NearV3.Candidates.ProcCodecSuffixKind
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedFullKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecSideFullKind

/-- Full retained cKind, across the actual header, every record, and both
suffixes. The executable generator supplies all row data and adjacency. -/
theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hparam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn1:0<R.n) (hn:R.n≤64) (ht:R.tau<P) (r : Nat) (hr:r<out.rows.size) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  by_cases hh:r<5
  · exact ProcCodecHeaderKind.active I R present vidV gb fwd out h hparam hn1 hn ht r hh
  · by_cases hrec:r<5+24*(R.n*R.n)
    · exact ProcCodecRecordFullKind.region I R present vidV gb fwd out h hn ht r (by omega) hrec
    · exact ProcCodecSuffixKind.active I R present vidV gb fwd out h ht r hr (by omega)

/-- All physical retained kind constraints, including padding and the cyclic
wrap row, from successful generation and native parameter/count bounds. -/
theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hparam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn1:0<R.n) (hn:R.n≤64) (ht:R.tau<P) (t r : Nat) (hr:r<2^22) (pub : List Fp) :
    ∀e∈kindGroup,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  obtain ⟨hne,hcap⟩ := ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn
  intro e he
  by_cases ha:r<out.rows.size
  · have hp:e.pubBound=0 := (by decide +kernel : ∀e∈kindGroup,e.pubBound=0) e he
    rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r ha pub e hp]
    exact active I R present vidV gb fwd out h hparam hn1 hn ht r ha e he
  · apply (ProcCodecPhysicalPadding.physical_local out.rows hne t r (by omega) hr pub).1 e
    unfold ProcPriorCodecActual.table ProcPriorCodecActual.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he))
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedFullKind
