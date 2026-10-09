import ZkFormal.NearV3.Candidates.ProcCodecPriorReadRecord
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideMultiplicity
namespace ZkFormal.NearV3.Candidates.ProcCodecPriorReadPhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPhysicalPadding ProcPriorCodecSideMultiplicity

theorem side_gate (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) (hs : r<5 ∨ 5+24*(R.n*R.n)≤r) :
    out.rows[r]![fA]! =0 := by
  have hl:=generated_length I R present vidV gb fwd out h
  rcases hs with hh|hh
  · rw [ProcCodecHeaderKind.header_cell I R present vidV gb fwd out h r hh]
    exact (header_flags I R present vidV _ _ r).1 fA (by simp)
  · by_cases hz:r<5+24*(R.n*R.n)+32
    · have he:r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))) := by omega
      rw [he,ProcCodecSuffixCells.hash_cell I R present vidV gb fwd out h _ (by omega)]
      exact (hash_flags I R present vidV _ _ _ _).1 fA (by simp)
    · have he:r=5+24*(R.n*R.n)+32+(r-(5+24*(R.n*R.n)+32)) := by omega
      rw [he,ProcCodecSuffixCells.ash_cell I R present vidV gb fwd out h _ (by omega)]
      exact (ash_flags I R present vidV _ _).1 fA (by simp)

/-- Exact whole physical row inventory, including header, suffix and padding
silence. Arithmetic coordinates refer to the actual generated record array. -/
theorem row (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r t : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t r pub 68 false =
      if 5≤r ∧ r<5+24*(R.n*R.n) then
        if (r-5)%24/8=2 ∧ (r-5)%24%8=2 then
          [ProcCodecPriorReadRecord.message R.tau ((r-5)/24)
            (ProcCodecPriorReadCells.prior I present ((r-5)/24))] else []
      else [] := by
  have hl:=generated_length I R present vidV gb fwd out h
  by_cases hc:5≤r ∧ r<5+24*(R.n*R.n)
  · rw [ite_eq_left hc]
    have he:r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
    conv => lhs; rw [he]
    exact ProcCodecPriorReadRecord.record I R present vidV gb fwd out h _ _ _ (by omega) (by omega) (by omega) t pub
  · rw [ite_eq_right hc,ProcCodecPriorReadTraffic.codec_row]
    change List.replicate (if cells out.rows r fA*cells out.rows r e2=1 then 1 else 0) _=[]
    by_cases hr:r<out.rows.size
    · rw [ProcCodecPhysicalRows.active_cells out.rows r hr]
      have hg:=side_gate I R present vidV gb fwd out h r hr (by omega)
      dsimp only
      simp only [hg,show Fp.ofNat 0=0 from rfl,Lean.Grind.Semiring.zero_mul,
        show (0:Fp)≠1 by decide +kernel,ite_false,List.replicate_zero]
    · rw [padding_cells out.rows r (by omega)]
      simp only [Lean.Grind.Semiring.zero_mul,show (0:Fp)≠1 by decide +kernel,ite_false,List.replicate_zero]
end ZkFormal.NearV3.Candidates.ProcCodecPriorReadPhysical
