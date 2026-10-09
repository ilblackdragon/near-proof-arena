import ZkFormal.NearV3.Candidates.UniqueSourcePartitions
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22HonestCarry
namespace ZkFormal.NearV3.Candidates.UniqueSourceCarry
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates Rcpt.Candidates.SourceLog22 Rcpt.Candidates.DedupPartitionTable
/-- Honest shifted placement copies every carried column across a boundary. -/
theorem placed_carry_equal {tr : Trace Fp} {left right off : Nat}
    (bs : List SrcpB) (rep : Nat → Bool)
    (hl : ∀ r,r<tr.height left → ∀ x,tr.cell left r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x))
    (hr : ∀ r,r<tr.height right → ∀ x,tr.cell right r x=
      Fp.ofNat (UniqueSourceRender.cell bs rep (off+(tr.height left-1)+r) x)) :
    carryRow tr left (tr.height left-1)=carryRow tr right 0 := by
  have hp : 0<tr.height left := Nat.two_pow_pos _
  have hq : 0<tr.height right := Nat.two_pow_pos _
  apply List.map_congr_left
  intro x _
  rw [hl _ (by omega),hr _ hq,Nat.add_zero]

/-- Explicit honest placement closes every carry bus for the actual SIZE-wrapped
four-table family; no carry-balance premise is assumed. -/
theorem honest_four_carries {tr : Trace Fp} {t0 t1 t2 t3 H : Nat} {pub : List Fp}
    (bs : List SrcpB) (rep : Nat → Bool)
    (hh : ∀ t∈[t0,t1,t2,t3],tr.height t=H)
    (h0 : ∀ r,r<H → ∀ x,tr.cell t0 r x=Fp.ofNat (UniqueSourceRender.cell bs rep r x))
    (h1 : ∀ r,r<H → ∀ x,tr.cell t1 r x=Fp.ofNat (UniqueSourceRender.cell bs rep ((H-1)+r) x))
    (h2 : ∀ r,r<H → ∀ x,tr.cell t2 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (2*(H-1)+r) x))
    (h3 : ∀ r,r<H → ∀ x,tr.cell t3 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (3*(H-1)+r) x))
    (b : Nat) (hb : 64≤b) :
    physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.first) tr t0 pub b true ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 64 65)) tr t1 pub b true ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 65 66)) tr t2 pub b true ++
      physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.last) tr t3 pub b true=
    physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.first) tr t0 pub b false ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 64 65)) tr t1 pub b false ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 65 66)) tr t2 pub b false ++
      physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.last) tr t3 pub b false := by
  have H0 := hh t0 (by simp)
  have H1 := hh t1 (by simp)
  have H2 := hh t2 (by simp)
  have H3 := hh t3 (by simp)
  have h01 : carryRow tr t0 (tr.height t0-1)=carryRow tr t1 0 := by
    apply placed_carry_equal bs rep (off:=0)
    · simpa only [H0,Nat.zero_add] using h0
    · simpa only [H0,H1,Nat.zero_add] using h1
  have h12 : carryRow tr t1 (tr.height t1-1)=carryRow tr t2 0 := by
    apply placed_carry_equal bs rep (off:=H-1)
    · simpa only [H1] using h1
    · simpa only [H1,H2,show (H-1)+(H-1)=2*(H-1) by omega] using h2
  have h23 : carryRow tr t2 (tr.height t2-1)=carryRow tr t3 0 := by
    apply placed_carry_equal bs rep (off:=2*(H-1))
    · simpa only [H2] using h2
    · simpa only [H2,H3,show 2*(H-1)+(H-1)=3*(H-1) by omega] using h3
  change physicalMessages (SizeCount.sourceTable firstTable) tr t0 pub b true ++
    physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr t1 pub b true ++
    physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr t2 pub b true ++
    physicalMessages (SizeCount.sourceTable lastTable) tr t3 pub b true =
    physicalMessages (SizeCount.sourceTable firstTable) tr t0 pub b false ++
    physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr t1 pub b false ++
    physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr t2 pub b false ++
    physicalMessages (SizeCount.sourceTable lastTable) tr t3 pub b false
  rw [counted_four_messages,counted_four_messages,four_carry_messages h01 h12 h23 b hb]

end ZkFormal.NearV3.Candidates.UniqueSourceCarry
