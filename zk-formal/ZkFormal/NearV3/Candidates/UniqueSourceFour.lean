import ZkFormal.NearV3.Candidates.UniqueSourcePhysicalLocal
namespace ZkFormal.NearV3.Candidates.UniqueSourceFour
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates UniqueSourcePhysicalLocal
/-- Four honest cap22 partitions, including the actual arity-three SIZE wrapper.
The same renderer cells are placed with one overlap row at each boundary. -/
theorem honest_four_local {bs : List SrcpB} {rep : Nat → Bool} (h : DedupRender.TableFacts bs rep)
    (hR : DedupRender.R bs≤16334272) {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (hl : ∀ t∈[t0,t1,t2,t3],tr.log t=22)
    (h0 : ∀ r,r<2^22 → ∀ x,tr.cell t0 r x=Fp.ofNat (UniqueSourceRender.cell bs rep r x))
    (h1 : ∀ r,r<2^22 → ∀ x,tr.cell t1 r x=Fp.ofNat (UniqueSourceRender.cell bs rep ((2^22-1)+r) x))
    (h2 : ∀ r,r<2^22 → ∀ x,tr.cell t2 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (2*(2^22-1)+r) x))
    (h3 : ∀ r,r<2^22 → ∀ x,tr.cell t3 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (3*(2^22-1)+r) x)) :
    TableLocal (SizeCount.sourceTable UniqueSourcePartitions.first) tr t0 pub ∧
    TableLocal (SizeCount.sourceTable (UniqueSourcePartitions.middle 64 65)) tr t1 pub ∧
    TableLocal (SizeCount.sourceTable (UniqueSourcePartitions.middle 65 66)) tr t2 pub ∧
    TableLocal (SizeCount.sourceTable UniqueSourcePartitions.last) tr t3 pub := by
  have l0 := hl t0 (by simp)
  have l1 := hl t1 (by simp)
  have l2 := hl t2 (by simp)
  have l3 := hl t3 (by simp)
  have H0 : tr.height t0=2^22 := congrArg (2^·) l0
  have H1 : tr.height t1=2^22 := congrArg (2^·) l1
  have H2 : tr.height t2=2^22 := congrArg (2^·) l2
  have H3 : tr.height t3=2^22 := congrArg (2^·) l3
  refine ⟨SourceLog22.source_local (first_local h (by omega) (by omega) ?_),
    SourceLog22.source_local (middle_local h (off:=2^22-1) (by decide) (by omega) (by omega) ?_),
    SourceLog22.source_local (middle_local h (off:=2*(2^22-1)) (by decide) (by omega) (by omega) ?_),
    SourceLog22.source_local (last_local h (off:=3*(2^22-1)) (by decide) (by omega) (by omega) ?_ ?_)⟩
  · simpa only [H0] using h0
  · simpa only [H1] using h1
  · simpa only [H2] using h2
  · rw [H3]; omega
  · simpa only [H3] using h3

end ZkFormal.NearV3.Candidates.UniqueSourceFour
