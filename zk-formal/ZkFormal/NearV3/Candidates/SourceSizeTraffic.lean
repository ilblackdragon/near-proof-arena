import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22HonestTraffic
import ZkFormal.NearV3.Candidates.SizeCountLocal
namespace ZkFormal.NearV3.Candidates.SourceSizeTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Rcpt.Candidates Rcpt.Candidates.SourceLog22 Rcpt.Candidates.DedupPartitionTable Rcpt.Candidates.DedupRender

def fourCount (tr : Trace Fp) (t0 t1 t2 t3 : Nat) (pub : List Fp) (sd : Bool) (m : List Fp) : Nat :=
  tableBusCount (SizeCount.sourceTable firstTable).interactions tr t0 pub B_SIZE sd m+
  tableBusCount (SizeCount.sourceTable (middleTable 64 65)).interactions tr t1 pub B_SIZE sd m+
  tableBusCount (SizeCount.sourceTable (middleTable 65 66)).interactions tr t2 pub B_SIZE sd m+
  tableBusCount (SizeCount.sourceTable lastTable).interactions tr t3 pub B_SIZE sd m

theorem four_size_count {tr : Trace Fp} {t0 t1 t2 t3 H : Nat} {pub : List Fp}
    (bs : List SrcpB) (rep : Nat → Bool) (hn : bs≠[])
    (hh : ∀ t∈[t0,t1,t2,t3],tr.height t=H)
    (hR : R bs≤3*(H-1)+H)
    (hshape : ∀ B∈bs,B.root.length=32 ∧ B.leaf.length=32 ∧
      ∀ it∈B.path,it.sib.length=32 ∧ it.acc.length=32)
    (h0 : ∀ r,r<H → ∀ x,tr.cell t0 r x=Fp.ofNat (cell bs rep r x))
    (h1 : ∀ r,r<H → ∀ x,tr.cell t1 r x=Fp.ofNat (cell bs rep ((H-1)+r) x))
    (h2 : ∀ r,r<H → ∀ x,tr.cell t2 r x=Fp.ofNat (cell bs rep (2*(H-1)+r) x))
    (h3 : ∀ r,r<H → ∀ x,tr.cell t3 r x=Fp.ofNat (cell bs rep (3*(H-1)+r) x))
    (sd : Bool) (m : List Fp) :
    fourCount tr t0 t1 t2 t3 pub sd m=
      if sd=true ∧ [Fp.ofNat 2,Fp.ofNat (size bs),0]=m then 1 else 0 := by
  have h := honest_four_counted_messages (pub:=pub) bs rep hn hh hR hshape h0 h1 h2 h3 B_SIZE sd
    (by decide) (by decide) (by decide)
  have hc := congrArg (fun xs : List (List Fp)=>xs.count m) h
  simp only [List.count_append,physicalMessages,←tableBusCount_eq] at hc
  change fourCount tr t0 t1 t2 t3 pub sd m=_ at hc
  rw [hc]
  cases sd <;> simp [DedupRender.traffic,Near.Msg.toFp,List.count_cons]
end ZkFormal.NearV3.Candidates.SourceSizeTraffic
