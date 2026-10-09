import ZkFormal.NearV3.Candidates.UniqueSourceTraffic
import ZkFormal.NearV3.Candidates.UniqueSourcePartitions
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Endpoints
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Carry
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSourceSender

namespace ZkFormal.NearV3.Candidates.UniqueSourcePhysicalTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open Rcpt.Candidates Rcpt.Candidates.SourceLog22 Rcpt.Candidates.DedupPartitionTable Rcpt.Candidates.DedupRender

def physicalMessages (T : Air.Table) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (b : Nat) (sd : Bool) : List (List Fp) :=
  (List.range (tr.height tt)).flatMap fun r => rowTraffic T.interactions tr tt r pub b sd

private theorem drop_last {α : Type} (f : Nat → List α) (H : Nat) (hp : 0<H) :
    (List.range H).flatMap (fun r => if r+1=H then [] else f r)=
      (List.range (H-1)).flatMap f := by
  have he : List.range H=List.range (H-1)++[H-1] := by
    simpa only [Nat.succ_eq_add_one,show H-1+1=H by omega] using (@List.range_succ (H-1))
  rw [he,List.flatMap_append]
  have hh : (List.range (H-1)).flatMap (fun r => if r+1=H then [] else f r)=
      (List.range (H-1)).flatMap f := by
    apply flatMap_congr'
    intro r hr
    have := List.mem_range.mp hr
    simp [show r+1≠H by omega]
  rw [hh]
  simp [show H-1+1=H by omega]

/-- Any carried prefix emits exactly its H-1 owned logical rows. -/
theorem rendered_prefix {T : Air.Table} {tr : Trace Fp} {tt off b : Nat}
    {pub : List Fp} {bs : List SrcpB} {rep : Nat → Bool} {sd : Bool}
    (hnormal : ∀ r,rowTraffic T.interactions tr tt r pub b sd=
      if r+1=tr.height tt then [] else rowTraffic DedupTable.interactions tr tt r pub b sd)
    (hc : ∀ r,r<tr.height tt → ∀ x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x)) :
    physicalMessages T tr tt pub b sd=
      ((List.range (tr.height tt-1)).flatMap fun r => rowN (UniqueSourceRender.cell bs rep (off+r)) b sd).map Msg.toFp := by
  unfold physicalMessages
  calc
    _ = (List.range (tr.height tt)).flatMap (fun r => if r+1=tr.height tt then []
      else (rowN (UniqueSourceRender.cell bs rep (off+r)) b sd).map Msg.toFp) := by
        apply flatMap_congr'
        intro r hr
        rw [hnormal]
        split
        · rfl
        · exact row_traffic _ (hc r (List.mem_range.mp hr)) (UniqueSourceTraffic.bool_bound bs rep _) b sd
    _ = _ := by rw [drop_last _ (tr.height tt) (show 0<tr.height tt from Nat.two_pow_pos _),List.map_flatMap]

/-- The final partition owns all of its rows, including the incoming overlap. -/
theorem rendered_suffix {tr : Trace Fp} {tt off b : Nat} {pub : List Fp}
    {bs : List SrcpB} {rep : Nat → Bool} {sd : Bool} (hb : b≠66)
    (hc : ∀ r,r<tr.height tt → ∀ x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x)) :
    physicalMessages UniqueSourcePartitions.last tr tt pub b sd=
      ((List.range (tr.height tt)).flatMap fun r => rowN (UniqueSourceRender.cell bs rep (off+r)) b sd).map Msg.toFp := by
  rw [List.map_flatMap]
  apply flatMap_congr'
  intro r hr
  have hn : rowTraffic UniqueSourcePartitions.last.interactions tr tt r pub b sd=
      rowTraffic DedupTable.interactions tr tt r pub b sd := by
    simp [UniqueSourcePartitions.last,SourceLog22.lastTable,rightTable,rightInteractions,rowTraffic,recv,Ne.symm hb]
  rw [hn]
  exact row_traffic _ (hc r (List.mem_range.mp hr)) (UniqueSourceTraffic.bool_bound bs rep _) b sd

private theorem join_ranges {α : Type} (f : Nat → List α) (a n m : Nat) :
    (List.range n).flatMap (fun r => f (a+r)) ++
      (List.range m).flatMap (fun r => f (a+n+r))=
      (List.range (n+m)).flatMap (fun r => f (a+r)) := by
  rw [List.range_add,List.flatMap_append,List.flatMap_map]
  simp only [Nat.add_assoc]

/-- Exact external traffic across all four physical source tables: overlap rows
are emitted only in their successor, preserving ordered message multiplicity. -/
theorem honest_four_messages {tr : Trace Fp} {t0 t1 t2 t3 H : Nat} {pub : List Fp}
    (bs : List SrcpB) (rep : Nat → Bool) (hn : bs≠[])
    (hh : ∀ t∈[t0,t1,t2,t3],tr.height t=H)
    (hR : R bs≤3*(H-1)+H)
    (hshape : ∀ B∈bs,B.root.length=32 ∧ B.leaf.length=32 ∧
      ∀ it∈B.path,it.sib.length=32 ∧ it.acc.length=32)
    (h0 : ∀ r,r<H → ∀ x,tr.cell t0 r x=Fp.ofNat (UniqueSourceRender.cell bs rep r x))
    (h1 : ∀ r,r<H → ∀ x,tr.cell t1 r x=Fp.ofNat (UniqueSourceRender.cell bs rep ((H-1)+r) x))
    (h2 : ∀ r,r<H → ∀ x,tr.cell t2 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (2*(H-1)+r) x))
    (h3 : ∀ r,r<H → ∀ x,tr.cell t3 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (3*(H-1)+r) x))
    (b : Nat) (sd : Bool) (hb0 : b≠64) (hb1 : b≠65) (hb2 : b≠66) :
    physicalMessages UniqueSourcePartitions.first tr t0 pub b sd ++
      physicalMessages (UniqueSourcePartitions.middle 64 65) tr t1 pub b sd ++
      physicalMessages (UniqueSourcePartitions.middle 65 66) tr t2 pub b sd ++
      physicalMessages UniqueSourcePartitions.last tr t3 pub b sd=
      (if sd then (UniqueSourceTraffic.traffic bs rep).sends b else (UniqueSourceTraffic.traffic bs rep).recvs b).map Msg.toFp := by
  have H0 := hh t0 (by simp)
  have H1 := hh t1 (by simp)
  have H2 := hh t2 (by simp)
  have H3 := hh t3 (by simp)
  have p0 := rendered_prefix (T:=UniqueSourcePartitions.first) (off:=0)
    (fun r => left_normal_row tr t0 r pub b sd hb0)
    (by simpa only [Nat.zero_add,H0] using h0)
  have p1 := rendered_prefix (T:=UniqueSourcePartitions.middle 64 65) (off:=H-1)
    (fun r => middle_normal_row tr t1 r pub 64 65 b sd hb0 hb1)
    (by simpa only [H1] using h1)
  have p2 := rendered_prefix (T:=UniqueSourcePartitions.middle 65 66) (off:=2*(H-1))
    (fun r => middle_normal_row tr t2 r pub 65 66 b sd hb1 hb2)
    (by simpa only [H2] using h2)
  have p3 := rendered_suffix (tr:=tr) (tt:=t3) (pub:=pub) (bs:=bs) (rep:=rep) (sd:=sd) (off:=3*(H-1)) hb2 (by simpa only [H3] using h3)
  rw [p0,p1,p2,p3,H0,H1,H2,H3,←List.map_append,←List.map_append,←List.map_append]
  have hj : (List.range (H-1)).flatMap (fun r => rowN (UniqueSourceRender.cell bs rep (0+r)) b sd) ++
      (List.range (H-1)).flatMap (fun r => rowN (UniqueSourceRender.cell bs rep ((H-1)+r)) b sd) ++
      (List.range (H-1)).flatMap (fun r => rowN (UniqueSourceRender.cell bs rep (2*(H-1)+r)) b sd) ++
      (List.range H).flatMap (fun r => rowN (UniqueSourceRender.cell bs rep (3*(H-1)+r)) b sd)=
      (List.range (3*(H-1)+H)).flatMap (fun r => rowN (UniqueSourceRender.cell bs rep r) b sd) := by
    have j0 := join_ranges (fun r => rowN (UniqueSourceRender.cell bs rep r) b sd) 0 (H-1) (H-1)
    have j1 := join_ranges (fun r => rowN (UniqueSourceRender.cell bs rep r) b sd) 0 (2*(H-1)) (H-1)
    have j2 := join_ranges (fun r => rowN (UniqueSourceRender.cell bs rep r) b sd) 0 (3*(H-1)) H
    simp only [Nat.zero_add] at j0 j1 j2 ⊢
    rw [show 2*(H-1)=(H-1)+(H-1) by omega] at j1
    rw [←j0] at j1
    rw [show (H-1)+(H-1)+(H-1)=3*(H-1) by omega] at j1
    rw [show (H-1)+(H-1)=2*(H-1) by omega] at j1
    rw [j1,j2]
  rw [hj,UniqueSourceTraffic.messages hn rep _ hR hshape b sd]

/-- The candidate SIZE arity extension changes no other external message. -/
theorem counted_messages (T : Air.Table) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (b : Nat) (sd : Bool) :
    physicalMessages (SizeCount.sourceTable T) tr tt pub b sd=
      (physicalMessages T tr tt pub b sd).map
        (fun m => if b=B_SIZE then m++[0] else m) := by
  simp only [physicalMessages,SizeCount.sourceTable,SizeCount.rowTraffic_withCount,
    eval_k,List.map_flatMap]
  rfl

/-- Uniform wrapping commutes with concatenation across all four providers. -/
theorem counted_four_messages (tr : Trace Fp) (t0 t1 t2 t3 : Nat) (pub : List Fp)
    (b : Nat) (sd : Bool) :
    physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.first) tr t0 pub b sd ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 64 65)) tr t1 pub b sd ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 65 66)) tr t2 pub b sd ++
      physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.last) tr t3 pub b sd=
      (physicalMessages UniqueSourcePartitions.first tr t0 pub b sd ++
        physicalMessages (UniqueSourcePartitions.middle 64 65) tr t1 pub b sd ++
        physicalMessages (UniqueSourcePartitions.middle 65 66) tr t2 pub b sd ++
        physicalMessages UniqueSourcePartitions.last tr t3 pub b sd).map
        (fun m => if b=B_SIZE then m++[0] else m) := by
  simp only [counted_messages,List.map_append]

/-- Actual honest four-table traffic, including the arity-three SIZE charge. -/
theorem honest_four_counted_messages {tr : Trace Fp} {t0 t1 t2 t3 H : Nat} {pub : List Fp}
    (bs : List SrcpB) (rep : Nat → Bool) (hn : bs≠[])
    (hh : ∀ t∈[t0,t1,t2,t3],tr.height t=H)
    (hR : R bs≤3*(H-1)+H)
    (hshape : ∀ B∈bs,B.root.length=32 ∧ B.leaf.length=32 ∧
      ∀ it∈B.path,it.sib.length=32 ∧ it.acc.length=32)
    (h0 : ∀ r,r<H → ∀ x,tr.cell t0 r x=Fp.ofNat (UniqueSourceRender.cell bs rep r x))
    (h1 : ∀ r,r<H → ∀ x,tr.cell t1 r x=Fp.ofNat (UniqueSourceRender.cell bs rep ((H-1)+r) x))
    (h2 : ∀ r,r<H → ∀ x,tr.cell t2 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (2*(H-1)+r) x))
    (h3 : ∀ r,r<H → ∀ x,tr.cell t3 r x=Fp.ofNat (UniqueSourceRender.cell bs rep (3*(H-1)+r) x))
    (b : Nat) (sd : Bool) (hb0 : b≠64) (hb1 : b≠65) (hb2 : b≠66) :
    physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.first) tr t0 pub b sd ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 64 65)) tr t1 pub b sd ++
      physicalMessages (SizeCount.sourceTable (UniqueSourcePartitions.middle 65 66)) tr t2 pub b sd ++
      physicalMessages (SizeCount.sourceTable UniqueSourcePartitions.last) tr t3 pub b sd=
      ((if sd then (UniqueSourceTraffic.traffic bs rep).sends b else (UniqueSourceTraffic.traffic bs rep).recvs b).map Msg.toFp).map
        (fun m => if b=B_SIZE then m++[0] else m) := by
  rw [counted_four_messages,honest_four_messages bs rep hn hh hR hshape h0 h1 h2 h3 b sd hb0 hb1 hb2]

end ZkFormal.NearV3.Candidates.UniqueSourcePhysicalTraffic
