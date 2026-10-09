import ZkFormal.NearV3.Candidates.ProcCodecPriorReadInventory
import ZkFormal.NearV3.Candidates.ProcPriorCodecQueries
import ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
import ZkFormal.NearV3.Candidates.ProcActualRunProjection
namespace ZkFormal.NearV3.Candidates.ProcCodecPriorReadNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest

/-- An absent native prior has the empty dictionary, so its actual lookup is
zero rather than a separately supplied grid. -/
theorem prior_value (b : NativeBlock) (hb:b.Valid) (k : Nat) :
    ProcCodecPriorReadCells.prior (ProcPreparedSequence.input b.pub b.old) b.prior.isSome k=
      (ProcActualInput.allowances b.pub.ids b.old)[k]! := by
  unfold ProcCodecPriorReadCells.prior
  cases hp:b.prior with
  | some raw => rfl
  | none =>
    have hd:=hb.2.2.2.1
    rw [hp] at hd
    have he:b.old=NearSpec.Bandwidth.State.initial:= (Option.some.inj hd).symm
    simp [he,ProcActualInput.allowances,NearSpec.Bandwidth.State.initial]
    by_cases hk:k<b.pub.ids.length*b.pub.ids.length
    · simp [getElem!_pos (Array.replicate (b.pub.ids.length*b.pub.ids.length) (0:Nat)) k (by simpa using hk)]
    · rw [getElem!_neg (Array.replicate (b.pub.ids.length*b.pub.ids.length) (0:Nat)) k (by simpa using hk)]; rfl

theorem native (b : NativeBlock) (hb:b.Valid) (hdim:b.run.n=b.pub.ids.length)
    (hn:0<b.run.n) (hn64:b.run.n≤64) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace b.output.rows codecPad) t r pub 68 false)=
      (ProcPriorCodecQueries.queries b.run.tau b.pub.ids b.old).map (List.map Fp.ofNat) := by
  rw [ProcCodecPriorReadInventory.physical _ _ _ _ _ _ _ hb.2.2.2.2 hn hn64]
  unfold ProcPriorCodecQueries.queries
  rw [List.map_map,hdim]
  apply List.map_congr_left
  intro k _
  rw [prior_value b hb k]
  simp [ProcCodecPriorReadRecord.message,ProcPriorSummary.low,ProcPriorSummary.big]

/-- Same block, same decoded dictionary: actual physical queries are the
last-original-record memory queries, preserving repeated and unknown IDs. -/
theorem native_events (b : NativeBlock) (hb:b.Valid) (hdim:b.run.n=b.pub.ids.length)
    (hn:0<b.run.n) (hn64:b.run.n≤64) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace b.output.rows codecPad) t r pub 68 false)=
      ((ProcPriorEvents.queryEvents b.pub.ids b.old.links).map (ProcPriorCodecQueries.message b.run.tau)).map
        (List.map Fp.ofNat) := by
  rw [native b hb hdim hn hn64 t pub,ProcPriorCodecQueries.native_queries]

theorem block_rows (b : NativeBlock) (hb:b.Valid) (hdim:b.run.n=b.pub.ids.length)
    (hn:0<b.run.n) (hn64:b.run.n≤64) :
    b.output.rows.toList.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row 68 false)=
      (ProcPriorCodecQueries.queries b.run.tau b.pub.ids b.old).map (List.map Fp.ofNat) := by
  have hsize:=native_block_length b hb hn64
  rw [←ProcCodecConcatTraffic.physical b.output.rows (by omega) 0 68 [] false]
  exact native b hb hdim hn hn64 0 []

theorem blocks (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.run.n=b.pub.ids.length ∧ 0<b.run.n ∧ b.run.n≤64)
    (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t r pub 68 false)=
      bs.flatMap (fun b=>(ProcPriorCodecQueries.queries b.run.tau b.pub.ids b.old).map (List.map Fp.ofNat)) := by
  have hsize:=native_block_rows_bound bs (fun b hm=>⟨(hb b hm).1,(hb b hm).2.2.2⟩)
  rw [ProcCodecConcatTraffic.blocks bs (by omega)]
  apply ProcCodecPublicIdEnumeration.flat_congr
  intro b hm
  obtain ⟨hv,hd,hn,h64⟩:=hb b hm
  exact block_rows b hv hd hn h64

/-- Accepted prepared inputs discharge dimensions from their actual process
execution. All queries retain each block's same decoded old state. -/
theorem prepared_blocks {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run)
    (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t r pub 68 false)=
      bs.flatMap (fun b=>((ProcPriorEvents.queryEvents b.pub.ids b.old.links).map
        (ProcPriorCodecQueries.message b.run.tau)).map (List.map Fp.ofNat)) := by
  have hh:∀b∈bs,b.Valid ∧ b.run.n=b.pub.ids.length ∧ 0<b.run.n ∧ b.run.n≤64 := by
    intro b hm
    obtain ⟨hv,hsp,tauV,hr⟩:=hb b hm
    have hf:=ProcActualRunProjection.run_fields _ _ _ hr
    have hn:b.run.n=b.pub.ids.length:=hf.2.1
    have hs:=prepD0_sched hp b.pub hsp
    exact ⟨hv,hn,by have :=hs.n1;omega,by have :=hs.n64;omega⟩
  rw [blocks bs hlen hh t pub]
  apply ProcCodecPublicIdEnumeration.flat_congr
  intro b _
  rw [ProcPriorCodecQueries.native_queries]
end ZkFormal.NearV3.Candidates.ProcCodecPriorReadNative
