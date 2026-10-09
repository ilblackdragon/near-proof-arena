import ZkFormal.NearV3.Candidates.ProcessRepairSdlFinite
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlIds
namespace ZkFormal.NearV3.Candidates.ProcessRepairSdlIds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundSdlIds
open ProcPriorRoutedCodecProjection (codec)
/-- Public SDL records, not downstream bus70 lookup rows, authenticate current
layout ID bytes. Global balance/ownership plus finite physical height supply
the public origin, with no supplied payload equality or timestamp bound. -/
theorem sender_byte {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height 0) (hS:cv (codec tr) 0 r fS=1) (hg:cv (codec tr) 0 r g<8) :
    cv (codec tr) 0 r bpost=idByte ids (cv (codec tr) 0 r kidx) (cv (codec tr) 0 r g) := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hrow:=ProcPriorCodecSoundSdlRows.sender_row hL hr hS
  obtain ⟨seed,hseed,hpublic⟩:=ProcessRepairSdlFinite.public_origin view r hr
    (by rw [hrow.1];decide)
  rw [I.count,hrec] at hpublic
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hpublic)
  have hR:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).1
  have hk:=record_index hL hr hR
  have ho:oE.eval (codec tr) 0 r pub=Fp.ofNat (cv (codec tr) 0 r g) := by
    have he:=hrow.2.2.1
    rw [(ProcPriorCodecSoundSdlDescent.messages (codec tr) 0 r pub).1] at he
    have hh:=congrArg (fun xs:List Fp=>xs[3]!) he
    simpa only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,
      List.getElem!_cons_succ,List.getElem!_cons_zero] using hh
  exact (dl_pub hn hmem hseed (cv_lt r klo) (cv_lt r khi) (by omega) (cv_lt r bpost) hk
    (by simp only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,ho])).2

theorem start_bytes {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height 0) (hs:cv (codec tr) 0 r rs=1) :
    r+7<tr.height 0 ∧ ∀i,i<8→cv (codec tr) 0 (r+i) bpost=idByte ids (cv (codec tr) 0 r kidx) i := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hw:=ProcPriorCodecSoundGeometry.sender_walk hL hr hs
  refine ⟨(hw 7 (by decide)).1,?_⟩
  intro i hi
  obtain ⟨hri,hS,hg,_,_⟩:=hw i hi
  have he:=sender_byte view I ids hn hrec (r+i) hri hS (by omega)
  rwa [hg,sender_index hL hr hs i hi] at he
/-- Prepared public SDL seed records authenticate the sender bytes of every
corrected record start to the actual current layout. One-layout preparation
allows any actual prepared scheduler instance to name that layout. -/
theorem prepared_start_bytes {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd : List (Nat×Nat))
    (hrec:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (r : Nat) (hr:r<tr.height 0) (hs:cv (codec tr) 0 r rs=1) :
    r+7<tr.height 0 ∧ ∀i,i<8→cv (codec tr) 0 (r+i) bpost=idByte sp.ids (cv (codec tr) 0 r kidx) i := by
  have hn:sp.ids.length≤64 := (prepD0_sched hprep sp hsp).n64
  have hp:I.recs B_SDL true=dlRecs 0 sp.ids := by
    rw [hrec,render_dlSend]
    obtain ⟨ids,hids⟩:=prepD0_ids hprep
    cases he:p.sched with
    | nil=>simp [he] at hsp
    | cons a as=>
      have ha:a∈p.sched := by simp [he]
      have hid:a.ids=sp.ids := (hids a ha).trans (hids sp hsp).symm
      simp only [he,List.map_cons,List.getD_cons_zero,instOf,hid]
  exact start_bytes view I sp.ids hn hp r hr hs
end ZkFormal.NearV3.Candidates.ProcessRepairSdlIds
