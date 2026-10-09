import ZkFormal.NearV3.Candidates.ProcSdlFiniteDescent
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlFinite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundSdlDescent

/-- Physical log22 height excludes any closed SDL predecessor cycle, including
field-timestamp wrap. Consequently a live receive has a real public origin;
no independent timestamp bound or generator premise is needed. -/
theorem public_origin {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (r : Nat) (hr:r<tr.height tc) (hm:(ProcPriorCodecActual.interactions[7]!).multNat tr tc r pub≠0) :
    ∃seedTau,seedTau<P ∧ pubCount AP pub B_SDL true (Fp.ofNat seedTau::payload tr tc r pub)≠0 := by
  classical
  apply Classical.byContradiction
  intro hn
  let A (v : Nat) := v<tr.height tc ∧
    (ProcPriorCodecActual.interactions[7]!).multNat tr tc v pub≠0 ∧ payload tr tc v pub=payload tr tc r pub
  have hheight:tr.height tc<P := by
    have hh:=height_le hH ht htab (by rfl : ProcPriorCodecActual.table.maxLog=22)
    have hp:2^22<P := by decide +kernel
    omega
  refine ProcSdlFiniteDescent.no_closed_set (tr.height tc) hheight A (fun v=>cv tr tc v tau) ?_ ?_ r ⟨hr,hm,rfl⟩
  · intro v hv
    exact ⟨hv.1,cv_lt v tau⟩
  · intro v hv
    have hi:ProcPriorCodecActual.interactions[7]!∈AP.tables[tc]!.interactions := by
      rw [htab]
      exact ProcPriorCodecSoundSdlRows.receive_member
    rcases recv_src hH ht hv.1 hi (by rfl : (ProcPriorCodecActual.interactions[7]!).bus=B_SDL)
      (by rfl : (ProcPriorCodecActual.interactions[7]!).send=false) hv.2.1 with hp|hsrc
    · have hpub:pubCount AP pub B_SDL true (Fp.ofNat (cv tr tc v tau)::payload tr tc r pub)≠0 := by
        simpa only [(messages tr tc v pub).1,hv.2.2] using hp
      exact (hn ⟨cv tr tc v tau,cv_lt v tau,hpub⟩).elim
    · obtain ⟨t',ht',w,hw,i',hi',hb,hs,hmsg,hm'⟩:=hsrc
      have he:t'=tc := Classical.byContradiction (fun hne=>own.only t' ht' hne i' hi' hb)
      subst t'
      rw [htab] at hi'
      have hei:=ProcPriorCodecSoundSdlSource.sender_eq hi' hb hs
      subst i'
      rw [(messages tr tc w pub).2,(messages tr tc v pub).1] at hmsg
      have hd:=List.cons.inj hmsg
      have hstamp:=congrArg Fp.toNat hd.1
      simp only [Fp.toNat_ofNat] at hstamp
      have hb:cv tr tc v tau<P := cv_lt v tau
      rw [Nat.mod_eq_of_lt hb] at hstamp
      refine ⟨w,⟨hw,?_,hd.2.trans hv.2.2⟩,hstamp⟩
      rwa [multiplicity_same]
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlFinite
