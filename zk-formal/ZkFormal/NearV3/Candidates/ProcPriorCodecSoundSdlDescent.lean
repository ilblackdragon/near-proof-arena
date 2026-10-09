import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlSource
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlDescent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

def payload (tr : Trace Fp) (tc r : Nat) (pub : List Fp) : List Fp :=
  [Fp.ofNat (cv tr tc r klo),Fp.ofNat (cv tr tc r khi),oE.eval tr tc r pub,Fp.ofNat (cv tr tc r bpost)]

theorem messages (tr : Trace Fp) (tc r : Nat) (pub : List Fp) :
    (ProcPriorCodecActual.interactions[7]!).msgVal tr tc r pub=Fp.ofNat (cv tr tc r tau)::payload tr tc r pub ∧
    (ProcPriorCodecActual.interactions[8]!).msgVal tr tc r pub=Fp.ofNat (cv tr tc r tau+1)::payload tr tc r pub := by
  rw [ProcPriorCodecSoundSdlRows.receive_same,ProcPriorCodecSoundSdlRows.send_same,i7_def,i8_def]
  have ht:(Expr.add (c tau) (k 1)).eval tr tc r pub=Fp.ofNat (cv tr tc r tau+1) := ev_of (by
    simp only [zev_add,zev_c,zev_k,cur_cv]
    omega)
  simp only [Interaction.msgVal,List.map_cons,List.map_nil,ev_c,ht,payload]
  trivial

theorem multiplicity_same (tr : Trace Fp) (tc r : Nat) (pub : List Fp) :
    (ProcPriorCodecActual.interactions[7]!).multNat tr tc r pub=
      (ProcPriorCodecActual.interactions[8]!).multNat tr tc r pub := rfl

/-- Global balance and SDL ownership force every live receive back to a public
seed. The only remaining domain premise is non-wrapping tau on live SDL sends;
this must come from corrected SPAR/block extraction, not native generation. -/
theorem public_origin {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (htau:∀r,r<tr.height tc→(ProcPriorCodecActual.interactions[8]!).multNat tr tc r pub≠0→cv tr tc r tau+1<P)
    (r : Nat) (hr:r<tr.height tc) (hm:(ProcPriorCodecActual.interactions[7]!).multNat tr tc r pub≠0) :
    ∃seedTau,seedTau≤cv tr tc r tau ∧
      pubCount AP pub B_SDL true (Fp.ofNat seedTau::payload tr tc r pub)≠0 := by
  generalize hn:cv tr tc r tau=n
  induction n using Nat.strongRecOn generalizing r with
  | ind n ih=>
    have hi:ProcPriorCodecActual.interactions[7]!∈AP.tables[tc]!.interactions := by
      rw [htab]
      exact ProcPriorCodecSoundSdlRows.receive_member
    rcases recv_src hH ht hr hi (by rfl : (ProcPriorCodecActual.interactions[7]!).bus=B_SDL)
      (by rfl : (ProcPriorCodecActual.interactions[7]!).send=false) hm with hp|hsrc
    · exact ⟨n,by omega,by simpa only [(messages tr tc r pub).1,hn] using hp⟩
    · obtain ⟨t',ht',r',hr',i',hi',hb,hs,hmsg,hm'⟩:=hsrc
      have he:t'=tc := Classical.byContradiction (fun hne=>own.only t' ht' hne i' hi' hb)
      subst t'
      rw [htab] at hi'
      have hei:=ProcPriorCodecSoundSdlSource.sender_eq hi' hb hs
      subst i'
      rw [(messages tr tc r' pub).2,(messages tr tc r pub).1] at hmsg
      have hd:=List.cons.inj hmsg
      have ht':=htau r' hr' hm'
      have heq:=ProcPriorCodecSoundPublicId.nat_eq _ _ ht' (cv_lt r tau) hd.1
      have hlt:cv tr tc r' tau<n := by omega
      obtain ⟨seed,hseed,hpublic⟩:=ih (cv tr tc r' tau) hlt r' hr'
        (by rwa [multiplicity_same]) rfl
      exact ⟨seed,by omega,by rwa [hd.2] at hpublic⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlDescent
