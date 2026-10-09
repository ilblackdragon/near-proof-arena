import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlRows
import ZkFormal.NearV3.Sched.Link.SoundIds
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

theorem only_sender : ProcPriorCodecActual.interactions.filter (fun i=>i.bus==B_SDL && i.send)=
    [ProcPriorCodecActual.interactions[8]!] := rfl

theorem sender_eq {i : Interaction} (hi:i∈ProcPriorCodecActual.interactions)
    (hb:i.bus=B_SDL) (hs:i.send=true) : i=ProcPriorCodecActual.interactions[8]! := by
  have hm:i∈ProcPriorCodecActual.interactions.filter (fun i=>i.bus==B_SDL && i.send) :=
    List.mem_filter.mpr ⟨hi,by simp [hb,hs]⟩
  rw [only_sender] at hm
  exact List.mem_singleton.mp hm

/-- Genuine global SDL ownership gives every live corrected sender byte a
public origin or a predecessor Codec send. This is not bus70 authentication:
bus70 only carries the resulting layout inventory downstream to ID lookup. -/
theorem start_sources {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (r : Nat) (hr:r<tr.height tc) (hs:cv tr tc r rs=1) :
    ∀j,j<8→
      pubCount AP pub B_SDL true ((ProcPriorCodecActual.interactions[7]!).msgVal tr tc (r+j) pub)≠0 ∨
      ∃r',r'<tr.height tc ∧
        (ProcPriorCodecActual.interactions[8]!).msgVal tr tc r' pub=
          (ProcPriorCodecActual.interactions[7]!).msgVal tr tc (r+j) pub ∧
        (ProcPriorCodecActual.interactions[8]!).multNat tr tc r' pub≠0 := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  intro j hj
  obtain ⟨hrj,hm,_⟩:=ProcPriorCodecSoundSdlRows.start_receives hL hr hs j hj
  have hi:ProcPriorCodecActual.interactions[7]!∈AP.tables[tc]!.interactions := by
    rw [htab]
    exact ProcPriorCodecSoundSdlRows.receive_member
  rcases recv_src hH ht hrj hi (by rfl : (ProcPriorCodecActual.interactions[7]!).bus=B_SDL)
    (by rfl : (ProcPriorCodecActual.interactions[7]!).send=false) (by rw [hm];decide) with hp|hsrc
  · exact Or.inl hp
  · right
    obtain ⟨t',ht',r',hr',i',hi',hb,hs',hmsg,hm'⟩:=hsrc
    have he:t'=tc := Classical.byContradiction (fun hn=>own.only t' ht' hn i' hi' hb)
    subst t'
    rw [htab] at hi'
    have hei:=sender_eq hi' hb hs'
    subst i'
    exact ⟨r',hr',hmsg,hm'⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlSource
