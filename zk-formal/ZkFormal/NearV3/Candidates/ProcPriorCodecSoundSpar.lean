import ZkFormal.NearV3.Candidates.ProcPriorCodecActual
import ZkFormal.NearV3.Sched.Link.CodecSV
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSpar
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched

theorem i6 : ProcPriorCodecActual.table.interactions[6]! =Codec.interactions[6]! := by rfl

theorem i6_mem : ProcPriorCodecActual.table.interactions[6]!∈ProcPriorCodecActual.table.interactions := by
  have hl : 6<ProcPriorCodecActual.table.interactions.length := by decide +kernel
  rw [getElem!_pos _ 6 hl]
  exact List.getElem_mem hl

/-- Corrected Codec's retained parameter receiver authenticates its timestamp
against the actual public SPAR records. No original Codec Local is invoked. -/
theorem first_par {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH : HoldsP AP pub tr) {tc : Nat} (htc : tc<AP.tables.length)
    (htab : AP.tables[tc]! =ProcPriorCodecActual.table) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat×Nat))
    (hrec : I.recs B_SPAR true=(render Ps fwd).par) (hlen : Ps.length<2013265921)
    {r : Nat} (hr : r<tr.height tc) (hF : cv tr tc r Codec.kF=1) :
    cv tr tc r Codec.tau<Ps.length ∧
      (ProcPriorCodecActual.table.interactions[6]!).msgVal tr tc r pub=
        (parCodec (cv tr tc r Codec.tau) (Ps.getD (cv tr tc r Codec.tau) instD)).map Fp.ofNat := by
  have hm : (ProcPriorCodecActual.table.interactions[6]!).multNat tr tc r pub=1 := by
    rw [i6]
    apply Codec.mult_of (by rw [Codec.i6_def])
    simp only [zev_c,cur_cv,hF]
    rfl
  have hp:=recv_pub hH SO.none SO.pub htc hr (by rw [htab]; exact i6_mem)
    (by rw [i6,Codec.i6_def]) (by rw [i6,Codec.i6_def]) (by rw [hm]; exact Nat.one_ne_zero)
  rw [I.count,hrec] at hp
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hp)
  apply par_codec_mem hlen hmem (cv_lt _ _)
  · rw [i6,Codec.i6_def]
    simp [Interaction.msgVal,Codec.ev_c]
  · rw [i6,Codec.i6_def]
    simp [Interaction.msgVal,Codec.ev_k]
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSpar
