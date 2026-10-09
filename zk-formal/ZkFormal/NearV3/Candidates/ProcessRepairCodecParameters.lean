import ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecParameters
import ZkFormal.NearV3.Candidates.ProcessRepairShaFacts
namespace ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem first_par {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length<2013265921)
    {r:Nat} (hr:r<tr.height 0) (hF:cv (codec tr) 0 r Codec.kF=1) :
    cv (codec tr) 0 r Codec.tau<Ps.length ∧
      (ProcPriorCodecActual.table.interactions[6]!).msgVal (codec tr) 0 r pub=
        (parCodec (cv (codec tr) 0 r Codec.tau) (Ps.getD (cv (codec tr) 0 r Codec.tau) instD)).map Fp.ofNat := by
  have hm:(ProcPriorCodecActual.table.interactions[6]!).multNat (codec tr) 0 r pub=1 := by
    rw [ProcPriorCodecSoundSpar.i6]
    apply Codec.mult_of (by rw [Codec.i6_def])
    simp only [zev_c,cur_cv,hF]
    rfl
  have ht:0<AP.tables.length := by rw [v.length];decide +kernel
  have hi:interaction (ProcPriorCodecActual.table.interactions[6]!)∈AP.tables[0]!.interactions := by
    rw [v.wires]
    exact member ProcPriorCodecSoundSpar.i6_mem (by decide +kernel)
  have hp:=recv_pub v.valid (ProcessRepairInterface.ownership v (fun _ i=>i.bus=B_SPAR→i.send=false) (spar_none (AP:=ProcessRepairBalance.reference AP) rfl)) hpub ht hr hi
    (show (interaction (ProcPriorCodecActual.table.interactions[6]!)).bus=B_SPAR from rfl)
    (show (interaction (ProcPriorCodecActual.table.interactions[6]!)).send=false from rfl)
    (by rw [mult,hm];exact Nat.one_ne_zero)
  rw [message,I.count,hrec] at hp
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hp)
  apply par_codec_mem hlen hmem (cv_lt _ _)
  · rw [ProcPriorCodecSoundSpar.i6,Codec.i6_def]
    simp [Interaction.msgVal,Codec.ev_c]
  · rw [ProcPriorCodecSoundSpar.i6,Codec.i6_def]
    simp [Interaction.msgVal,Codec.ev_k]

theorem local_codec {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    ProcPriorCodecSoundRows.CLocal (codec tr) 0 pub := by
  have h:=v.component 8 (by decide +kernel) (by decide)
  have hb:ZkFormal.Near.TableLocal ProcPriorCodecActual.table (codec tr) 0 pub:=
    (ProcPriorComparatorRouting.local_iff _ _ _ _).mp h
  exact hb.constr

/-- Actual fused Codec active rows inherit public SPAR parameters. The concrete
family supplies the no-table-sender proof; only public segment ownership and
its authenticated record inventory remain explicit. -/
theorem active_small {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0) (ha:cv (codec tr) 0 r Codec.act=1) :
    cv (codec tr) 0 r Codec.tau<33 ∧
    cv (codec tr) 0 r Codec.nn=(Ps.getD (cv (codec tr) 0 r Codec.tau) instD).n ∧
    1≤cv (codec tr) 0 r Codec.nn ∧ cv (codec tr) 0 r Codec.nn≤64 ∧
    1≤cv (codec tr) 0 r Codec.NN ∧ cv (codec tr) 0 r Codec.NN≤4096 := by
  have hL:=local_codec v
  obtain ⟨f,hfr,hF,hc⟩:=ProcPriorCodecSoundOrigin.instance_origin hL r hr ha
  obtain ⟨ht,hpar⟩:=first_par v hpub I Ps fwd hrec (by omega) (by omega) hF
  have hn:=ProcPriorCodecSoundParameters.header_n _ _ hpar
  have ht0:=hc Codec.tau (by simp)
  have hn0:=hc Codec.nn (by simp)
  rw [ht0] at ht
  rw [ht0,hn0] at hn
  have hm:Ps.getD (cv (codec tr) 0 r Codec.tau) instD∈Ps := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht,Option.getD_some]
    exact List.getElem_mem ht
  have hs:=hns _ hm
  rw [Nat.mod_eq_of_lt (show (Ps.getD (cv (codec tr) 0 r Codec.tau) instD).n<P by rw [P_val];omega)] at hn
  have hsq:=ProcPriorCodecSoundRecordBound.active_square hL hr ha (by omega)
  have hh0:=Nat.mul_le_mul (show 1≤cv (codec tr) 0 r Codec.nn by omega) (show 1≤cv (codec tr) 0 r Codec.nn by omega)
  have hh1:=Nat.mul_le_mul (show cv (codec tr) 0 r Codec.nn≤64 by omega) (show cv (codec tr) 0 r Codec.nn≤64 by omega)
  exact ⟨by omega,hn,by omega,by omega,by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
