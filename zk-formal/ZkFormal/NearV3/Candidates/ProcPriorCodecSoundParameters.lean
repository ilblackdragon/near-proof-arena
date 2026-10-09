import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundOrigin
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSpar
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundParameters
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched

theorem header_n {tr : Trace Fp} {t r : Nat} {pub : List Fp} (tauV : Nat) (P0 : InstPub)
    (h : (ProcPriorCodecActual.table.interactions[6]!).msgVal tr t r pub=(parCodec tauV P0).map Fp.ofNat) :
    cv tr t r Codec.nn=P0.n%ZkFormal.Algebra.P := by
  rw [ProcPriorCodecSoundSpar.i6,Codec.i6_def] at h
  have he:=congrArg (fun xs : List Fp=>xs[2]!) h
  have hf : Fp.ofNat (cv tr t r Codec.nn)=Fp.ofNat P0.n := by
    simpa [ProcPriorCodecSoundSpar.i6,Codec.i6_def,Interaction.msgVal,parCodec,Codec.ev_c] using he
  have hn:=congrArg Fp.toNat hf
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show cv tr t r Codec.nn<ZkFormal.Algebra.P from cv_lt _ _)] using hn

/-- All active corrected Codec rows inherit the timestamp and shard count
from a real publicly authenticated first-row parameter packet. -/
theorem active_parameters {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH : HoldsP AP pub tr) {tc : Nat} (htc : tc<AP.tables.length)
    (htab : AP.tables[tc]! =ProcPriorCodecActual.table) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat×Nat))
    (hrec : I.recs B_SPAR true=(render Ps fwd).par) (hlen : Ps.length<2013265921)
    {r : Nat} (hr : r<tr.height tc) (ha : cv tr tc r Codec.act=1) :
    cv tr tc r Codec.tau<Ps.length ∧
      cv tr tc r Codec.nn=(Ps.getD (cv tr tc r Codec.tau) instD).n%ZkFormal.Algebra.P := by
  have hl:=local_of_holdsP hH htc
  rw [htab] at hl
  have hL : ProcPriorCodecSoundRows.CLocal tr tc pub := hl
  obtain ⟨f,hfr,hF,hconst⟩:=ProcPriorCodecSoundOrigin.instance_origin hL r hr ha
  have ht:=hconst Codec.tau (by simp)
  have hn:=hconst Codec.nn (by simp)
  obtain ⟨hbound,hpar⟩:=ProcPriorCodecSoundSpar.first_par hH htc htab SO I Ps fwd hrec hlen (by omega) hF
  have hnn:=header_n _ _ hpar
  simp only [ht,hn] at hbound hnn
  exact ⟨hbound,hnn⟩

theorem active_small {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH : HoldsP AP pub tr) {tc : Nat} (htc : tc<AP.tables.length)
    (htab : AP.tables[tc]! =ProcPriorCodecActual.table) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat×Nat))
    (hrec : I.recs B_SPAR true=(render Ps fwd).par) (hlen : Ps.length≤33)
    (hns : ∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r : Nat} (hr : r<tr.height tc) (ha : cv tr tc r Codec.act=1) :
    cv tr tc r Codec.tau<33 ∧ cv tr tc r Codec.tau+1<ZkFormal.Algebra.P ∧
      cv tr tc r Codec.nn=(Ps.getD (cv tr tc r Codec.tau) instD).n ∧
      1≤cv tr tc r Codec.nn ∧ cv tr tc r Codec.nn≤64 := by
  obtain ⟨ht,hn⟩:=active_parameters hH htc htab SO I Ps fwd hrec (by omega) hr ha
  have hm : Ps.getD (cv tr tc r Codec.tau) instD∈Ps := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht,Option.getD_some]
    exact List.getElem_mem ht
  have hsz:=hns _ hm
  have hp : 64<ZkFormal.Algebra.P := by decide +kernel
  rw [Nat.mod_eq_of_lt (by omega)] at hn
  exact ⟨by omega,by omega,hn,by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundParameters
