import ZkFormal.NearV3.Render.Ups.CodecRelayInventory
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

/-- Public SPAR supply bounds this candidate table's actual receives. This is
an ordinary global bus consequence, with other receivers counted nonnegatively. -/
def CodecSparSupply (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (Ps : List InstPub) (fwd : List (Nat×Nat)) : Prop :=
  ∀m,tableBusCount codecTable.interactions tr t pub B_SPAR false m ≤
    ((render Ps fwd).par.map (·.map Fp.ofNat)).count m

private theorem recvCount (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) (m : List Fp) :
    tableBusCount codecTable.interactions tr t pub b false m =
    tableBusCount Codec.interactions tr t pub b false m := by
  rw [tableBusCount_eq,tableBusCount_eq]
  congr 1
  apply UpsRows.flatMap_congr'
  intro r _
  exact codecRelay_rowRecvs tr t r pub b

private theorem par_mem_row (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hm : (Codec.interactions[6]!).multNat tr t r pub=1) :
    (Codec.interactions[6]!).msgVal tr t r pub∈rowTraffic Codec.interactions tr t r pub B_SPAR false := by
  unfold rowTraffic
  refine List.mem_flatMap.mpr ⟨Codec.interactions[6]!,codec_mem 6 (by decide),?_⟩
  rw [if_pos (by rw [Codec.i6_def];exact ⟨rfl,rfl⟩),hm]
  simp

theorem codecRelay_first_par {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) {f : Nat}
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Codec.kF=1) :
    Chacha.cv tr t f Codec.tau<Ps.length ∧
      (Codec.interactions[6]!).msgVal tr t f pub =
      (parCodec (Chacha.cv tr t f Codec.tau) (Ps.getD (Chacha.cv tr t f Codec.tau) instD)).map Fp.ofNat := by
  obtain ⟨_,_,_,_,hm,hmsg,_⟩:=Codec.codec_first hl hh hf hF
  have hc : 0<tableBusCount Codec.interactions tr t pub B_SPAR false
      ((Codec.interactions[6]!).msgVal tr t f pub) := by
    rw [tableBusCount_eq]
    apply List.count_pos_iff.mpr
    exact List.mem_flatMap.mpr ⟨f,List.mem_range.mpr hf,par_mem_row tr t f pub hm⟩
  have hs:=hs ((Codec.interactions[6]!).msgVal tr t f pub)
  rw [recvCount] at hs
  apply par_codec_mem (Ps:=Ps) (fwd:=fwd) hn (List.count_pos_iff.mp (by omega)) (Chacha.cv_lt _ _)
  · rw [hmsg];rfl
  · rw [hmsg];rfl

theorem codecRelay_block_unique {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) {f g : Nat}
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Codec.kF=1)
    (hg : g<tr.height t) (hG : Chacha.cv tr t g Codec.kF=1)
    (ht : Chacha.cv tr t f Codec.tau=Chacha.cv tr t g Codec.tau) : f=g := by
  by_cases he : f=g
  · exact he
  exfalso
  obtain ⟨htf,hpf⟩:=codecRelay_first_par hl hh hs hn hf hF
  obtain ⟨_,hpg⟩:=codecRelay_first_par hl hh hs hn hg hG
  rw [←ht] at hpg
  obtain ⟨_,_,_,_,hmf,_⟩:=Codec.codec_first hl hh hf hF
  obtain ⟨_,_,_,_,hmg,_⟩:=Codec.codec_first hl hh hg hG
  let m := (parCodec (Chacha.cv tr t f Codec.tau) (Ps.getD (Chacha.cv tr t f Codec.tau) instD)).map Fp.ofNat
  have hfmem : m∈rowTraffic Codec.interactions tr t f pub B_SPAR false :=
    by dsimp [m]; rw [←hpf]; exact par_mem_row tr t f pub hmf
  have hgmem : m∈rowTraffic Codec.interactions tr t g pub B_SPAR false :=
    by dsimp [m]; rw [←hpg]; exact par_mem_row tr t g pub hmg
  have hc : 2≤tableBusCount Codec.interactions tr t pub B_SPAR false m := by
    rw [tableBusCount_eq]
    exact count_two _ m he hfmem hgmem _ List.nodup_range (List.mem_range.mpr hf) (List.mem_range.mpr hg)
  have hs:=hs m
  rw [recvCount] at hs
  have hp:=par_codec_count (fwd:=fwd) hn _ htf
  dsimp [m] at hc hs
  omega
end ZkFormal.NearV3.Render.UpsRelay
