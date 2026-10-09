import ZkFormal.NearV3.Render.Ups.CodecRelaySupply
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

theorem codecRelay_active_instance {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    (hr : r<tr.height t) (ha : Chacha.cv tr t r Codec.act=1) :
    ∃f,f<tr.height t ∧ Chacha.cv tr t f Codec.kF=1 ∧ Codec.IC tr t r f := by
  obtain ⟨f,hfr,hF,he⟩:=Codec.codec_cover hl hh r hr ha
  have hf : f<tr.height t := by omega
  obtain ⟨_,_,_,_,_,_,hH,hR,_,hZ,_,hA,_⟩:=Codec.codec_block hl hh hf hF
  refine ⟨f,hf,hF,?_⟩
  by_cases h0 : r-f<5
  · have h := (hH (r-f) h0).2.2.2.1
    simpa only [Nat.add_sub_of_le hfr] using h
  · by_cases h1 : r-f<5+24*Chacha.cv tr t f Codec.NN
    · have hk : (r-f-5)/24<Chacha.cv tr t f Codec.NN := by omega
      have h:=(hR ((r-f-5)/24) hk ((r-f-5)%24) (by omega)).2.2.2.2.2.2
      have he : f+5+24*((r-f-5)/24)+(r-f-5)%24=r := by omega
      rw [he] at h
      exact h
    · by_cases h2 : r-f<5+24*Chacha.cv tr t f Codec.NN+32
      · have h:=(hZ (r-f-(5+24*Chacha.cv tr t f Codec.NN)) (by omega)).2.2.2.2.1
        have he : f+5+24*Chacha.cv tr t f Codec.NN+(r-f-(5+24*Chacha.cv tr t f Codec.NN))=r := by omega
        rw [he] at h
        exact h
      · have h:=(hA (r-f-(5+24*Chacha.cv tr t f Codec.NN+32)) (by omega)).2.2.2
        have he : f+5+24*Chacha.cv tr t f Codec.NN+32+(r-f-(5+24*Chacha.cv tr t f Codec.NN+32))=r := by omega
        rw [he] at h
        exact h

theorem codecRelay_active_tau {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length≤32) (hr : r<tr.height t) (ha : Chacha.cv tr t r Codec.act=1) :
    Chacha.cv tr t r Codec.tau<32 := by
  obtain ⟨f,hf,hF,hi⟩:=codecRelay_active_instance hl hh hr ha
  have he:=hi Codec.tau (by simp [Codec.instCols])
  have ht:=(codecRelay_first_par hl hh hs (by omega) hf hF).1
  omega
end ZkFormal.NearV3.Render.UpsRelay
