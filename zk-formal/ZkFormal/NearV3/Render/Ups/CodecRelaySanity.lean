import ZkFormal.NearV3.Render.Ups.CodecRelayActive
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

/-- Complete actual unchanged Codec sanity-hash BYTES inventory, lifted to
canonical natural messages for the trie extraction interface. -/
def codecSanityMsgs (tr : Trace Fp) (t : Nat) (pub : List Fp) : List Msg :=
  ((List.range (tr.height t)).flatMap fun r=>rowTraffic Codec.interactions tr t r pub B_BYTES true).map
    (List.map Fp.toNat)

theorem codecSanityMsgs_count (tr : Trace Fp) (t : Nat) (pub : List Fp) (m : List Fp) :
    cnt (codecSanityMsgs tr t pub) m=tableBusCount Codec.interactions tr t pub B_BYTES true m := by
  rw [tableBusCount_eq]
  unfold cnt codecSanityMsgs
  rw [List.map_map]
  have he : Msg.toFp ∘ List.map Fp.toNat = id := by
    funext xs
    simp [Function.comp_def,Msg.toFp,List.map_map,Fp.ofNat_toNat]
  rw [he,List.map_id]

private theorem row_sanity (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic Codec.interactions tr t r pub B_BYTES true=
      List.replicate ((Codec.interactions[2]!).multNat tr t r pub)
        ((Codec.interactions[2]!).msgVal tr t r pub) := by
  simp [rowTraffic,Codec.interactions,B_BYTES,B_VBYTES,B_DIGEST,Sched.B_SPOST,
    Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP]

private theorem sanity_active {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hr : r<tr.height t)
    (hm : (Codec.interactions[2]!).multNat tr t r pub≠0) : Chacha.cv tr t r Codec.act=1 := by
  have hk:=Codec.kinds hl hr
  by_cases ha : Chacha.cv tr t r Codec.act=1
  · exact ha
  have hz : Chacha.cv tr t r Codec.kZ=0 := by omega
  have hA : Chacha.cv tr t r Codec.kA=0 := by omega
  have h0 : (Codec.interactions[2]!).multNat tr t r pub=0 := by
    apply Codec.mult_zero (by rw [Codec.i2_def])
    simp only [Chacha.zev_add,Chacha.zev_c,Chacha.cur_cv,hz,hA]
    rfl
  exact False.elim (hm h0)

/-- Codec's remaining SHA family is exactly kind11, hence disjoint from every
compact UPS/fresh relay job (kind12). Bounds come from actual public SPAR. -/
theorem codecSanityMsgs_other {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length≤32) :
    ∀m∈codecSanityMsgs tr t pub,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS := by
  intro m hm a ha
  obtain ⟨M,hM,rfl⟩:=List.mem_map.mp hm
  obtain ⟨r,hr,hM⟩:=List.mem_flatMap.mp hM
  rw [row_sanity] at hM
  obtain ⟨hg,rfl⟩:=List.mem_replicate.mp hM
  have hr:=List.mem_range.mp hr
  have ht:=codecRelay_active_tau hl hh hs hn hr (sanity_active hl hr hg)
  rw [Codec.i2_def] at ha
  simp only [Interaction.msgVal,List.map_cons,List.map_nil,Codec.ev_shaId,Codec.ev_c,
    List.head?_cons,Option.some.injEq] at ha
  have hi : 11+16*Chacha.cv tr t r Codec.tau<P := by have := UpsRows.P_gt;omega
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hi] at ha
  subst a
  exact ⟨hi,by simp [Nat.add_mod,Nat.mul_mod,K_VUPS]⟩
end ZkFormal.NearV3.Render.UpsRelay
