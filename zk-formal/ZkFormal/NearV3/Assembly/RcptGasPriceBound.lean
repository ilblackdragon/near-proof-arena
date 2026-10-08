import ZkFormal.NearV3.Assembly.RcptGasPrepared

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 Sched ZkFormal.Air ZkFormal.Algebra

theorem decodeBlockV6_gasPrice {version : Nat} {prevHash lite rest : Bytes} {hdr : BlockHdr}
    (h : decodeBlockV6 version prevHash lite rest=.ok hdr) : hdr.nextGasPrice<256^16 := by
  unfold decodeBlockV6 at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    simpa only [Params.two128] using V3.pU128_lt (by assumption)

theorem decodeBlk_gasPrice {r : BlockRec} {b : Blk} (h : decodeBlk r=.ok b) :
    b.hdr.nextGasPrice<256^16 := by
  unfold decodeBlk at h
  obtain ⟨hdr,hh,h⟩ := bind_ok h
  obtain ⟨slots,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h
  exact decodeBlockV6_gasPrice hh

private theorem decoded_block_gasPrice {rs : List BlockRec} {bs : List Blk} {i : Nat} {b out : Blk}
    (hp : (pure b : Except String Blk)=.ok out) (hb : bs[i]?=some b)
    (hm : rs.mapM decodeBlk=.ok bs) : out.hdr.nextGasPrice<256^16 := by
  cases hp
  obtain ⟨r,_,hr⟩ := mapM_ok _ _ _ hm b (List.mem_of_getElem? hb)
  exact decodeBlk_gasPrice hr

set_option maxHeartbeats 4000000 in
theorem prepClaim_gasPrice_bound {cb : Bytes} {pc : PrepC} (h : prepClaim cb=.ok pc) :
    pc.hdr.gasPrice<256^16 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    exact decoded_block_gasPrice (by assumption) (by assumption) (by assumption)

theorem prepD0_gasPrice_bound {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) : p.hdr.gasPrice<256^16 := by
  obtain ⟨pc,hc,hb⟩ := bind_ok hp
  rw [prepBody_gasPrice hb]
  exact prepClaim_gasPrice_bound hc

theorem prepD0_native_gasPrice_bound {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    (m.ctx k).gasPrice<256^16 := by
  rw [←prepD0_native_gasPrice hp hk hm]
  exact prepD0_gasPrice_bound hp

theorem prepD0_native_gas_evidence {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} (overhead : Nat)
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    GasPublicBytes (m.ctx k) (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) ∧
      (m.ctx k).gasPrice<256^16 :=
  ⟨prepD0_native_GasPublicBytes overhead hp hk hm,prepD0_native_gasPrice_bound hp hk hm⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
