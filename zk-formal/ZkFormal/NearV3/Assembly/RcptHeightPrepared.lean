import ZkFormal.NearV3.Assembly.RcptNativeRid
import ZkFormal.NearV3.Assembly.PrepContext
import ZkFormal.NearV3.Assembly.PrepFacts
import ZkFormal.NearV3.Public.HeaderBinding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 Sched ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

set_option maxHeartbeats 4000000 in
theorem prepClaim_height {cb : Bytes} {pc : PrepC} (h : prepClaim cb=.ok pc) :
    pc.hdr.height=pc.ctxB2.height := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; rfl

theorem prepBody_height {pc : PrepC} {hint : Hint} {p : Prep}
    (h : prepBody pc hint=.ok p) : p.hdr.height=pc.hdr.height := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first
    | (simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; rfl)
    | (cases h)

theorem prepD0_native_height {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    p.hdr.height=(m.ctx k).height := by
  obtain ⟨pc,hc,hb⟩ := bind_ok hp
  rw [prepBody_height hb,prepClaim_height hc,(prepClaim_native_context hc hk hm).ctx]

/-- Exact fixed-header gas bytes, before any native context identification. -/
theorem prepared_height_byte (p : Prep) (overhead i : Nat)
    (hr : Public.RootsSized p) (hi : i<8) :
    (Public.preparedBytes p overhead).getD (PH_HEIGHT+i) 0=(u64 p.hdr.height).getD i 0 := by
  rw [Public.prepared_header p overhead hr (by unfold PH_HEIGHT; omega)]
  let preBytes := borshBytes prepTag ++ u32 p.hdr.K ++ u32 p.hdr.n ++ u64 p.hdr.own ++
    u32 p.hdr.ownIdx ++ u32 p.hdr.numShards
  let suffix := u128 p.hdr.gasPrice ++ u64 p.hdr.gasLimit ++ p.hdr.prevStateRoot ++ p.hdr.postStateRoot ++
    p.hdr.outcomeRoot ++ u128 p.hdr.balanceBurnt ++ u32 p.body.length ++ u32 overhead
  have he : Public.headerBytes p overhead=preBytes++u64 p.hdr.height++suffix := by
    simp only [Public.headerBytes,PrepHdr.encode,preBytes,suffix,List.append_assoc]
  have hl : preBytes.length=PH_HEIGHT := by
    simp only [preBytes,List.length_append,u32,u64,leN_length]
    have hh := Public.oldHeader_length p hr
    obtain ⟨hpre,hpost,hout⟩ := hr
    simp only [List.length_append,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout] at hh
    unfold PH_HEIGHT
    omega
  rw [he,←hl]
  exact Public.getD_middle preBytes _ suffix (by simpa [u64,leN_length] using hi)

theorem prepared_HeightPublicBytes (p : Prep) (overhead : Nat) (ctx : ApplyCtx)
    (hr : Public.RootsSized p) (hg : p.hdr.height=ctx.height) :
    HeightPublicBytes ctx (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) := by
  intro i hi
  rw [Public.pub_getD,prepared_height_byte p overhead i hr hi,hg]

theorem prepD0_native_HeightPublicBytes {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} (overhead : Nat)
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    :
    HeightPublicBytes (m.ctx k) (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) :=
  prepared_HeightPublicBytes p overhead (m.ctx k) (prepD0_roots hp) (prepD0_native_height hp hk hm)

end ZkFormal.NearV3.Assembly.RcptSkeleton
