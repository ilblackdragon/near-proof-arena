import ZkFormal.NearV3.Assembly.RcptNativeRid
import ZkFormal.NearV3.Assembly.NativeHeader
import ZkFormal.NearV3.Assembly.PrepContext
import ZkFormal.NearV3.Assembly.PrepFacts
import ZkFormal.NearV3.Assembly.RoutingBoundedPrep
import ZkFormal.NearV3.Public.HeaderBinding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 Sched ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

set_option maxHeartbeats 4000000 in
theorem prepClaim_outcomeRoot {cb : Bytes} {pc : PrepC} (h : prepClaim cb=.ok pc) :
    pc.hdr.outcomeRoot=pc.H.prevOutcomeRoot := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; rfl

theorem prepBody_outcomeRoot {pc : PrepC} {hint : Hint} {p : Prep}
    (h : prepBody pc hint=.ok p) : p.hdr.outcomeRoot=pc.hdr.outcomeRoot := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first
    | (simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; rfl)
    | (cases h)

theorem prepD0_native_outcomeRoot {cb wb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hd : decodeW wb=.ok w)
    (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w) :
    p.hdr.outcomeRoot=outcomeRoot m.result.outcomes := by
  obtain ⟨pc,hpc,hbody⟩ := bind_ok hp
  have hpctx := prepClaim_native_context hpc hk hm
  rw [prepBody_outcomeRoot hbody,prepClaim_outcomeRoot hpc,hpctx.header]
  obtain ⟨n,last,hn,_,_,_,hh⟩ := checkD0_native_header hk hd hc
  have he := MainExecutionV3.NativeValid.unique hm hn
  subst n
  exact hh.outcomeRoot

theorem prepared_outcome_byte (p : Prep) (overhead i : Nat)
    (hr : Public.RootsSized p) (hi : i<32) :
    (Public.preparedBytes p overhead).getD (PH_OUT+i) 0=p.hdr.outcomeRoot.getD i 0 := by
  rw [Public.prepared_header p overhead hr (by unfold PH_OUT;omega)]
  let preBytes := borshBytes prepTag++u32 p.hdr.K++u32 p.hdr.n++u64 p.hdr.own++
    u32 p.hdr.ownIdx++u32 p.hdr.numShards++u64 p.hdr.height++u128 p.hdr.gasPrice++
    u64 p.hdr.gasLimit++p.hdr.prevStateRoot++p.hdr.postStateRoot
  let suffix := u128 p.hdr.balanceBurnt++u32 p.body.length++u32 overhead
  have he : Public.headerBytes p overhead=preBytes++p.hdr.outcomeRoot++suffix := by
    simp only [Public.headerBytes,PrepHdr.encode,preBytes,suffix,List.append_assoc]
  have hl : preBytes.length=PH_OUT := by
    have hh := Public.oldHeader_length p hr
    obtain ⟨hpre,hpost,hout⟩ := hr
    simp only [preBytes,List.length_append,u32,u64,u128,leN_length,hpre,hpost]
    simp only [List.length_append,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout] at hh
    unfold PH_OUT
    omega
  rw [he,←hl]
  exact Public.getD_middle preBytes _ suffix (by rw [hr.2.2];exact hi)

theorem prepared_outcome_public (p : Prep) (overhead : Nat) (hr : Public.RootsSized p) :
    pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_OUT 32=
      p.hdr.outcomeRoot.map UInt8.toNat := by
  apply List.ext_getElem
  · simp [pubBytes,hr.2.2]
  · intro i h1 h2
    have hi : i<32 := by simpa [pubBytes] using h1
    have hl : i<p.hdr.outcomeRoot.length := by rw [hr.2.2];exact hi
    simp only [pubBytes,List.getElem_map,List.getElem_range]
    change ((ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)).getD (PH_OUT+i) 0).toNat=_
    rw [Public.pub_getD,prepared_outcome_byte p overhead i hr hi,native_byte_decode]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some]

/-- The actual normalized public statement commits the same native outcome root,
using checker acceptance and native execution uniqueness, not a root premise. -/
theorem prepD0_native_outcome_public {cb wb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} (overhead : Nat)
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hd : decodeW wb=.ok w)
    (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w) :
    pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes
      (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)) PH_OUT 32=
      (outcomeRoot m.result.outcomes).map UInt8.toNat := by
  rw [prepared_outcome_public _ overhead (by exact prepD0_roots (p:=p) hp)]
  change p.hdr.outcomeRoot.map UInt8.toNat=_
  rw [prepD0_native_outcomeRoot hp hk hd hc hm]

end ZkFormal.NearV3.Assembly.RcptSkeleton
