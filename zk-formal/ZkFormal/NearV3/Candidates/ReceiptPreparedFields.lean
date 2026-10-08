import ZkFormal.NearV3.Assembly.RcptOutcomePrepared
import ZkFormal.NearV3.Assembly.PrepBodyComplete

namespace ZkFormal.NearV3.Candidates.ReceiptPreparedFields
open NearSpec NearSpecV3 Sched ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton

set_option maxHeartbeats 4000000 in
theorem claim_fields {cb : Bytes} {pc : PrepC} (h : prepClaim cb=.ok pc) :
    pc.hdr.own=pc.H.shardId ∧ pc.hdr.balanceBurnt=pc.H.prevBalanceBurnt := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; exact ⟨rfl,rfl⟩

theorem body_fields {pc : PrepC} {hint : Hint} {p : Prep} (h : prepBody pc hint=.ok p) :
    p.hdr.n=hint.n ∧ p.body=hint.body ∧ p.hdr.own=pc.hdr.own ∧
      p.hdr.balanceBurnt=pc.hdr.balanceBurnt := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first
    | (simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; exact ⟨rfl,rfl,rfl,rfl⟩)
    | (cases h)

theorem native_fields {cb wb : Bytes} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb (nativeHint k w m)=.ok p) (hk : walkD0 cb=.ok k)
    (hd : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w) :
    p.hdr.n=(appliedReceipts k w).length ∧
    p.body=u32 0++encodeReceipts m.result.outgoing ∧
    p.hdr.own=k.H.shardId ∧ p.hdr.balanceBurnt=m.result.tokensBurnt := by
  obtain ⟨pc,hpc,hbody⟩:=bind_ok hp
  obtain ⟨hn,hb,ho,ht⟩:=body_fields hbody
  obtain ⟨hown,hburnt⟩:=claim_fields hpc
  have hheader:=(prepClaim_native_context hpc hk hm).header
  obtain ⟨n,last,hnative,_,_,_,hh⟩:=checkD0_native_header hk hd hc
  have he:=MainExecutionV3.NativeValid.unique hm hnative
  subst n
  exact ⟨hn,hb,ho.trans (hown.trans (congrArg ChunkInner.shardId hheader)),
    ht.trans (hburnt.trans ((congrArg ChunkInner.prevBalanceBurnt hheader).trans hh.tokensBurnt))⟩

theorem count_byte (p : Prep) (overhead i : Nat) (hr : Public.RootsSized p) (hi : i<4) :
    (Public.preparedBytes p overhead).getD (PH_N+i) 0=(u32 p.hdr.n).getD i 0 := by
  rw [Public.prepared_header p overhead hr (by unfold PH_N;omega)]
  let preBytes := borshBytes prepTag++u32 p.hdr.K
  let suffix := u64 p.hdr.own++u32 p.hdr.ownIdx++u32 p.hdr.numShards++u64 p.hdr.height++u128 p.hdr.gasPrice++u64 p.hdr.gasLimit++p.hdr.prevStateRoot++p.hdr.postStateRoot++p.hdr.outcomeRoot++u128 p.hdr.balanceBurnt++u32 p.body.length++u32 overhead
  have he : Public.headerBytes p overhead=preBytes++u32 p.hdr.n++suffix := by
    simp only [Public.headerBytes,PrepHdr.encode,preBytes,suffix,List.append_assoc]
  have hl : preBytes.length=PH_N := by
    have hh := Public.oldHeader_length p hr
    obtain ⟨hpre,hpost,hout⟩ := hr
    simp only [preBytes,List.length_append,u32,u64,u128,leN_length,hpre,hpost,hout]
    simp only [List.length_append,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout] at hh
    unfold PH_N
    omega
  rw [he,←hl]
  exact Public.getD_middle preBytes _ suffix (by simpa [u32,u64,u128,leN_length] using hi)

theorem own_byte (p : Prep) (overhead i : Nat) (hr : Public.RootsSized p) (hi : i<8) :
    (Public.preparedBytes p overhead).getD (PH_OWN+i) 0=(u64 p.hdr.own).getD i 0 := by
  rw [Public.prepared_header p overhead hr (by unfold PH_OWN;omega)]
  let preBytes := borshBytes prepTag++u32 p.hdr.K++u32 p.hdr.n
  let suffix := u32 p.hdr.ownIdx++u32 p.hdr.numShards++u64 p.hdr.height++u128 p.hdr.gasPrice++u64 p.hdr.gasLimit++p.hdr.prevStateRoot++p.hdr.postStateRoot++p.hdr.outcomeRoot++u128 p.hdr.balanceBurnt++u32 p.body.length++u32 overhead
  have he : Public.headerBytes p overhead=preBytes++u64 p.hdr.own++suffix := by
    simp only [Public.headerBytes,PrepHdr.encode,preBytes,suffix,List.append_assoc]
  have hl : preBytes.length=PH_OWN := by
    have hh := Public.oldHeader_length p hr
    obtain ⟨hpre,hpost,hout⟩ := hr
    simp only [preBytes,List.length_append,u32,u64,u128,leN_length,hpre,hpost,hout]
    simp only [List.length_append,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout] at hh
    unfold PH_OWN
    omega
  rw [he,←hl]
  exact Public.getD_middle preBytes _ suffix (by simpa [u32,u64,u128,leN_length] using hi)

theorem burnt_byte (p : Prep) (overhead i : Nat) (hr : Public.RootsSized p) (hi : i<16) :
    (Public.preparedBytes p overhead).getD (PH_BURNT+i) 0=(u128 p.hdr.balanceBurnt).getD i 0 := by
  rw [Public.prepared_header p overhead hr (by unfold PH_BURNT;omega)]
  let preBytes := borshBytes prepTag++u32 p.hdr.K++u32 p.hdr.n++u64 p.hdr.own++u32 p.hdr.ownIdx++u32 p.hdr.numShards++u64 p.hdr.height++u128 p.hdr.gasPrice++u64 p.hdr.gasLimit++p.hdr.prevStateRoot++p.hdr.postStateRoot++p.hdr.outcomeRoot
  let suffix := u32 p.body.length++u32 overhead
  have he : Public.headerBytes p overhead=preBytes++u128 p.hdr.balanceBurnt++suffix := by
    simp only [Public.headerBytes,PrepHdr.encode,preBytes,suffix,List.append_assoc]
  have hl : preBytes.length=PH_BURNT := by
    have hh := Public.oldHeader_length p hr
    obtain ⟨hpre,hpost,hout⟩ := hr
    simp only [preBytes,List.length_append,u32,u64,u128,leN_length,hpre,hpost,hout]
    simp only [List.length_append,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout] at hh
    unfold PH_BURNT
    omega
  rw [he,←hl]
  exact Public.getD_middle preBytes _ suffix (by simpa [u32,u64,u128,leN_length] using hi)

theorem body_byte (p : Prep) (overhead i : Nat) (hr : Public.RootsSized p) (hi : i<4) :
    (Public.preparedBytes p overhead).getD (PH_BLEN+i) 0=(u32 p.body.length).getD i 0 := by
  rw [Public.prepared_header p overhead hr (by unfold PH_BLEN;omega)]
  let preBytes := borshBytes prepTag++u32 p.hdr.K++u32 p.hdr.n++u64 p.hdr.own++u32 p.hdr.ownIdx++u32 p.hdr.numShards++u64 p.hdr.height++u128 p.hdr.gasPrice++u64 p.hdr.gasLimit++p.hdr.prevStateRoot++p.hdr.postStateRoot++p.hdr.outcomeRoot++u128 p.hdr.balanceBurnt
  let suffix := u32 overhead
  have he : Public.headerBytes p overhead=preBytes++u32 p.body.length++suffix := by
    simp only [Public.headerBytes,PrepHdr.encode,preBytes,suffix,List.append_assoc]
  have hl : preBytes.length=PH_BLEN := by
    have hh := Public.oldHeader_length p hr
    obtain ⟨hpre,hpost,hout⟩ := hr
    simp only [preBytes,List.length_append,u32,u64,u128,leN_length,hpre,hpost,hout]
    simp only [List.length_append,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout] at hh
    unfold PH_BLEN
    omega
  rw [he,←hl]
  exact Public.getD_middle preBytes _ suffix (by simpa [u32,u64,u128,leN_length] using hi)

end ZkFormal.NearV3.Candidates.ReceiptPreparedFields
