import ZkFormal.NearV3.Assembly.SchedulerCodecHashTraffic

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Candidates.SchedSetAll Candidates.SchedSetAllRange
open Sched Sched.Gen Sched.Codec Candidates.ProcPriorCodecAssignments
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private theorem prior_miss (v : Nat) (values : Nat→Nat) :
    lookup ((List.range 8).map (fun i=>(prbit i,values i))) dgg v=v :=
  miss_block 79 8 dgg v values (by decide +kernel)
private theorem post_miss (v : Nat) (values : Nat→Nat) :
    lookup ((List.range 8).map (fun i=>(pbit i,values i))) dgg v=v :=
  miss_block 16 8 dgg v values (by decide +kernel)
private theorem regs_miss (v : Nat) (values : Nat→Nat) :
    lookup ((List.range 32).map (fun i=>(reg i,values i))) dgg v=v := by
  apply lookup_miss
  intro p hp
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
  have h:∀i:Fin 32,reg i.val≠dgg:=by decide +kernel
  exact h ⟨i,List.mem_range.mp hi⟩

private theorem instance_miss (I : Input) (R : Run) (present : Bool) (vidV : Nat) :
    lookup (ProcPriorCodecNativeHash.instanceCells I R present vidV) dgg 0=0 := by
  simp [ProcPriorCodecNativeHash.instanceCells,lookup,dgg,act,tau,pres,vid,nn,NN,base,fair,itz,zt]

/-- No header byte row contributes a DIGEST demand. -/
theorem header_digest_gate (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) :
    (headerRow (ProcPriorCodecNativeHash.instanceCells I R present vidV) params hdr present p)[dgg]! =0 := by
  unfold headerRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append,prior_miss,append,post_miss,
    append,regs_miss,append,instance_miss]
  simp [lookup,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,dgg]

/-- No action-hash input byte row contributes a DIGEST demand. -/
theorem ash_digest_gate (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat) :
    (ashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV) I base0 j)[dgg]! =0 := by
  unfold ashRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append,instance_miss]
  simp [lookup,kA,pos,sj,bsha,pm0,pm1,isj,esj,dgg]

/-- The record helper preserves zero DIGEST gate when its actual extra
assignments do not write that column. -/
theorem record_digest_gate (I : Input) (R : Run) (present : Bool)
    (vidV n kk f gg p bpo bpr : Nat) (extra : List (Nat×Nat))
    (he : ∀a∈extra,a.1≠dgg) :
    (recordRow I present n kk f gg p bpo bpr
      (ProcPriorCodecNativeHash.instanceCells I R present vidV) extra)[dgg]! =0 := by
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append,lookup_miss _ _ _ he,append]
  have hm : ∀v,lookup (if f=0 then (List.range 8).map (fun i=>(prbit i,
      (bytesLE (I.ids.getD (kk/n) 0) 8).getD (gg+i) 0)) else []) dgg v=v := by
    intro v
    split
    · exact prior_miss v _
    · rfl
  rw [hm,append,post_miss,append,instance_miss]
  simp [lookup,kR,pos,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,g,ig7,e7,ikl,ekl,dgg]

/-- Zero actual digest gate excludes all DIGEST interactions on that row. -/
theorem zero_digest_row (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hz : tr.cell t r dgg=0) : Near.rowTraffic Codec.interactions tr t r pub B_DIGEST false=[] := by
  rw [codec_digest_row]
  have hm:(Codec.interactions[3]!).multNat tr t r pub=0:=by
    apply Codec.mult_zero (by rw [Codec.i3_def])
    simp only [Chacha.zev_c,Chacha.cur_cv,Chacha.cv,hz]
    rfl
  rw [hm,List.replicate_zero]

end ZkFormal.NearV3.Assembly.CodecDigest
