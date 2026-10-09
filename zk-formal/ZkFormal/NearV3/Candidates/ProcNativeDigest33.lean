import ZkFormal.NearV3.Assembly.SchedulerWholeDigestConservation
namespace ZkFormal.NearV3.Candidates.ProcNativeDigest33
open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render ZkFormal.NearV3.Render.UpsGen
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

/-! Preparation allows up to33 scheduler instances. Their actual Codec rows
still fit log22. These are physical DIGEST inventory theorems, not concatenated
Codec local-validity or full-certificate claims. -/
theorem indexed_digests (bs : List NativeBlock) (start : Nat)
    (hv:∀b∈bs,b.Valid) (ht:∀b∈bs,b.run.tau<ZkFormal.Algebra.P)
    (ho:∀i b,bs[i]?=some b→b.run.tau=start+i) :
    (bs.flatMap fun b=>b.output.rows.toList.flatMap rowDigests)=
      (Sha.Gen.expectedDigests (schedulerSanityJobs start (bs.map NativeBlock.witness))).map Msg.toFp := by
  induction bs generalizing start with
  | nil=>rfl
  | cons b bs ih=>
    have hh:=native_block_digests b (hv b (by simp)) (ht b (by simp))
    have hτ:=ho 0 b (by rfl)
    simp only [Nat.add_zero] at hτ
    have htail:∀i x,bs[i]?=some x→x.run.tau=(start+1)+i:=by
      intro i x hx
      have he:=ho (i+1) x (by simpa using hx)
      omega
    have hhTail:=ih (start+1) (fun x hx=>hv x (by simp [hx]))
      (fun x hx=>ht x (by simp [hx])) htail
    rw [List.flatMap_cons,hh,hhTail,hτ]
    simp only [List.map_cons,schedulerSanityJobs,Sha.Gen.expectedDigests,
      List.cons_append,List.nil_append]
    rfl

/-- Exact physical corrected Codec DIGEST conservation for the generated
concatenation. Block placement, all silent rows and padding are derived here. -/
theorem codec_count (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64)
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount Codec.interactions (SchedHeight.trace (nativeBlockRows bs) codecPad)
      t pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (schedulerSanityJobs 0 (bs.map NativeBlock.witness))).map Msg.toFp).count msg := by
  have hsize:=native_block_rows_bound bs hb
  have hcap:(nativeBlockRows bs).size≤2^22:=by omega
  rw [trace_digest_count _ hcap]
  unfold nativeBlockRows
  rw [List.toList_toArray,List.flatMap_assoc]
  have ht:∀b∈bs,b.run.tau<ZkFormal.Algebra.P:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    have hir:=(List.getElem?_eq_some_iff.mp hi).1
    rw [ho i b hi]
    have := UpsRows.P_gt
    omega
  rw [indexed_digests bs 0 (fun b hm=>(hb b hm).1) ht (by simpa using ho)]

/-- Complete scheduler DIGEST conservation between the native SHA jobs and
both physical consumers: compact UPS plus the corrected generated Codec.
The exact same operational witness sequence determines both job families. -/
theorem whole_count (bs : List NativeBlock) (insts : List UpsInst)
    (hlen:bs.length≤33) (hsize:insts.length=bs.length)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧ b.witness.pre.wf=true)
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hi:∀i u I,(bs.map NativeBlock.witness)[i]?=some u→insts[i]?=some I→
      AllocatedNativeInstance (bs.map NativeBlock.witness) i u I ∧
        NativeShaFamily u I ∧ NativeEncodedInstance u I)
    (hcap:UpsRelay.compactR insts≤2^22) (tu tc : Nat) (pub msg : List Fp) :
    tableBusCount UpsRelay.compactTable.interactions (CompactHeight.trace insts) tu pub B_DIGEST false msg+
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) Sched.Gen.codecPad) tc pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (schedulerShaJobs 0 (bs.map NativeBlock.witness)++
        schedulerSanityJobs 0 (bs.map NativeBlock.witness))).map Msg.toFp).count msg := by
  have hv:∀u∈bs.map NativeBlock.witness,u.Valid ∧ u.pre.wf=true:=by
    intro u hu
    obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hu
    exact ⟨(hb b hb').1.1,(hb b hb').2.2⟩
  have hup:=scheduler_compact_digest_count (bs.map NativeBlock.witness) insts
    (by simpa using hsize) hv hi hcap tu pub msg
  have hcodec:=codec_count bs hlen (fun b h=>⟨(hb b h).1,(hb b h).2.1⟩) ho tc pub msg
  rw [repaired_digest_count]
  rw [hup,hcodec]
  simp only [Sha.Gen.expectedDigests,List.filter_append,List.map_append,List.count_append]

end ZkFormal.NearV3.Candidates.ProcNativeDigest33
