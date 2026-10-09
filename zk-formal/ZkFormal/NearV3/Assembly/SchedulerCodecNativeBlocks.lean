import ZkFormal.NearV3.Assembly.SchedulerCodecTraceDigests

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Concrete generator inputs and output for one operational scheduler call. -/
structure NativeBlock where
  witness : SchedulerUpsertWitness
  pub : Scheduler.SchedPub
  prior : Option Bytes
  old : Bandwidth.State
  run : Run
  vid : Nat
  grants : Array Nat
  forwarded : List (Nat×Nat)
  output : CodecOut

def NativeBlock.Valid (b : NativeBlock) : Prop :=
  b.witness.Valid ∧
  readKey b.witness.pre keyBwState "bandwidth scheduler state"=.ok b.prior ∧
  schedPub b.witness.ctx=some b.pub ∧
  (match b.prior with | none=>some Bandwidth.State.initial | some raw=>Bandwidth.State.decode raw)=some b.old ∧
  ProcPriorCodecGen.codecRows (ProcPreparedSequence.input b.pub b.old) b.run b.prior.isSome b.vid
    b.grants b.forwarded=.ok b.output

/-- A successful concrete block supplies exactly its same native sanity job. -/
theorem native_block_digests (b : NativeBlock) (hb:b.Valid) (ht:b.run.tau<ZkFormal.Algebra.P) :
    b.output.rows.toList.flatMap rowDigests=
      (Sha.Gen.expectedDigests [schedulerSanityJob b.run.tau b.witness]).map Msg.toFp := by
  obtain ⟨hv,hr,hp,hd,hgen⟩:=hb
  rw [generated_digests _ _ _ _ _ _ _ ht hgen]
  have hjob:=prepared_sanity_job (old:=b.old) hv hr hp (by split <;> simp_all) b.run.tau
  rw [hjob]
  rfl

/-- The exact corrected generator row count closes the common-log22 bound,
using only ordinary64-shard and32-instance bounds. -/
theorem native_block_length (b : NativeBlock) (hb:b.Valid) (hn:b.run.n≤64) :
    b.output.rows.size≤98373 := by
  rw [generated_length _ _ _ _ _ _ _ hb.2.2.2.2]
  have hh:=Nat.mul_le_mul hn hn
  omega

def nativeBlockRows (bs : List NativeBlock) : Array (Array Nat) :=
  (bs.flatMap fun b=>b.output.rows.toList).toArray

theorem native_block_rows_bound (bs : List NativeBlock)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64) : (nativeBlockRows bs).size≤98373*bs.length := by
  induction bs with
  | nil=>simp [nativeBlockRows]
  | cons b bs ih=>
    have hh:=native_block_length b (hb b (by simp)).1 (hb b (by simp)).2
    have ht:=ih (fun x hx=>hb x (by simp [hx]))
    simp only [nativeBlockRows,List.flatMap_cons,List.length_append,List.size_toArray,
      Array.length_toList,List.length_cons] at *
    omega

private theorem indexed_digests (bs : List NativeBlock) (start : Nat)
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
    simp only [List.map_cons,schedulerSanityJobs,Sha.Gen.expectedDigests,List.filter_cons_of_pos,
      List.filter_nil,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
    rfl

/-- Exact physical corrected Codec DIGEST conservation for the generated
concatenation. Block placement, all silent rows and padding are derived here. -/
theorem native_codec_digest_count (bs : List NativeBlock) (hlen:bs.length≤32)
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

end ZkFormal.NearV3.Assembly.CodecDigest
