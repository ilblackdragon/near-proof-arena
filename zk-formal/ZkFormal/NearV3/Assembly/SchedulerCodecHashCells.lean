import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Candidates.SchedSetAll Candidates.SchedSetAllRange
open Sched Sched.Gen Sched.Codec Candidates.ProcPriorCodecAssignments

private theorem lookup_stable (xs : List (Nat×Nat)) (c v : Nat)
    (he : ∀p∈xs,p.1=c→p.2=v) : lookup xs c v=v := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    change lookup xs c (if a.1=c then a.2 else v)=v
    have ha:=he a (by simp)
    have ht:=ih (fun p hp=>he p (by simp [hp]))
    by_cases hc:a.1=c
    · rw [if_pos hc,ha hc];exact ht
    · rw [if_neg hc];exact ht

private theorem lookup_same (xs : List (Nat×Nat)) (c v initial : Nat)
    (hm : (c,v)∈xs) (he : ∀p∈xs,p.1=c→p.2=v) : lookup xs c initial=v := by
  induction xs generalizing initial with
  | nil=>simp at hm
  | cons a xs ih=>
    change lookup xs c (if a.1=c then a.2 else initial)=v
    rcases List.mem_cons.mp hm with h|h
    · subst a
      simp only [ite_true]
      exact lookup_stable xs c v (fun p hp=>he p (by simp [hp]))
    · exact ih _ h (fun p hp=>he p (by simp [hp]))

private theorem reg_shape (i : Nat) (hi:i<32) :
    reg i<Codec.width ∧ (reg i<16∨24≤reg i) ∧ (reg i<79∨87≤reg i) := by
  have h : ∀i:Fin 32,reg i.val<Codec.width ∧ (reg i.val<16∨24≤reg i.val) ∧
      (reg i.val<79∨87≤reg i.val) := by decide +kernel
  exact h ⟨i,hi⟩

private theorem reg_injective {i j : Nat} (hi:i<32) (hj:j<32) (he:reg i=reg j) : i=j := by
  have h : ∀i j:Fin 32,reg i.val=reg j.val→i.val=j.val := by decide +kernel
  exact h ⟨i,hi⟩ ⟨j,hj⟩ he

private theorem prior_miss (c v x : Nat) (hc:c<79∨87≤c) :
    lookup ((List.range 8).map (fun i=>(prbit i,bit x i))) c v=v :=
  miss_block 79 8 c v (fun i=>bit x i) hc
private theorem post_miss (c v x : Nat) (hc:c<16∨24≤c) :
    lookup ((List.range 8).map (fun i=>(pbit i,bit x i))) c v=v :=
  miss_block 16 8 c v (fun i=>bit x i) hc

/-- Actual hash-row register bytes, independent of repaired Codec legality. -/
theorem hash_register (inst : List (Nat×Nat)) (digest hpre : List Nat)
    (present : Bool) (base0 j i : Nat) (hi:i<32) :
    (hashRow inst digest hpre present base0 j)[reg i]! =digest.getD (j+i) 0 := by
  have hs:=reg_shape i hi
  unfold hashRow
  rw [SchedSetAll.cell _ _ _ hs.1,append]
  rw [prior_miss _ _ _ hs.2.2,append,post_miss _ _ _ hs.2.1,append]
  apply lookup_same
  · exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  · intro p hp he
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hp
    have hki:=reg_injective (List.mem_range.mp hk) hi he
    simp only [hki]

/-- The sole generated digest gate is the first hash row. -/
theorem hash_digest_gate (inst : List (Nat×Nat)) (digest hpre : List Nat)
    (present : Bool) (base0 j : Nat) :
    (hashRow inst digest hpre present base0 j)[dgg]! =if j=0 then 1 else 0 := by
  unfold hashRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append]
  rw [prior_miss _ _ _ (by decide +kernel),append,
    post_miss _ _ _ (by decide +kernel),append]
  have hm : ∀p∈(List.range 32).map (fun i=>(reg i,digest.getD (j+i) 0)),p.1≠dgg := by
    intro p hp
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
    have h : ∀i:Fin 32,reg i.val≠dgg := by decide +kernel
    exact h ⟨i,List.mem_range.mp hi⟩
  rw [lookup_miss _ _ _ hm,append]
  simp [lookup,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj]

/-- The hash rows retain the actual global instance identifier. -/
theorem hash_tau (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    (hashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV)
      digest hpre present base0 j)[tau]! = R.tau := by
  rw [ProcPriorCodecHashReads.projection _ _ _ _ _ _ _ (by decide +kernel),append]
  simp [ProcPriorCodecHashReads.hashScalars,ProcPriorCodecNativeHash.instanceCells,
    lookup,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj,tau,act,pres,vid,nn,NN,base,fair,itz,zt]

end ZkFormal.NearV3.Assembly.CodecDigest
