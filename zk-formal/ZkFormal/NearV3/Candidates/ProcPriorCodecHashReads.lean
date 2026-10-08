import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderReads
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHashReads
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments SchedSetAll ProcPriorCodecRegisterMiss

def hashScalars (digest hpre : List Nat) (present : Bool) (base0 j : Nat) : List (Nat×Nat) :=
  [(kZ,1),(dgg,if j=0 then 1 else 0),(pos,base0+j),(sj,j),(bpost,digest[j]!),
   (bpre,if present then hpre[j]! else 0),(bsha,if present then hpre[j]! else 0),
   (vbg,b2n present),(isj,finv (fsub j 31)),(esj,if j=31 then 1 else 0)]

theorem projection (inst : List (Nat×Nat)) (digest hpre : List Nat) (present : Bool)
    (base0 j c : Nat) (hc:c∈untouched) :
    (hashRow inst digest hpre present base0 j)[c]! =
      lookup (inst++hashScalars digest hpre present base0 j) c 0 := by
  have hw: c<Codec.width := by
    have h : ∀c∈untouched,c<Codec.width := by decide +kernel
    exact h c hc
  unfold hashRow
  rw [SchedSetAll.cell _ _ c hw,append,prior_bits _ _ _ hc,
    append,post_bits _ _ _ hc,append,registers _ _ _ hc]
  rfl

theorem post_byte (inst : List (Nat×Nat)) (digest hpre : List Nat) (present : Bool) (base0 j : Nat) :
    (hashRow inst digest hpre present base0 j)[bpost]! = digest[j]! := by
  rw [projection _ _ _ _ _ _ _ (by decide +kernel),append]
  simp [hashScalars,lookup,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj]

theorem prior_byte (inst : List (Nat×Nat)) (digest hpre : List Nat) (present : Bool) (base0 j : Nat) :
    (hashRow inst digest hpre present base0 j)[bpre]! = if present then hpre[j]! else 0 := by
  rw [projection _ _ _ _ _ _ _ (by decide +kernel),append]
  simp [hashScalars,lookup,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj]

theorem phase_flags_zero (inst : List (Nat×Nat)) (digest hpre : List Nat) (present : Bool)
    (base0 j c : Nat) (hc:c∈[kR,rs,rend,fS,fA,ehp])
    (hi:∀a∈inst,a.1≠c) :
    (hashRow inst digest hpre present base0 j)[c]! = 0 := by
  have hu:c∈untouched := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rw [projection _ _ _ _ _ _ _ hu,append,lookup_miss _ _ _ hi]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [hashScalars,lookup,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj,kR,rs,rend,fS,fA,ehp]

end ZkFormal.NearV3.Candidates.ProcPriorCodecHashReads
