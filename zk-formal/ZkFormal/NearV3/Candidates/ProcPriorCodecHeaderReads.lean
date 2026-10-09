import ZkFormal.NearV3.Candidates.ProcPriorCodecRegisterMiss
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderReads
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments SchedSetAll ProcPriorCodecRegisterMiss

def headerScalars (hdr : List Nat) (present : Bool) (p : Nat) : List (Nat×Nat) :=
  [(kH,1),(kF,if p=0 then 1 else 0),(pos,p),(bpost,hdr[p]!),
   (bpre,if present then hdr[p]! else 0),(vbg,b2n present),
   (ihp,finv (fsub p 4)),(ehp,if p=4 then 1 else 0)]

theorem projection (inst : List (Nat×Nat)) (params hdr : List Nat) (present : Bool)
    (p c : Nat) (hc:c∈untouched) :
    (headerRow inst params hdr present p)[c]! = lookup (inst++headerScalars hdr present p) c 0 := by
  have hw: c<Codec.width := by
    have h : ∀c∈untouched,c<Codec.width := by decide +kernel
    exact h c hc
  unfold headerRow
  rw [SchedSetAll.cell _ _ c hw,append,prior_bits _ _ _ hc,
    append,post_bits _ _ _ hc,append,registers _ _ _ hc]
  rfl

theorem post_byte (inst : List (Nat×Nat)) (params hdr : List Nat) (present : Bool) (p : Nat) :
    (headerRow inst params hdr present p)[bpost]! = hdr[p]! := by
  rw [projection _ _ _ _ _ _ (by decide +kernel),append]
  simp [headerScalars,lookup,kH,kF,pos,bpost,bpre,vbg,ihp,ehp]

theorem header_end (inst : List (Nat×Nat)) (params hdr : List Nat) (present : Bool) (p : Nat) :
    (headerRow inst params hdr present p)[ehp]! = if p=4 then 1 else 0 := by
  rw [projection _ _ _ _ _ _ (by decide +kernel),append]
  simp [headerScalars,lookup,kH,kF,pos,bpost,bpre,vbg,ihp,ehp]

theorem record_flags_zero (inst : List (Nat×Nat)) (params hdr : List Nat) (present : Bool)
    (p c : Nat) (hc:c∈[kR,kZ,kA,rs,rend,fS,fR,fA])
    (hi:∀a∈inst,a.1≠c) :
    (headerRow inst params hdr present p)[c]! = 0 := by
  have hu:c∈untouched := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rw [projection _ _ _ _ _ _ hu,append,lookup_miss _ _ _ hi]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [headerScalars,lookup,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,kR,kZ,kA,rs,rend,fS,fR,fA]

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderReads
