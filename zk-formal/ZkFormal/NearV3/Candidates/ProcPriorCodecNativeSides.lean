import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNativeSides
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash

theorem ash_zero (I : Input) (R : Run) (present : Bool) (vidV base0 j c : Nat)
    (hc:c∈[kR,rs,rend,fS,fA,ehp]) :
    (ashRow (instanceCells I R present vidV) I base0 j)[c]! = 0 := by
  have hw:c<Codec.width := by
    have h : ∀c∈[kR,rs,rend,fS,fA,ehp],c<Codec.width := by decide +kernel
    exact h c hc
  unfold ashRow
  rw [SchedSetAll.cell _ _ c hw,SchedSetAll.append,
    SchedSetAll.lookup_miss _ _ _ (instance_avoids I R present vidV c hc)]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [SchedSetAll.lookup,kA,pos,sj,bsha,pm0,pm1,isj,esj,kR,rs,rend,fS,fA,ehp]

theorem ash_additions (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 j)[c]!))
        nxt first last trans)=0 := by
  have hz : ∀c∈[kR,rs,rend,fS,fA,ehp],
      Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 j)[c]!)=0 := by
    intro c hc; rw [ash_zero I R present vidV base0 j c hc]; rfl
  exact ProcPriorCodecNonrecordPhase.inactive_header _ nxt first last trans
    (hz rs (by simp)) (hz kR (by simp)) (hz rend (by simp))
    (hz fA (by simp)) (hz fS (by simp)) (hz ehp (by simp))

/-- The only header-side adjacency premise is the actual first-record grid
initialization. Digest and ordinary header rows need no next-counter restriction. -/
theorem header_additions (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hend:p=4 → nxt srcC=0 ∧ nxt useC=0) :
    ∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat ((headerRow (instanceCells I R present vidV) params hdr present p)[c]!))
        nxt first last trans)=0 := by
  have hz : ∀c∈[kR,rs,rend,fS,fA],
      Fp.ofNat ((headerRow (instanceCells I R present vidV) params hdr present p)[c]!)=0 := by
    intro c hc
    have h1:c∈[kR,kZ,kA,rs,rend,fS,fR,fA] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc ⊢; grind
    have h2:c∈[kR,rs,rend,fS,fA,ehp] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc ⊢; grind
    rw [ProcPriorCodecHeaderReads.record_flags_zero _ _ _ _ _ c h1
      (instance_avoids I R present vidV c h2)]
    rfl
  refine ProcPriorCodecNonrecordPhase.additions
    (fun c=>Fp.ofNat ((headerRow (instanceCells I R present vidV) params hdr present p)[c]!))
    nxt first last trans (hz rs (by simp)) (hz kR (by simp)) (hz rend (by simp))
    (hz fA (by simp)) (hz fS (by simp)) ?_
  by_cases he:p=4
  · exact Or.inr (hend he)
  · left
    rw [ProcPriorCodecHeaderReads.header_end,if_neg he]
    rfl

end ZkFormal.NearV3.Candidates.ProcPriorCodecNativeSides
