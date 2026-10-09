import ZkFormal.NearV3.Candidates.ProcPriorCodecSideKind
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideRecord
open ZkFormal.Air ZkFormal.Algebra Lean.Grind ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ZkFormal.NearV3.Sched.Gen
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange

def offCols : List Nat := [kR,e7,fS,fR,fA,rend,rs,a0g,u0g,fwg,cg]

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz : ∀c∈offCols,cur c=0)
    (hd : cur dgg*(1-cur kZ)=0 ∧ cur dgg*cur sj=0) :
    ∀e∈cRec,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  have hR:=hz kR (by simp [offCols])
  have h7:=hz e7 (by simp [offCols])
  have hS:=hz fS (by simp [offCols])
  have hFR:=hz fR (by simp [offCols])
  have hFA:=hz fA (by simp [offCols])
  have hEnd:=hz rend (by simp [offCols])
  have hRs:=hz rs (by simp [offCols])
  have hA0:=hz a0g (by simp [offCols])
  have hU0:=hz u0g (by simp [offCols])
  have hFw:=hz fwg (by simp [offCols])
  have hCg:=hz cg (by simp [offCols])
  simp [cRec,List.forall_mem_cons,Expr.evalWith,ProcPriorCells.env,c,n,k,sub,smul,mul3,notE,
    hR,h7,hS,hFR,hFA,hEnd,hRs,hA0,hU0,hFw,hCg,
    Semiring.zero_mul,Semiring.mul_zero,AddCommMonoid.add_zero,
    AddCommGroup.neg_zero]
  change cur dgg*(1 + -cur kZ)=0 ∧ cur dgg*cur sj=0
  grind
theorem off_miss (c v : Nat) (values : Nat→Nat) (hc : c∈offCols) :
    lookup ((List.range 32).map fun i=>(reg i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v := by
  constructor
  · apply lookup_miss
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh : ∀i:Fin 32,∀c∈offCols,reg i.val≠c := by decide +kernel
    exact hh ⟨i,List.mem_range.mp hi⟩ c hc
  · have hh : ∀c∈offCols,(c<16∨24≤c) ∧ (c<79∨87≤c) := by decide +kernel
    exact ⟨miss_block 16 8 c v values (hh c hc).1,miss_block 79 8 c v values (hh c hc).2⟩

theorem header_off (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (params hdr : List Nat) (p c : Nat) (hc : c∈offCols) :
    (headerRow (instanceCells I R present vid) params hdr present p)[c]! =0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈offCols,c<Codec.width) c hc
  unfold headerRow
  rw [SchedSetAll.cell _ _ c hw,append,(off_miss c _ _ hc).2.2,
    append,(off_miss c _ _ hc).2.1,append,(off_miss c _ _ hc).1]
  simp only [offCols,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [instanceCells,ProcPriorCodecHeaderReads.headerScalars,lookup,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,
    kR,e7,fS,fR,fA,rend,rs,a0g,u0g,fwg,cg]
theorem hash_off (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (digest hpre : List Nat) (base0 j c : Nat) (hc : c∈offCols) :
    (hashRow (instanceCells I R present vid) digest hpre present base0 j)[c]! =0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈offCols,c<Codec.width) c hc
  unfold hashRow
  rw [SchedSetAll.cell _ _ c hw,append,(off_miss c _ _ hc).2.2,
    append,(off_miss c _ _ hc).2.1,append,(off_miss c _ _ hc).1]
  simp only [offCols,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [instanceCells,ProcPriorCodecHashReads.hashScalars,lookup,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kH,kZ,kF,pos,bpost,bpre,vbg,sj,bsha,isj,esj,dgg,
    kR,e7,fS,fR,fA,rend,rs,a0g,u0g,fwg,cg]

theorem ash_off (I : Input) (R : Run) (present : Bool) (vid base0 j c : Nat) (hc : c∈offCols) :
    (ashRow (instanceCells I R present vid) I base0 j)[c]! =0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈offCols,c<Codec.width) c hc
  unfold ashRow
  rw [SchedSetAll.cell _ _ c hw]
  simp only [offCols,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [instanceCells,lookup,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kA,pos,sj,bsha,pm0,pm1,isj,esj,
    kR,e7,fS,fR,fA,rend,rs,a0g,u0g,fwg,cg]
theorem header_record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈cRec,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((headerRow (instanceCells I R present vid) params hdr present p)[c]!))
      nxt first last trans)=0 := by
  apply inactive
  · intro c hc; rw [header_off I R present vid params hdr p c hc]; rfl
  · obtain ⟨_,_,_,_,_,hD⟩ := ProcPriorCodecSideMultiplicity.header_flags I R present vid params hdr p
    rw [hD]
    change (0:Fp)*_=0 ∧ (0:Fp)*_=0
    simp [Semiring.zero_mul]

theorem hash_record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈cRec,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vid) digest hpre present base0 j)[c]!))
      nxt first last trans)=0 := by
  apply inactive
  · intro c hc; rw [hash_off I R present vid digest hpre base0 j c hc]; rfl
  · obtain ⟨_,_,hZ,_,_,hD⟩ := ProcPriorCodecSideMultiplicity.hash_flags I R present vid digest hpre base0 j
    have hJ := (ProcPriorCodecSideTrailer.hash_cells I R present vid digest hpre base0 j).2.2.2.1
    rw [hZ,hD,hJ]
    by_cases hj : j=0
    · subst j; decide +kernel
    · simp only [if_neg hj]
      change (0:Fp)*_=0 ∧ (0:Fp)*_=0
      simp [Semiring.zero_mul]

theorem ash_record (I : Input) (R : Run) (present : Bool) (vid base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈cRec,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vid) I base0 j)[c]!))
      nxt first last trans)=0 := by
  apply inactive
  · intro c hc; rw [ash_off I R present vid base0 j c hc]; rfl
  · obtain ⟨_,_,_,_,_,hD⟩ := ProcPriorCodecSideMultiplicity.ash_flags I R present vid base0 j
    rw [hD]
    change (0:Fp)*_=0 ∧ (0:Fp)*_=0
    simp [Semiring.zero_mul]
end ZkFormal.NearV3.Candidates.ProcPriorCodecSideRecord
