import ZkFormal.NearV3.Candidates.ProcPriorCodecSideMultiplicity
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecSideMultiplicity SchedSetAll SchedSetAllRange

def scalarBits : List Nat :=
  [act,kH,kR,kZ,kA,kF,pres,fS,fR,fA,e7,e2,ekl,ehp,esj,zt,cbit,cg,rend,vbg,fwg,dgg,rs]
def retainedBits : List Nat := scalarBits++(List.range 8).map pbit

theorem scalar_miss (c v : Nat) (values : Nat→Nat) (hc:c∈scalarBits) :
    lookup ((List.range 32).map fun i=>(reg i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v := by
  constructor
  · apply lookup_miss
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh : ∀i:Fin 32,∀c∈scalarBits,reg i.val≠c := by decide +kernel
    exact hh ⟨i,List.mem_range.mp hi⟩ c hc
  · have hh : ∀c∈scalarBits,(c<16∨24≤c) ∧ (c<79∨87≤c) := by decide +kernel
    exact ⟨miss_block 16 8 c v values (hh c hc).1,miss_block 79 8 c v values (hh c hc).2⟩

theorem header_scalar (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p c : Nat) (hc:c∈scalarBits) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[c]! =
      lookup (instanceCells I R present vidV++ProcPriorCodecHeaderReads.headerScalars hdr present p) c 0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈scalarBits,c<Codec.width) c hc
  unfold headerRow
  rw [SchedSetAll.cell _ _ c hw,append,(scalar_miss c _ _ hc).2.2,
    append,(scalar_miss c _ _ hc).2.1,append,(scalar_miss c _ _ hc).1]
  rfl

theorem hash_scalar (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j c : Nat) (hc:c∈scalarBits) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! =
      lookup (instanceCells I R present vidV++ProcPriorCodecHashReads.hashScalars digest hpre present base0 j) c 0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈scalarBits,c<Codec.width) c hc
  unfold hashRow
  rw [SchedSetAll.cell _ _ c hw,append,(scalar_miss c _ _ hc).2.2,
    append,(scalar_miss c _ _ hc).2.1,append,(scalar_miss c _ _ hc).1]
  rfl

theorem native_bit (x i : Nat) : Gen.bit x i=0 ∨ Gen.bit x i=1 := by
  have h : x/2^i%2<2 := Nat.mod_lt _ (by decide)
  unfold Gen.bit
  omega

theorem header_post_bit (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p i : Nat) (hi:i<8) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[pbit i]! = Gen.bit hdr[p]! i := by
  have hqb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun j=>(prbit j,values j)) (pbit i) v=v :=
    miss_block 79 8 (pbit i) v values (by left; unfold pbit; omega)
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun j=>(pbit j,values j)) (pbit i) v=values i := by
    have hh := lookup_block 16 8 values (pbit i) v
    simpa [SchedSetAllRange.block,pbit,show 16+i<24 by omega] using hh
  unfold headerRow
  rw [SchedSetAll.cell _ _ _ (by unfold pbit Codec.width; omega),append,hqb,append,hpb]

theorem hash_post_bit (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j i : Nat) (hi:i<8) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[pbit i]! = Gen.bit digest[j]! i := by
  have hqb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun k=>(prbit k,values k)) (pbit i) v=v :=
    miss_block 79 8 (pbit i) v values (by left; unfold pbit; omega)
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun k=>(pbit k,values k)) (pbit i) v=values i := by
    have hh := lookup_block 16 8 values (pbit i) v
    simpa [SchedSetAllRange.block,pbit,show 16+i<24 by omega] using hh
  unfold hashRow
  rw [SchedSetAll.cell _ _ _ (by unfold pbit Codec.width; omega),append,hqb,append,hpb]


theorem header_scalar_bool (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p c : Nat) (hc:c∈scalarBits) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[c]! = 0 ∨ (headerRow (instanceCells I R present vidV) params hdr present p)[c]! = 1 := by
  rw [header_scalar _ _ _ _ _ _ _ _ hc]
  simp only [scalarBits,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases present <;> simp [instanceCells,ProcPriorCodecHeaderReads.headerScalars,lookup,b2n,
    act,kH,kR,kZ,kA,kF,pres,fS,fR,fA,e7,e2,ekl,ehp,esj,zt,cbit,cg,rend,vbg,fwg,dgg,rs,
    tau,vid,nn,NN,base,fair,itz,kH,kF,pos,bpost,bpre,vbg,ihp,ehp]
  all_goals first | omega | (split <;> omega)

theorem hash_scalar_bool (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j c : Nat) (hc:c∈scalarBits) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! = 0 ∨ (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! = 1 := by
  rw [hash_scalar _ _ _ _ _ _ _ _ _ hc]
  simp only [scalarBits,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases present <;> simp [instanceCells,ProcPriorCodecHashReads.hashScalars,lookup,b2n,
    act,kH,kR,kZ,kA,kF,pres,fS,fR,fA,e7,e2,ekl,ehp,esj,zt,cbit,cg,rend,vbg,fwg,dgg,rs,
    tau,vid,nn,NN,base,fair,itz,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj]
  all_goals first | omega | (split <;> omega)

theorem ash_bool (I : Input) (R : Run) (present : Bool) (vidV base0 j c : Nat)
    (hc:c∈retainedBits) :
    (ashRow (instanceCells I R present vidV) I base0 j)[c]! = 0 ∨
      (ashRow (instanceCells I R present vidV) I base0 j)[c]! = 1 := by
  rcases List.mem_append.mp hc with hc|hc
  · have hw : c<Codec.width := (by decide +kernel : ∀c∈scalarBits,c<Codec.width) c hc
    unfold ashRow
    rw [SchedSetAll.cell _ _ _ hw]
    simp only [scalarBits,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases present <;> simp [instanceCells,lookup,b2n,
      act,kH,kR,kZ,kA,kF,pres,fS,fR,fA,e7,e2,ekl,ehp,esj,zt,cbit,cg,rend,vbg,fwg,dgg,rs,
      tau,vid,nn,NN,base,fair,itz,pos,sj,bsha,pm0,pm1,isj]
    all_goals first | omega | (split <;> omega)
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi' := List.mem_range.mp hi
    unfold ashRow
    rw [SchedSetAll.cell _ _ _ (by unfold pbit Codec.width; omega)]
    left
    have hh : ∀i:Fin 8,∀c∈[act,tau,pres,vid,nn,NN,base,fair,itz,zt,kA,pos,sj,bsha,pm0,pm1,isj,esj],c≠pbit i.val := by decide +kernel
    apply lookup_miss
    intro p hp
    have hm : p.1∈[act,tau,pres,vid,nn,NN,base,fair,itz,zt,kA,pos,sj,bsha,pm0,pm1,isj,esj] := by
      have hm:=List.mem_map_of_mem (f:=Prod.fst) hp
      simpa [instanceCells] using hm
    exact hh ⟨i,hi'⟩ p.1 hm

theorem header_bool (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p c : Nat) (hc:c∈retainedBits) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[c]! = 0 ∨
      (headerRow (instanceCells I R present vidV) params hdr present p)[c]! = 1 := by
  rcases List.mem_append.mp hc with hc|hc
  · exact header_scalar_bool I R present vidV params hdr p c hc
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    rw [header_post_bit _ _ _ _ _ _ _ _ (List.mem_range.mp hi)]
    exact native_bit _ _

theorem hash_bool (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j c : Nat) (hc:c∈retainedBits) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! = 0 ∨
      (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! = 1 := by
  rcases List.mem_append.mp hc with hc|hc
  · exact hash_scalar_bool I R present vidV digest hpre base0 j c hc
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    rw [hash_post_bit _ _ _ _ _ _ _ _ _ (List.mem_range.mp hi)]
    exact native_bit _ _

def booleanGroup : List Expr :=
  ((boolCols.map ZkFormal.Chacha.Table.boolC)++
    recBoolCols.map (fun c=>Expr.mul (ZkFormal.Chacha.Table.E.c kR) (ZkFormal.Chacha.Table.boolC c))).filter
      (fun e=>!ProcPriorCodecActual.retiredKind.contains e)

theorem boolean_group_eq : booleanGroup=retainedBits.map ZkFormal.Chacha.Table.boolC++
    recBoolCols.map (fun c=>Expr.mul (ZkFormal.Chacha.Table.E.c kR) (ZkFormal.Chacha.Table.boolC c)) := by
  decide +kernel

theorem boolean_group (row : Array Nat) (hb : ∀c∈retainedBits,row[c]! = 0 ∨ row[c]! = 1)
    (hr : row[kR]! = 0) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈booleanGroup,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat row[c]!) nxt first last trans)=0 := by
  rw [boolean_group_eq]
  simp only [List.forall_mem_append,List.forall_mem_map]
  constructor
  · intro c hc
    rcases hb c hc with hx|hx
    all_goals simp only [ZkFormal.Chacha.Table.boolC,ZkFormal.Chacha.Table.E.sub,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
      ite_false,Bool.false_eq_true,hx]
    all_goals simp only [←Fp.ofNat_def]
    all_goals grind
  · intro c hc
    simp only [ZkFormal.Chacha.Table.E.c,Expr.evalWith,ProcPriorCells.env,
      ite_false,Bool.false_eq_true,hr]
    simp only [←Fp.ofNat_def]
    grind

theorem header_boolean_group (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈booleanGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((headerRow (instanceCells I R present vidV) params hdr present p)[c]!))
      nxt first last trans)=0 :=
  boolean_group _ (fun c hc=>header_bool I R present vidV params hdr p c hc)
    ((header_flags I R present vidV params hdr p).1 kR (by simp)) nxt first last trans

theorem hash_boolean_group (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈booleanGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!))
      nxt first last trans)=0 :=
  boolean_group _ (fun c hc=>hash_bool I R present vidV digest hpre base0 j c hc)
    ((hash_flags I R present vidV digest hpre base0 j).1 kR (by simp)) nxt first last trans

theorem ash_boolean_group (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈booleanGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 j)[c]!))
      nxt first last trans)=0 :=
  boolean_group _ (fun c hc=>ash_bool I R present vidV base0 j c hc)
    ((ash_flags I R present vidV base0 j).1 kR (by simp)) nxt first last trans
end ZkFormal.NearV3.Candidates.ProcPriorCodecSideKind
