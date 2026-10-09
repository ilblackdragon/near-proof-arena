import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeSides
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideTrailer
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange

def scalarColumns : List Nat := [kH,kR,kZ,kA,kF,fwg,sj,esj,bsha,pm0,pm1,act,vbg,dgg,fS,fR,fA,rend,cg,rs,ehp]

theorem scalar_registers (c v : Nat) (values : Nat→Nat) (hc:c∈scalarColumns) :
    lookup ((List.range 32).map fun i=>(reg i,values i)) c v=v := by
  apply lookup_miss
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have hh : ∀i:Fin 32,∀c∈scalarColumns,reg i.val≠c := by decide +kernel
  exact hh ⟨i,List.mem_range.mp hi⟩ c hc

theorem scalar_bits (c v : Nat) (values : Nat→Nat) (hc:c∈scalarColumns) :
    lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v := by
  have hh : ∀c∈scalarColumns,(c<16∨24≤c) ∧ (c<79∨87≤c) := by decide +kernel
  exact ⟨miss_block 16 8 c v values (hh c hc).1,miss_block 79 8 c v values (hh c hc).2⟩

theorem hash_scalar (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j c : Nat) (hc:c∈scalarColumns) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! =
      lookup (instanceCells I R present vidV++ProcPriorCodecHashReads.hashScalars digest hpre present base0 j) c 0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈scalarColumns,c<Codec.width) c hc
  unfold hashRow
  rw [SchedSetAll.cell _ _ c hw,append,(scalar_bits c _ _ hc).2,
    append,(scalar_bits c _ _ hc).1,append,scalar_registers c _ _ hc]
  rfl

theorem header_scalar (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p c : Nat) (hc:c∈scalarColumns) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[c]! =
      lookup (instanceCells I R present vidV++ProcPriorCodecHeaderReads.headerScalars hdr present p) c 0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈scalarColumns,c<Codec.width) c hc
  unfold headerRow
  rw [SchedSetAll.cell _ _ c hw,append,(scalar_bits c _ _ hc).2,
    append,(scalar_bits c _ _ hc).1,append,scalar_registers c _ _ hc]
  rfl

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz : cur kZ=0) (ha : cur kA=0) (hf : cur fwg=0) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [cTrl,List.forall_mem_append,List.forall_mem_cons,
    List.forall_mem_map]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,hz,ha,hf,mul3,notE,ZkFormal.Chacha.Table.E.k]
  grind

theorem header_trailer (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((headerRow (instanceCells I R present vidV) params hdr present p)[c]!))
      nxt first last trans)=0 := by
  apply inactive
  all_goals rw [header_scalar _ _ _ _ _ _ _ _ (by decide +kernel)]
  all_goals simp [instanceCells,ProcPriorCodecHeaderReads.headerScalars,lookup,
    act,tau,pres,vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,kZ,kA,fwg]
  all_goals rfl

theorem ash_cells (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat) :
    let row:=ashRow (instanceCells I R present vidV) I base0 j
    row[kZ]! = 0 ∧ row[kA]! = 1 ∧ row[fwg]! = 0 ∧ row[sj]! = 32+j ∧
      row[esj]! = (if j=31 then 1 else 0) ∧ row[pm0]! = j ∧ row[pm1]! = row[bsha]! ∧
      row[fb 0]! = 0 ∧ row[fb 1]! = 0 ∧ row[fb 2]! = 0 := by
  dsimp only
  unfold ashRow
  repeat rw [SchedSetAll.cell _ _ _ (by decide +kernel)]
  simp [instanceCells,lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,
    kZ,kA,fwg,sj,esj,pm0,pm1,bsha,fb,pos,isj]

/-- All retained trailer constraints hold on native all-shards-hash rows.
Only the two actual successor fields are needed before the terminal byte. -/
theorem ash_trailer (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp)
    (hn : j≠31 → nxt kA=1 ∧ nxt sj=Fp.ofNat (32+j+1)) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 j)[c]!))
      nxt first last trans)=0 := by
  by_cases hj : j=31
  · subst j
    obtain ⟨hz,ha,hf,hs,he,hp,hb,hb0,hb1,hb2⟩ := ash_cells I R present vidV base0 31
    simp only [cTrl,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_map]
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,
      mul3,notE,hz,ha,hf,hs,he,hp,hb,hb0,hb1,hb2,ite_true]
    simp only [←Fp.ofNat_def]
    grind
  · obtain ⟨hz,ha,hf,hs,he,hp,hb,hb0,hb1,hb2⟩ := ash_cells I R present vidV base0 j
    obtain ⟨hna,hns⟩ := hn hj
    simp only [cTrl,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_map]
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,
      mul3,notE,hz,ha,hf,hs,he,hp,hb,hb0,hb1,hb2,hj,hna,hns,ite_false,ite_true]
    have hadd (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b := by
      apply Fp.ext
      simp only [Fp.toNat_ofNat,Fp.add_def,Fp.toNat_add]
      exact Nat.add_mod _ _ _
    simp only [hadd,←Fp.ofNat_def]
    grind

theorem register_zero (values : Nat→Nat) (v : Nat) :
    lookup ((List.range 32).map fun i=>(reg i,values i)) (reg 0) v=values 0 := by
  rw [List.range_eq_range',List.range'_succ,List.map_cons]
  change lookup ((List.range' 1 31).map fun i=>(reg i,values i)) (reg 0) (if reg 0=reg 0 then values 0 else v)=_
  simp only [ite_true]
  apply lookup_miss
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have hh : ∀i∈List.range' 1 31,reg i≠reg 0 := by decide +kernel
  exact hh i hi

theorem hash_register_zero (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[reg 0]! = digest[j]! := by
  have hqb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun i=>(prbit i,values i)) (reg 0) v=v :=
    miss_block 79 8 (reg 0) v values (by decide +kernel)
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun i=>(pbit i,values i)) (reg 0) v=v :=
    miss_block 16 8 (reg 0) v values (by decide +kernel)
  unfold hashRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append,hqb,append,hpb,append,register_zero]
  simp only [Nat.add_zero,List.getD_eq_getElem?_getD,getElem!_def]
  split <;> simp_all

theorem hash_cells (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    let row:=hashRow (instanceCells I R present vidV) digest hpre present base0 j
    row[kZ]! = 1 ∧ row[kA]! = 0 ∧ row[fwg]! = 0 ∧ row[sj]! = j ∧
      row[esj]! = (if j=31 then 1 else 0) ∧ row[bsha]! = row[bpre]! ∧ row[bpost]! = row[reg 0]! := by
  dsimp only
  rw [hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),
    hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),
    hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),
    hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),
    hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),
    hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),
    ProcPriorCodecHashReads.prior_byte,ProcPriorCodecHashReads.post_byte,hash_register_zero]
  simp [instanceCells,ProcPriorCodecHashReads.hashScalars,lookup,
    act,tau,pres,vid,nn,NN,base,fair,itz,zt,kZ,kA,fwg,sj,esj,bsha,dgg,pos,bpost,bpre,vbg,isj]

/-- Every retained trailer constraint holds on an actual digest row, including
the complete 31-register shift and the digest-to-public-hash transition. -/
theorem hash_trailer (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hn : j≠31 → nxt kZ=1 ∧ nxt sj=Fp.ofNat (j+1) ∧
      ∀i<31,nxt (reg i)=Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[reg (i+1)]!))
    (hend : j=31 → nxt kA=1 ∧ nxt sj=Fp.ofNat 32) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!))
      nxt first last trans)=0 := by
  have hadd (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b := by
    apply Fp.ext
    simp only [Fp.toNat_ofNat,Fp.add_def,Fp.toNat_add]
    exact Nat.add_mod _ _ _
  by_cases hj : j=31
  · subst j
    obtain ⟨hz,ha,hf,hs,he,hb,hp⟩ := hash_cells I R present vidV digest hpre base0 31
    obtain ⟨hna,hns⟩ := hend rfl
    simp only [cTrl,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_map]
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,
      mul3,notE,hz,ha,hf,hs,he,hb,hp,hna,hns,ite_true,ite_false,Bool.false_eq_true]
    simp only [←Fp.ofNat_def]
    grind
  · obtain ⟨hz,ha,hf,hs,he,hb,hp⟩ := hash_cells I R present vidV digest hpre base0 j
    obtain ⟨hnz,hns,hreg⟩ := hn hj
    simp only [cTrl,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_map]
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,
      mul3,notE,hz,ha,hf,hs,he,hb,hp,hnz,hns,hj,ite_false,ite_true,Bool.false_eq_true]
    simp only [hadd,←Fp.ofNat_def]
    constructor
    · grind
    · intro i hi
      have hh := hreg i (List.mem_range.mp hi)
      simp only [←Fp.ofNat_def] at hh
      grind

theorem lookup_value (xs : List (Nat×Nat)) (c v initial : Nat)
    (hex : ∃p∈xs,p.1=c) (hv : ∀p∈xs,p.1=c → p.2=v) : lookup xs c initial=v := by
  induction xs generalizing initial with
  | nil => simp at hex
  | cons p ps ih =>
    by_cases ht : ∃q∈ps,q.1=c
    · exact ih _ ht (fun q hq=>hv q (by simp [hq]))
    · have hp : p.1=c := by
        obtain ⟨q,hq,he⟩ := hex
        rcases List.mem_cons.mp hq with rfl|hq
        · exact he
        · exact False.elim (ht ⟨q,hq,he⟩)
      simp only [lookup,List.foldl_cons,hp,ite_true]
      exact (lookup_miss ps c p.2 (by intro q hq he; exact ht ⟨q,hq,he⟩)).trans (hv p (by simp) hp)

theorem register_value (values : Nat→Nat) (v i : Nat) (hi:i<32) :
    lookup ((List.range 32).map fun j=>(reg j,values j)) (reg i) v=values i := by
  apply lookup_value
  · exact ⟨(reg i,values i),List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩,rfl⟩
  · intro p hp he
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hh : ∀a b:Fin 32,reg a.val=reg b.val → a.val=b.val := by decide +kernel
    have hji := hh ⟨j,List.mem_range.mp hj⟩ ⟨i,hi⟩ he
    change j=i at hji
    simp only [hji]

theorem hash_register (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j i : Nat) (hi:i<32) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[reg i]! = digest.getD (j+i) 0 := by
  have hw : reg i<Codec.width := (by decide +kernel : ∀i:Fin 32,reg i.val<Codec.width) ⟨i,hi⟩
  have hb : (reg i<16∨24≤reg i) ∧ (reg i<79∨87≤reg i) :=
    (by decide +kernel : ∀i:Fin 32,(reg i.val<16∨24≤reg i.val) ∧ (reg i.val<79∨87≤reg i.val)) ⟨i,hi⟩
  have hqb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun j=>(prbit j,values j)) (reg i) v=v :=
    miss_block 79 8 (reg i) v values hb.2
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun j=>(pbit j,values j)) (reg i) v=v :=
    miss_block 16 8 (reg i) v values hb.1
  unfold hashRow
  rw [SchedSetAll.cell _ _ _ hw,append,hqb,append,hpb,append,register_value _ _ i hi]

/-- Actual consecutive digest rows discharge all trailer transition premises. -/
theorem hash_inside (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (hj:j<31) (first last trans : Fp) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!))
      (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 (j+1))[c]!))
      first last trans)=0 := by
  apply hash_trailer
  · intro _
    obtain ⟨hz,_,_,hs,_⟩ := hash_cells I R present vidV digest hpre base0 (j+1)
    refine ⟨?_,?_,?_⟩
    · rw [hz]; rfl
    · rw [hs]
    · intro i hi
      rw [hash_register _ _ _ _ _ _ _ _ _ (by omega),hash_register _ _ _ _ _ _ _ _ _ (by omega)]
      rw [show j+1+i=j+(i+1) by omega]
  · intro he; omega

/-- The final digest row hands off to the first native all-shards-hash row. -/
theorem hash_to_ash (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 : Nat) (first last trans : Fp) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 31)[c]!))
      (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 0)[c]!))
      first last trans)=0 := by
  apply hash_trailer
  · intro h; exact False.elim (h rfl)
  · intro _
    obtain ⟨_,ha,_,hs,_⟩ := ash_cells I R present vidV base0 0
    constructor
    · rw [ha]; rfl
    · rw [hs]

/-- Actual consecutive public-hash rows discharge all trailer premises. -/
theorem ash_inside (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (_hj:j<31) (first last trans : Fp) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 j)[c]!))
      (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 (j+1))[c]!))
      first last trans)=0 := by
  apply ash_trailer
  intro _
  obtain ⟨_,ha,_,hs,_⟩ := ash_cells I R present vidV base0 (j+1)
  constructor
  · rw [ha]; rfl
  · rw [hs,Nat.add_assoc]
end ZkFormal.NearV3.Candidates.ProcPriorCodecSideTrailer
