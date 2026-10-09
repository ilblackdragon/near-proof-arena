import ZkFormal.NearV3.Candidates.ProcPriorCodecSideCarry
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideNext
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll

open ZkFormal.Chacha.Table.E in
def nextGroup : List Expr :=
  [.mul encG (sub (n pos) (.add (c pos) (k 1))),
   mul3 (c kA) (c esj) (.mul (n act) (notE (n kF)))]

theorem next_group_eq : nextGroup=(cKind.drop 77).take 2 := by decide +kernel

theorem next_group_retained :
    nextGroup.filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x)=nextGroup := by decide +kernel

theorem cast_add (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat,Fp.add_def,Fp.toNat_add]
  exact Nat.add_mod _ _ _

theorem encoded_next (cur nxt : Nat→Fp) (first last trans : Fp)
    (hA:cur kA=0) (hp:nxt pos=cur pos+1) :
    ∀e∈nextGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  simp only [nextGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,mul3,
    Bool.false_eq_true,ite_false,ite_true,hA,hp]
  all_goals try simp only [←Fp.ofNat_def]
  all_goals grind only

theorem hash_position (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[pos]! = base0+j := by
  rw [ProcPriorCodecSideZero.hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel),append]
  simp [ProcPriorCodecHashReads.hashScalars,lookup,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj]

theorem ash_position (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat) :
    (ashRow (instanceCells I R present vidV) I base0 j)[pos]! = base0+32+j := by
  unfold ashRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append]
  simp [lookup,kA,pos,sj,bsha,pm0,pm1,isj,esj]

theorem header_inside (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (first last trans : Fp) :
    ∀e∈nextGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present p)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present (p+1))[c]!)
      first last trans)=0 := by
  apply encoded_next
  · rw [(ProcPriorCodecSideMultiplicity.header_flags I R present vidV params hdr p).2.2.2.1]
    rfl
  · rw [(ProcPriorCodecSideZero.header_cells I R present vidV params hdr p).2.2.2.1,
      (ProcPriorCodecSideZero.header_cells I R present vidV params hdr (p+1)).2.2.2.1,cast_add]
    rfl

theorem hash_inside (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (first last trans : Fp) :
    ∀e∈nextGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!)
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 (j+1))[c]!)
      first last trans)=0 := by
  apply encoded_next
  · rw [(ProcPriorCodecSideMultiplicity.hash_flags I R present vidV digest hpre base0 j).2.2.2.1]
    rfl
  · rw [hash_position,hash_position,show base0+(j+1)=base0+j+1 by omega,cast_add]
    rfl

theorem hash_to_ash (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 : Nat) (first last trans : Fp) :
    ∀e∈nextGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 31)[c]!)
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 0)[c]!)
      first last trans)=0 := by
  apply encoded_next
  · rw [(ProcPriorCodecSideMultiplicity.hash_flags I R present vidV digest hpre base0 31).2.2.2.1]
    rfl
  · rw [hash_position,ash_position,show base0+32+0=base0+31+1 by omega,cast_add]
    rfl

theorem ash_next (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp)
    (hn:j≠31 ∨ nxt act=0 ∨ nxt kF=1) :
    ∀e∈nextGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 j)[c]!) nxt
      first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.ash_flags I R present vidV base0 j
  have hR:=hz kR (by simp)
  have he := (ProcPriorCodecSideZero.ash_cells I R present vidV base0 j).2.2.2.2.2.1
  intro e helem
  simp only [nextGroup,List.mem_cons,List.mem_nil_iff,or_false] at helem
  rcases helem with rfl|rfl
  · simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      encG,Bool.false_eq_true,ite_false,ite_true,hH,hZ,hR]
    change (0+(0+0))*_=0
    grind only
  · simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      notE,mul3,Bool.false_eq_true,ite_false,ite_true,hA,he]
    rcases hn with hn|hn|hn
    · simp only [hn,ite_false]
      change 1*0*_=0
      grind only
    · rw [hn]
      grind only
    · rw [hn]
      change 1*_*(_*(1+ -1))=0
      grind only

theorem ash_to_header (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (I' : Input) (R' : Run) (present' : Bool) (vidV' : Nat) (params hdr : List Nat)
    (first last trans : Fp) :
    ∀e∈nextGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 31)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I' R' present' vidV') params hdr present' 0)[c]!)
      first last trans)=0 := by
  apply ash_next
  right; right
  rw [(ProcPriorCodecSideMultiplicity.header_flags I' R' present' vidV' params hdr 0).2.2.2.2.1]
  rfl

theorem ash_final_carry (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecSideCarry.carryGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 31)[c]!) nxt
      first last trans)=0 := by
  obtain ⟨hz,ha,hA,hs,hi,he,ht,hiv,hzt⟩ := ProcPriorCodecSideZero.ash_cells I R present vidV base0 31
  intro e hm
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
  simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
    gT,Bool.false_eq_true,ite_false,ite_true,ha,hA,he]
  change (1+ -(1*1))*_=0
  grind only

end ZkFormal.NearV3.Candidates.ProcPriorCodecSideNext
