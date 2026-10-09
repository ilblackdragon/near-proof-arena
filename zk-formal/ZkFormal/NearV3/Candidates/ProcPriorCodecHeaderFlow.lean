import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInitial
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderFlow
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecHeaderRegisters ProcPriorCodecNativeBytes

open ZkFormal.Chacha.Table.E in
def localGroup : List Expr :=
  [.mul (c kH) (sub (c bpost) (c (reg 0))),
   .mul (c kH) (sub (c bpre) (.mul (c pres) (c bpost)))]

open ZkFormal.Chacha.Table.E in
def shiftGroup : List Expr :=
  [mul3 (c kH) (notE (c ehp)) (notE (n kH))]++
  (List.range 31).map (fun i=>mul3 (c kH) (notE (c ehp)) (sub (n (reg i)) (c (reg (i+1)))))

open ZkFormal.Chacha.Table.E in
def endGroup : List Expr :=
  [.mul (c ehp) (notE (n fS)),.mul (c ehp) (n kidx),
   .mul (c ehp) (n g),.mul (c ehp) (notE (n rs))]

def flowGroup : List Expr := localGroup++shiftGroup++endGroup

theorem flow_group_eq : flowGroup=cKind.drop 91 := by decide +kernel

theorem header_decomposition : ProcPriorCodecHeaderInactive.headerGroup=
    ProcPriorCodecHeaderInitial.initialGroup++flowGroup := by decide +kernel

theorem local_native (I : Input) (R : Run) (present : Bool) (vidV p : Nat) (hp:p<5)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈localGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present p)[c]!) nxt first last trans)=0 := by
  obtain ⟨hpr,hpost,hpre,hv⟩ := ProcPriorCodecSideBytes.header_byte_cells I R present vidV
    (parameters I R) (ProcPriorCodecNativeBytes.header R) p
  have hr:=native_register_zero I R present vidV p hp
  intro e he
  simp only [localGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.sub,Bool.false_eq_true,ite_false,hpr,hpost,hpre,hr]
  all_goals cases present
  all_goals try simp only [b2n,Bool.false_eq_true,ite_false,ite_true]
  all_goals change _=0
  all_goals try simp only [show Fp.ofNat 0=0 by rfl,show Fp.ofNat 1=1 by rfl]
  all_goals grind only

theorem shift (cur nxt : Nat→Fp) (first last trans : Fp)
    (hh:nxt kH=1) (hs:∀i,i<31→nxt (reg i)=cur (reg (i+1))) :
    ∀e∈shiftGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  simp only [shiftGroup,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|he
  · simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,mul3,
      Bool.false_eq_true,ite_false,ite_true,hh]
    change _*_* (1+ -1)=0
    grind only
  · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,mul3,
      Bool.false_eq_true,ite_false,ite_true,hs i (List.mem_range.mp hi)]
    grind only

theorem shift_inside (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (first last trans : Fp) :
    ∀e∈shiftGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present p)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present (p+1))[c]!)
      first last trans)=0 := by
  apply shift
  · rw [(ProcPriorCodecSideMultiplicity.header_flags I R present vidV params hdr (p+1)).2.1]
    rfl
  · intro i hi
    rw [header_register _ _ _ _ _ _ _ _ (by omega),header_register _ _ _ _ _ _ _ _ (by omega),
      show p+1+i=p+(i+1) by omega]

theorem shift_end (cur nxt : Nat→Fp) (first last trans : Fp) (he:cur ehp=1) :
    ∀e∈shiftGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  simp only [shiftGroup,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|hm
  · simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,mul3,
      Bool.false_eq_true,ite_false,ite_true,he]
    change _*(1+ -1)*_=0
    grind only
  · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,mul3,
      Bool.false_eq_true,ite_false,ite_true,he]
    change _*(1+ -1)*_=0
    grind only

theorem boundary_inactive (cur nxt : Nat→Fp) (first last trans : Fp) (he:cur ehp=0) :
    ∀e∈endGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  simp only [endGroup,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,
    Bool.false_eq_true,ite_false,ite_true,he]
  all_goals grind only

theorem boundary (cur nxt : Nat→Fp) (first last trans : Fp)
    (hS:nxt fS=1) (hk:nxt kidx=0) (hg:nxt g=0) (hr:nxt rs=1) :
    ∀e∈endGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  simp only [endGroup,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,
    Bool.false_eq_true,ite_false,ite_true,hS,hk,hg,hr]
  all_goals try simp only [show Fp.ofNat 1=1 by rfl]
  all_goals grind only
theorem native_inside (I : Input) (R : Run) (present : Bool) (vidV p : Nat) (hp:p<4)
    (first last trans : Fp) :
    ∀e∈flowGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present p)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present (p+1))[c]!) first last trans)=0 := by
  simp only [flowGroup,List.forall_mem_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact local_native I R present vidV p (by omega) _ _ _ _
  · exact shift_inside I R present vidV (parameters I R) (ProcPriorCodecNativeBytes.header R) p _ _ _
  · apply boundary_inactive
    rw [(ProcPriorCodecSideZero.header_cells I R present vidV
      (parameters I R) (ProcPriorCodecNativeBytes.header R) p).2.2.2.2.2.1]
    simp only [show p≠4 by omega,ite_false]
    rfl

theorem native_end (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (nxt : Nat→Fp) (first last trans : Fp)
    (hS:nxt fS=1) (hk:nxt kidx=0) (hg:nxt g=0) (hr:nxt rs=1) :
    ∀e∈flowGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present 4)[c]!) nxt first last trans)=0 := by
  simp only [flowGroup,List.forall_mem_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact local_native I R present vidV 4 (by decide) _ _ _ _
  · apply shift_end
    rw [(ProcPriorCodecSideZero.header_cells I R present vidV
      (parameters I R) (ProcPriorCodecNativeBytes.header R) 4).2.2.2.2.2.1]
    rfl
  · exact boundary _ _ _ _ _ hS hk hg hr

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderFlow
