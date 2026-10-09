import ZkFormal.NearV3.Candidates.ProcPriorCodecSideMultiplicity
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideAdditions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecSideMultiplicity ProcPriorCodecSideZero

theorem side (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz:∀c∈[kR,rs,rend,fA,fS],cur c=0)
    (hs:cur ehp*nxt srcC=0) (hu:cur ehp*nxt useC=0) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  have hR:=hz kR (by simp)
  have hrs:=hz rs (by simp)
  have hrend:=hz rend (by simp)
  have hA:=hz fA (by simp)
  have hS:=hz fS (by simp)
  simp only [ProcPriorCodecActual.additions,isZ,List.take_succ_cons,List.take_zero,
    List.cons_append,List.nil_append,List.forall_mem_cons,List.forall_mem_append,List.forall_mem_nil]
  simp only [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    Bool.false_eq_true,ite_false,ite_true,hR,hrs,hrend,hA,hS]
  simp only [Lean.Grind.Semiring.zero_mul,hs,hu,true_and]
  intro e he
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
  simp only [mul3,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,Expr.evalWith,ProcPriorCells.env,Bool.false_eq_true,ite_false,ite_true,hS]
  grind only

theorem header (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hs:(p=4→nxt srcC=0)) (hu:(p=4→nxt useC=0)) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ProcPriorCodecAssignments.headerRow (ProcPriorCodecNativeHash.instanceCells I R present vidV) params hdr present p)[c]!)
      nxt first last trans)=0 := by
  obtain ⟨hz,_⟩:=header_flags I R present vidV params hdr p
  obtain ⟨_,_,_,_,_,hehp,_⟩:=header_cells I R present vidV params hdr p
  apply side
  · intro c hc
    have hh:c∈[kR,fS,fR,fA,rend,fwg,cg,rs] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp
    rw [hz c hh]; rfl
  · rw [hehp]
    by_cases hp:p=4
    · rw [if_pos hp,hs hp]; grind only
    · rw [if_neg hp]; change (0:Fp)*_=0; grind only
  · rw [hehp]
    by_cases hp:p=4
    · rw [if_pos hp,hu hp]; grind only
    · rw [if_neg hp]; change (0:Fp)*_=0; grind only

theorem hash (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ProcPriorCodecAssignments.hashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV) digest hpre present base0 j)[c]!)
      nxt first last trans)=0 := by
  obtain ⟨hz,_⟩:=hash_flags I R present vidV digest hpre base0 j
  obtain ⟨hz0,_⟩:=hash_cells I R present vidV digest hpre base0 j
  apply side
  · intro c hc
    have hh:c∈[kR,fS,fR,fA,rend,fwg,cg,rs] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp
    rw [hz c hh]; rfl
  all_goals rw [hz0 ehp (by simp)]; change (0:Fp)*_=0; grind only

theorem ash (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ProcPriorCodecAssignments.ashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV) I base0 j)[c]!)
      nxt first last trans)=0 := by
  obtain ⟨hz,_⟩:=ash_flags I R present vidV base0 j
  obtain ⟨hz0,_⟩:=ash_cells I R present vidV base0 j
  apply side
  · intro c hc
    have hh:c∈[kR,fS,fR,fA,rend,fwg,cg,rs] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp
    rw [hz c hh]; rfl
  all_goals rw [hz0 ehp (by simp)]; change (0:Fp)*_=0; grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecSideAdditions
