import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryRows
import ZkFormal.NearV3.Candidates.ProcPriorCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecCarryLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep

theorem high (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k gg : Nat) (s mid out : State)
    (hk : k<R.n*R.n) (hg : gg<7) (hg2 : 2≤gg)
    (ha : step I R present gb fwd inst k 2 gg s=.ok (.yield mid))
    (hb : step I R present gb fwd inst k 2 (gg+1) mid=.ok (.yield out))
    (first last trans : Fp) :
    ∃a b,mid.1=s.1.push a ∧ out.1=mid.1.push b ∧
      ∀e∈(cRec.drop 44).take 4 ++ (cRec.drop 52).take 2,e.evalWith
        (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!) first last trans)=0 := by
  obtain ⟨a,har,hap,hab,hac⟩ := ProcPriorCodecCarryRows.cells I R present gb fwd inst k gg s mid (by omega) hk hg2 ha
  obtain ⟨b,hbr,hbp,hbb,hbc⟩ := ProcPriorCodecCarryRows.cells I R present gb fwd inst k (gg+1) mid out (by omega) hk (by omega) hb
  have hcb : out.2.2.2.2.2=mid.2.2.2.2.2 := by
    have h := ProcPriorCodecCarryTotal.byte_carry I R present gb fwd inst k (gg+1) mid out (by omega) hb
    simpa only [if_neg (show gg+1≠2 by omega)] using h
  have hp : b[apR]! = a[apR]! := hbp.trans hap.symm
  have hb' : b[bigR]! = a[bigR]! := hbb.trans hab.symm
  have hc : b[cb]! = a[cb]! := hbc.trans (hcb.trans hac.symm)
  refine ⟨a,b,har,hbr,?_⟩
  simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [ite_true,mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hp,hb',hc]
  all_goals grind only
/-- All six source-allowance/carry transition equations, including the inactive
first two bytes, follow from the actual executable row pair. -/
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k gg : Nat) (s mid out : State)
    (hk : k<R.n*R.n) (hg : gg<7)
    (ha : step I R present gb fwd inst k 2 gg s=.ok (.yield mid))
    (hb : step I R present gb fwd inst k 2 (gg+1) mid=.ok (.yield out))
    (first last trans : Fp) :
    ∃a b,mid.1=s.1.push a ∧ out.1=mid.1.push b ∧
      ∀e∈(cRec.drop 44).take 4 ++ (cRec.drop 52).take 2,e.evalWith
        (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!) first last trans)=0 := by
  by_cases hh : 2≤gg
  · exact high I R present gb fwd inst k gg s mid out hk hg hh ha hb first last trans
  · obtain ⟨a,har,_,_,_,hlow,_,he2⟩ :=
      ProcPriorCodecAllowanceData.cells I R present gb fwd inst k gg s mid (by omega) hk ha
    obtain ⟨b,hbr,_⟩ := ProcPriorCodecAccumulatorRows.cells I R present gb fwd inst k (gg+1) mid out (by omega) hb
    have hl : a[lowf]! =1 := by simpa only [if_pos (show gg<3 by omega)] using hlow
    have he : a[e2]! =0 := by simpa only [if_neg (show gg≠2 by omega)] using he2
    refine ⟨a,b,har,hbr,?_⟩
    simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
      List.mem_cons,List.mem_nil_iff,or_false]
    intro e heq
    rcases heq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [ite_true,mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hl,he,
      show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
    all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecCarryLocal
