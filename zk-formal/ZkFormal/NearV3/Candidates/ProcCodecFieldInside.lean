import ZkFormal.NearV3.Candidates.ProcCodecRecordTransitionShape
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
set_option maxRecDepth 4096
namespace ZkFormal.NearV3.Candidates.ProcCodecFieldInside
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecTransitionRows ProcPriorCodecEndArithmetic

theorem inside (R : Run) (k f g : Nat) (a b : Array Nat) (ha : Shape R k f g a)
    (hb : Shape R k f (g+1) b) (hg : g<7) (first last trans : Fp) :
    ∀e∈(cRec.drop 1).take 5,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!) first last trans)=0 := by
  obtain ⟨hr,hg0,he,hS,hR,hA,hk,_⟩ := ha
  obtain ⟨nr,ng0,ne,nS,nR,nA,nk,_⟩ := hb
  have hg7 : g≠7 := by omega
  simp only [cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    hr,hg0,he,hS,hR,hA,hk,ng0,nS,nR,nA,nk,hg7,cast_add,show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 0=(0:Fp) from rfl]
  all_goals grind

theorem end_inactive (a : Array Nat) (he : a[e7]! =1) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈(cRec.drop 1).take 5,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  simp only [cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl
  all_goals simp [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.c,Expr.evalWith,ProcPriorCells.env,he]
  all_goals grind

theorem record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∀e∈(cRec.drop 1).take 5,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have ha := ProcCodecRecordTransitionShape.record I R present vid gb fwd out h k f g hk hf hg
  by_cases hg7 : g=7
  · subst g
    apply end_inactive
    exact ha.2.2.1
  · have hb := ProcCodecRecordTransitionShape.record I R present vid gb fwd out h k f (g+1) hk hf (by omega)
    have hl := generated_length I R present vid gb fwd out h
    have hn : 5+24*k+8*f+g+1<out.rows.size := by omega
    unfold ProcCodecPhysicalRows.rowEnvAt
    rw [if_pos hn,show 5+24*k+8*f+g+1=5+24*k+8*f+(g+1) by omega]
    exact inside R k f g _ _ ha hb (by omega) _ _ _

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈(cRec.drop 1).take 5,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 :=
  ProcCodecPhysicalRecordGroups.active_of_records I R present vid gb fwd out h _
    (fun e he=>List.mem_of_mem_drop (List.mem_of_mem_take he))
    (fun k f g hk hf hg=>record I R present vid gb fwd out h k f g hk hf hg) r hr
end ZkFormal.NearV3.Candidates.ProcCodecFieldInside
