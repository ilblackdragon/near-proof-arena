import ZkFormal.NearV3.Candidates.ProcPriorCodecTransitionRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecBoundaryEquations
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecTransitionRows ProcPriorCodecEndArithmetic

def equations : List Expr := (cRec.drop 6).take 5 ++ (cRec.drop 12).take 5

theorem interior (R : Run) (k f g : Nat) (a : Array Nat) (ha : Shape R k f g a)
    (hg : g≠7) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨_,_,he,_,_,_,_,_,hr⟩ := ha
  simp only [equations,cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,he,hr,hg]
  all_goals try simp only [show (2:Nat)≠0 from by decide,show (2:Nat)≠1 from by decide,ite_false,ite_true,Nat.one_mul,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind only

theorem field_change (R : Run) (k f : Nat) (a b : Array Nat)
    (ha : Shape R k f 7 a) (hb : Shape R k (f+1) 0 b) (hf : f<2)
    (first last trans : Fp) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!) first last trans)=0 := by
  obtain ⟨_,_,he,hS,hR,_,hk,_,hr⟩ := ha
  obtain ⟨_,ng,_,_,nR,nA,nk,_⟩ := hb
  have hf' : f=0 ∨ f=1 := by omega
  rcases hf' with rfl|rfl
  all_goals simp only [equations,cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  all_goals intro e heq
  all_goals rcases heq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    he,hS,hR,hk,hr,ng,nR,nA,nk]
  all_goals try simp only [show (2:Nat)≠0 from by decide,show (2:Nat)≠1 from by decide,ite_false,ite_true,Nat.one_mul,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind only

theorem record_change (R : Run) (k : Nat) (a b : Array Nat)
    (ha : Shape R k 2 7 a) (hb : Shape R (k+1) 0 0 b) (hk : k+1<R.n*R.n)
    (first last trans : Fp) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!) first last trans)=0 := by
  obtain ⟨_,_,he,hS,hR,_,hk0,hkl,hr⟩ := ha
  obtain ⟨_,ng,_,nS,_,_,nk,_⟩ := hb
  have hne : k+1≠R.n*R.n := by omega
  simp only [equations,cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    he,hS,hR,hk0,hkl,hr,ng,nS,nk,hne,Bool.false_eq_true,ite_true,ite_false,cast_add]
  all_goals try simp only [show (2:Nat)≠0 from by decide,show (2:Nat)≠1 from by decide,ite_false,ite_true,Nat.one_mul,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals try simp only [show (2:Nat)≠0 from by decide,show (2:Nat)≠1 from by decide,ite_false,ite_true,Nat.one_mul,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind only

theorem final_record (R : Run) (k : Nat) (a : Array Nat) (ha : Shape R k 2 7 a)
    (hk : k+1=R.n*R.n) (nxt : Nat→Fp) (hz : nxt kZ=1) (hj : nxt sj=0) (hd : nxt dgg=1)
    (first last trans : Fp) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨_,_,he,hS,hR,_,_,hkl,hr⟩ := ha
  simp only [equations,cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    he,hS,hR,hkl,hr,hk,hz,hj,hd]
  all_goals try simp only [show (2:Nat)≠0 from by decide,show (2:Nat)≠1 from by decide,ite_false,ite_true,Nat.one_mul,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecBoundaryEquations
