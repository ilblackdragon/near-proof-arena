import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordPhase
set_option maxHeartbeats 1000000
open ZkFormal.Air ZkFormal.Algebra Lean.Grind ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecStepRows ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash

def phase : List Expr := (cKind.drop (boolCols.length+recBoolCols.length)).take 6

theorem record_phase (cur nxt : Nat→Fp) (trans : Fp)
    (ha : cur act=1) (hR : cur kR=1)
    (hH : cur kH=0) (hZ : cur kZ=0) (hA : cur kA=0) (hF : cur kF=0)
    (hs : cur fS+(cur fR+cur fA)=1) :
    ∀e∈phase,e.evalWith (ProcPriorCells.env cur nxt 0 0 trans)=0 := by
  have he : phase=[sub (c act) (.add (c kH) (.add (c kR) (.add (c kZ) (c kA)))),
    sub (c kR) (.add (c fS) (.add (c fR) (c fA))),
    .mul (c kF) (notE (c kH)),.mul .isLast (c act),
    mul3 .isTransition (notE (c act)) (n act),
    .mul .isFirst (.mul (c act) (notE (c kF)))] := by decide +kernel
  rw [he]
  simp only [List.forall_mem_cons,List.forall_mem_nil,Expr.evalWith,ProcPriorCells.env,c,n,k,sub,mul3,notE,
    ha,hR,hH,hZ,hA,hF,Bool.false_eq_true,ite_true,ite_false,List.not_mem_nil,false_implies,forall_const]
  change (1 + -(0+(1+(0+0))) : Fp)=0 ∧
    (1:Fp)+ -(cur fS+(cur fR+cur fA))=0 ∧
    (0:Fp)*(1 + -0)=0 ∧ (0:Fp)*1=0 ∧
    trans*(1 + -(1:Fp))*nxt act=0 ∧ (0:Fp)*(1*(1 + -0))=0 ∧ True
  rw [hs]
  have hz : (1:Fp)+ -(1:Fp)=0 := by decide +kernel
  simp only [hz,Semiring.mul_zero,Semiring.zero_mul]
  decide +kernel

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f g : Nat) (s out : State)
    (hf : f<3) (hg : g<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f g s=.ok (.yield out))
    (nxt : Nat→Fp) (trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈phase,
      e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt 0 0 trans)=0 := by
  obtain ⟨tail,ht,hr⟩ := successful_row I R present gb fwd (instanceCells I R present vid) k f g s out hf hg h
  let a := record I R present (instanceCells I R present vid)
    (baseExtra R.n k f g (b2n I.allowed[k]!) gb[k]!++tail) k f g
  have hh : a[act]! =1 ∧ a[kR]! =1 ∧ a[kH]! =0 ∧ a[kZ]! =0 ∧ a[kA]! =0 ∧
      a[kF]! =0 ∧ a[ehp]! =0 ∧ a[fS]! =(if f=0 then 1 else 0) ∧
      a[fR]! =(if f=1 then 1 else 0) ∧ a[fA]! =(if f=2 then 1 else 0) := by
    exact ProcPriorCodecRecordKind.flags I R present vid k f g _ _ _ _ _ tail ht
  obtain ⟨ha,hR,hH,hZ,hA,hF,_,hS,hFR,hFA⟩ := hh
  refine ⟨a,hr,record_phase _ nxt trans ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals simp only [ha,hR,hH,hZ,hA,hF,hS,hFR,hFA]
  all_goals first | rfl | skip
  have hf' : f=0 ∨ f=1 ∨ f=2 := by omega
  rcases hf' with rfl|rfl|rfl <;> decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordPhase
