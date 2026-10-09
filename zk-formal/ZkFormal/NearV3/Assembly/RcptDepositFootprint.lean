import ZkFormal.NearV3.Assembly.RcptDepositCandidateLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def depositCandidateColumn (col : Nat) : Bool :=
  col∈[sDEP,fs,fe,b,bef,lk,st,big,r,tprev,r1,c1,c2,c3,c4,dsum,invB] ||
    decide (xb 0≤col ∧ col<xb 66) || decide (dl 0≤col ∧ col<dl 7)

def depositCandidateNext (col : Nat) : Bool :=
  col∈[c1,c2,c3,c4,dsum,r1] || decide (xb 0≤col ∧ col<xb 8) || decide (dl 0≤col ∧ col<dl 7)

def depositCandidateFootprint : Expr→Bool
  | .const _ | .pub _=>true
  | .col col nx=>if nx then depositCandidateNext col else depositCandidateColumn col
  | .add a b | .mul a b=>depositCandidateFootprint a && depositCandidateFootprint b
  | .neg a=>depositCandidateFootprint a
  | _=>false

theorem depositCandidate_footprint : (depositAgeConstraints).all depositCandidateFootprint=true := by decide

theorem depositCandidate_no_emission (col : Nat) (hc : depositCandidateColumn col=true) : emissionColumn col=false := by
  simp only [depositCandidateColumn,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hc
  simp only [sDEP,fs,fe,b,bef,lk,st,big,r,tprev,r1,c1,c2,c3,c4,dsum,invB,xb,dl] at hc
  simp only [emissionColumn,decide_eq_false_iff_not]
  omega

theorem depositCandidate_eval_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,depositCandidateColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (hn : ∀col,depositCandidateNext col=true→tr.cell t ((pos+1)%tr.height t) col=
      tr'.cell t' ((pos'+1)%tr'.height t') col)
    (e : Expr) (he : depositCandidateFootprint e=true) : e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  induction e with
  | const | pub => rfl
  | col col nx =>
    cases nx
    · exact hc col he
    · exact hn col he
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : depositCandidateFootprint a=true ∧ depositCandidateFootprint b=true := by simpa only [depositCandidateFootprint,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : depositCandidateFootprint a=true ∧ depositCandidateFootprint b=true := by simpa only [depositCandidateFootprint,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem depositCandidate_inactive (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sDEP=0) (hr : tr.cell 0 pos r1=0) (hs : tr.cell 0 pos st=0) :
    ∀e∈depositAgeConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  change e∈[_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [dp,eval_mul,eval_mul3,eval_c,hz,hr,hs]
  all_goals grind only


end ZkFormal.NearV3.Assembly.RcptSkeleton
