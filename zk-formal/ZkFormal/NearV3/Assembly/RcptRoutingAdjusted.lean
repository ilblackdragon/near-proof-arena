import ZkFormal.NearV3.Assembly.RcptSystemCertificate
import ZkFormal.NearV3.Assembly.RoutingFrameTransport

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

/-- Preserve actual receipt registers: receiver rows keep the total receiver
length; the first RID row has index zero and its real digest byte. These fields
are unused by the routing equations in the complementary state. -/
def routingAdjustedCell (f : RouteFrame) (len : Nat) (ridByte : Fp) (col : Nat) : Fp :=
  if col==idx && f.atEnd then 0 else
  if col==Lv && !f.atEnd then Fp.ofNat len else
  if col==b && f.atEnd then ridByte else frameCell f col

def routingAdjustedTrace (f : RouteFrame) (len : Nat) (ridByte : Fp) : Trace Fp :=
  ⟨fun _=>1,fun _ row=>if row=0 then routingAdjustedCell f len ridByte else frameNext f⟩

theorem routingAdjusted_other (f : RouteFrame) (len : Nat) (rb : Fp) (col : Nat)
    (h : col≠idx ∧ col≠Lv ∧ col≠b) : routingAdjustedCell f len rb col=frameCell f col := by
  simp only [routingAdjustedCell,beq_eq_false_iff_ne.mpr h.1,beq_eq_false_iff_ne.mpr h.2.1,
    beq_eq_false_iff_ne.mpr h.2.2,Bool.false_and,Bool.false_eq_true,ite_false]

theorem routingAdjusted_bits (f : RouteFrame) (len : Nat) (rb : Fp) (pub : List Fp) :
    (bitsX 20 9).eval (routingAdjustedTrace f len rb) 0 0 pub=(bitsX 20 9).eval (frameTrace f) 0 0 pub ∧
    (bitsX 29 9).eval (routingAdjustedTrace f len rb) 0 0 pub=(bitsX 29 9).eval (frameTrace f) 0 0 pub := by
  constructor <;> rfl

set_option maxRecDepth 4096 in
theorem routingAdjusted_eval (f : RouteFrame) (len : Nat) (rb : Fp) (pub : List Fp) :
    ∀e∈cRoute,e.eval (routingAdjustedTrace f len rb) 0 0 pub=e.eval (frameTrace f) 0 0 pub := by
  intro e he
  have hb := routingAdjusted_bits f len rb pub
  simp only [cRoute,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_sub,eval_add,eval_mul,eval_mul3,eval_not,eval_k,rwE,orE,hb.1,hb.2,eval_c,eval_n]
  all_goals dsimp only [routingAdjustedTrace,frameTrace,Trace.height]
  all_goals simp only [Nat.reducePow,Nat.reduceAdd,Nat.reduceMod,ite_true,ite_false]
  all_goals simp only [routingAdjustedCell,idx,Lv,b,sV,sRID,fs,gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH,xb,
    Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceBEq,beq_self_eq_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false]
  all_goals cases hf : f.atEnd <;> simp only [hf,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals try rfl
  all_goals simp only [show (8:Nat)=sV from rfl,show (9:Nat)=sRID from rfl,frame_cell_0,frame_cell_1,hf,ite_true,ite_false]
  all_goals try simp only [sV,sRID,Nat.reduceEqDiff,Nat.reduceBEq,ite_true,ite_false]
  all_goals grind only

theorem routingAdjusted_local (f : RouteFrame) (hf : f.Ordered) (len : Nat) (rb : Fp) (pub : List Fp) :
    ∀e∈cRoute,e.eval (routingAdjustedTrace f len rb) 0 0 pub=0 := by
  intro e he
  rw [routingAdjusted_eval f len rb pub e he]
  exact frame_route_constraints f hf pub e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
