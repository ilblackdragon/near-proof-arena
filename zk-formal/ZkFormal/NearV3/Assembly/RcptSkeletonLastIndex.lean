import ZkFormal.NearV3.Assembly.RcptSkeletonTransitions

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

private theorem pred_cast (n : Nat) (hn : 0<n) : ((n-1:Nat):Fp)=(n:Fp)-1 := by
  have he : n-1+1=n := by omega
  have hc := congrArg (fun x : Nat=>(x:Fp)) he
  grind only

/-- The generated natural field lengths realize every exact last-index expression
of the active V3 table; account nonemptiness is derived from native Receipt.wf. -/
theorem field_last_index (x : Input) (hw : x.receipt.wf=true) (pub : List Fp)
    {s : Nat} {e : Expr} (he : (s,e)∈lastIdx) :
    e.eval (shapeTrace x) 0 0 pub=((fieldLen x s-1:Nat):Fp) := by
  have hp : 0<x.receipt.predecessorId.length ∧ 0<x.receipt.receiverId.length ∧
      0<x.receipt.signerId.length := by
    simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hw
    grind only
  have hpk : 32+32*x.receipt.signerPk.tag-1=31+32*x.receipt.signerPk.tag := by omega
  simp only [lastIdx,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he <;>
    cases he <;>
    simp [eval_sub,eval_c,eval_add,eval_smul,eval_k,shapeTrace,shapeCell,fieldLen,
      sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,
      sXLH,sXRH,sXRF,sXRZ,Lp,Lv,Ls,kt,hr,hpk,pred_cast _ hp.1,pred_cast _ hp.2.1,pred_cast _ hp.2.2]
  all_goals first | rfl | (change (31:Fp)+32*(x.receipt.signerPk.tag:Fp)=((31+32*x.receipt.signerPk.tag:Nat):Fp); grind only)

end ZkFormal.NearV3.Assembly.RcptSkeleton
