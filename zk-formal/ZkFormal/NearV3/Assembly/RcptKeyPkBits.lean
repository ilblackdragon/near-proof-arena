import ZkFormal.NearV3.Assembly.RcptKeyGatePhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

set_option maxRecDepth 4096 in
theorem keyPk_upper_cell (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<4) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (keyAux accountId accessId fallback))) p ⟨sPK,i,len⟩ (xb j)=
      frameBit (keyByte p ⟨sPK,i,len⟩/16) j := by
  have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hh with rfl|rfl|rfl|rfl
  all_goals simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,keyAux,
    tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
    kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,sPK,sGP,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
    List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
    decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
  all_goals exact boolInput_preserves _ _ (frameBit_boolean _ _)

set_option maxRecDepth 4096 in
theorem keyPk_lower_cell (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<4) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (keyAux accountId accessId fallback))) p ⟨sPK,i,len⟩ (xb (4+j))=
      frameBit (keyByte p ⟨sPK,i,len⟩%16) j := by
  have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hh with rfl|rfl|rfl|rfl
  all_goals simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,keyAux,
    tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
    kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,sPK,sGP,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
    List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
    decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
  all_goals exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem keyPk_nibbles_eval (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    let tr := receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (keyAux accountId accessId fallback))) p ⟨sPK,i,len⟩ ⟨sPK,i,len⟩
    hiPK.eval tr 0 0 pub=Fp.ofNat (keyByte p ⟨sPK,i,len⟩/16) ∧
      loPK.eval tr 0 0 pub=Fp.ofNat (keyByte p ⟨sPK,i,len⟩%16) := by
  dsimp only
  constructor
  · rw [show hiPK=bitsX 0 4 from rfl,eval_frame_bits _ 0 0 pub 0 (keyByte p ⟨sPK,i,len⟩/16) 4
      (fun j hj=>by simpa only [Nat.zero_add,receiptPair,ite_true] using keyPk_upper_cell accountId accessId constants pub digests tokens fallback p i len j hj)]
    rw [Nat.mod_eq_of_lt (keyByte_nibbles p ⟨sPK,i,len⟩).2.1]
  · rw [show loPK=bitsX 4 4 from rfl,eval_frame_bits _ 0 0 pub 4 (keyByte p ⟨sPK,i,len⟩%16) 4
      (fun j hj=>keyPk_lower_cell accountId accessId constants pub digests tokens fallback p i len j hj)]
    rw [Nat.mod_eq_of_lt (keyByte_nibbles p ⟨sPK,i,len⟩).2.2]

end ZkFormal.NearV3.Assembly.RcptSkeleton
