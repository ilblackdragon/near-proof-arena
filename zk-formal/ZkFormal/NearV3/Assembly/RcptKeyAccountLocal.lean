import ZkFormal.NearV3.Assembly.RcptKeyCharacterCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

def keyAccountCurrent : List Expr :=
  [.mul (c sV) (sub (c tA) (.add (k 2) (two (c idx)))),.mul (c sV) (sub (c symA) hiE),
   .mul (c sV) (c lastA),.mul (c kz) (sub (c tA) (c idx)),.mul (c kz) (c symA),.mul (c kz) (c lastA),
   mul3 (c sRID) (c fs) (sub (c tA) (.add (k 2) (two (c Lv)))),
   mul3 (c sRID) (c fs) (sub (c symA) (k SYM_END)),mul3 (c sRID) (c fs) (sub (c lastA) (k 1)),
   .mul (c kz) (Dsl.not (c sVL)),mul3 (c sVL) (c fs) (Dsl.not (c kz)),
   .mul (c sV) (sub (c tB) (.add (k 3) (two (c idx)))),.mul (c sV) (sub (c symB) loE)]

theorem keyAccountCurrent_footprint : keyAccountCurrent.all currentExpr=true ∧ keyAccountCurrent.all noEmissionExpr=true := by decide

theorem keyAccountCurrent_in_key : ∀e∈keyAccountCurrent,e∈cKey := by
  intro e he
  simp only [keyAccountCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cKey,List.mem_cons,List.not_mem_nil,or_false]
  grind only

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem receipt_key_account_current (ctx : ApplyCtx) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hi : row.index<fieldLen p.input row.state) :
    ∀e∈keyAccountCurrent,e.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists)
        (booleanReceiptAux (characterAux (keyAux accountId accessId fallback)))) p row row) 0 0 pub=0 := by
  let cn := booleanConstants constants
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists)
    (booleanReceiptAux (characterAux (keyAux accountId accessId fallback)))
  let tr := receiptPair cn aux p row row
  have hfields := keyAux_transport accountId accessId constants pub digests (receiptPlanToken ctx lists) (characterAux fallback) p row
  rw [key_character_commute] at hfields
  have htA : tr.cell 0 0 tA=Fp.ofNat (keyPosA p row) := hfields tA (by decide)
  have htB : tr.cell 0 0 tB=Fp.ofNat (keyPosB p row) := hfields tB (by decide)
  have hsA : tr.cell 0 0 symA=Fp.ofNat (keySymA p row) := hfields symA (by decide)
  have hsB : tr.cell 0 0 symB=Fp.ofNat (keySymB p row) := hfields symB (by decide)
  have hlA : tr.cell 0 0 lastA=bitCell (keyLast p row) := hfields lastA (by decide)
  have hz : tr.cell 0 0 kz=bitCell (keyZero row) := hfields kz (by decide)
  have hidx : tr.cell 0 0 idx=Fp.ofNat row.index := rfl
  have hlv : tr.cell 0 0 Lv=Fp.ofNat p.input.receipt.receiverId.length := rfl
  have hfs : tr.cell 0 0 fs=keyFirst row := by
    change (if row.index=0 then (1:Fp) else 0)=bitCell (row.index==0)
    simp only [bitCell,beq_iff_eq]
  have hst (s : Nat) (hsc : controlColumn s=true) (hss : s∈states) : tr.cell 0 0 s=keyState row s := by
    have hh := (receipt_control_cell cn aux p row hsc).trans (control_state row hss)
    apply hh.trans
    by_cases hs : s=row.state
    · simp only [keyState,bitCell,hs,beq_self_eq_true,ite_true]
    · simp only [keyState,bitCell,if_neg hs,beq_eq_false_iff_ne.mpr (Ne.symm hs),Bool.false_eq_true,ite_false]
  have hchars (hv : row.state=sV) : hiE.eval tr 0 0 pub=Fp.ofNat (keyByte p row/16) ∧
      loE.eval tr 0 0 pub=Fp.ofNat (keyByte p row%16) :=
    key_character_nibbles ctx lists constants pub digests (keyAux accountId accessId fallback) p row hw (Or.inl hv) hi
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [keyAccountCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_mul,eval_mul3,eval_sub,eval_add,eval_not,eval_k,two,eval_smul,eval_c,
    htA,htB,hsA,hsB,hlA,hz,hidx,hlv,hfs,hst sV (by decide) (by decide),
    hst sVL (by decide) (by decide),hst sRID (by decide) (by decide)]
  all_goals by_cases hV : row.state=sV
  all_goals by_cases hVL : row.state=sVL
  all_goals by_cases hR : row.state=sRID
  all_goals by_cases h0 : row.index=0
  all_goals by_cases h2 : row.index<2
  all_goals try rw [(hchars hV).1]
  all_goals try rw [(hchars hV).2]
  all_goals simp only [sV,sVL,sRID] at hV hVL hR
  all_goals try omega
  all_goals simp only [hV,hVL,hR,h0,h2,keyState,keyFirst,keyPosA,keyPosB,keySymA,keySymB,keyLast,keyZero,bitCell,
    sV,sVL,sRID,sT0,sSL,sS,sKT,sPK,sGP,ofNat_add_e,ofNat_mul_e,
    Nat.reduceEqDiff,Nat.reduceBEq,decide_true,decide_false,Bool.true_or,Bool.false_or,Bool.or_true,Bool.or_false,
    Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_eq_true,
    beq_iff_eq,ite_true,ite_false,or_true,true_or,or_false,false_or]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,
    show Fp.ofNat 2=(2:Fp) from rfl,show Fp.ofNat 3=(3:Fp) from rfl,show Fp.ofNat SYM_END=(SYM_END:Fp) from rfl]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
