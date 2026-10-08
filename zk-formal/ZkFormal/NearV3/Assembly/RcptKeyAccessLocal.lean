import ZkFormal.NearV3.Assembly.RcptKeyAccessBytes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

def keyAccessCurrent : List Expr :=
  [ mul3 (c ee) (c sT0) (c tA), mul3 (c ee) (c sT0) (c symA), mul3 (c ee) (c sT0) (c lastA),
    .mul (mul3 (c ee) (c sSL) (c fs)) (sub (c tA) (.add (k 2) (two (c Ls)))),
    .mul (mul3 (c ee) (c sSL) (c fs)) (c symA), .mul (mul3 (c ee) (c sSL) (c fs)) (c lastA),
    mul3 (c ee) (c sS) (sub (c tA) (.add (k 2) (two (c idx)))),
    mul3 (c ee) (c sS) (sub (c symA) hiE), mul3 (c ee) (c sS) (c lastA),
    mul3 (c ee) (c sKT) (sub (c tA) (.add (k 4) (two (c Ls)))),
    mul3 (c ee) (c sKT) (c symA), mul3 (c ee) (c sKT) (c lastA),
    mul3 (c ee) (c sPK) (sub (c tA) (sum [k 6, two (c Ls), two (c idx)])),
    mul3 (c ee) (c sPK) (sub (c symA) hiPK), mul3 (c ee) (c sPK) (c lastA),
    mul3 (c ee) (c sPK) (sub (c b) (.add (smul 16 hiPK) loPK)),
    .mul (mul3 (c ee) (c sGP) (c fs)) (sub (c tA) (sum [k 70, two (c Ls), smul 64 (c kt)])),
    .mul (mul3 (c ee) (c sGP) (c fs)) (sub (c symA) (k SYM_END)),
    .mul (mul3 (c ee) (c sGP) (c fs)) (sub (c lastA) (k 1)),
    mul3 (c ee) (c sT0) (sub (c tB) (k 1)), mul3 (c ee) (c sT0) (sub (c symB) (k 2)),
    .mul (mul3 (c ee) (c sSL) (c fs)) (sub (c tB) (.add (k 3) (two (c Ls)))),
    .mul (mul3 (c ee) (c sSL) (c fs)) (sub (c symB) (k 2)),
    mul3 (c ee) (c sS) (sub (c tB) (.add (k 3) (two (c idx)))),
    mul3 (c ee) (c sS) (sub (c symB) loE),
    mul3 (c ee) (c sKT) (sub (c tB) (.add (k 5) (two (c Ls)))),
    mul3 (c ee) (c sKT) (sub (c symB) (c b)),
    mul3 (c ee) (c sPK) (sub (c tB) (sum [k 7, two (c Ls), two (c idx)])),
    mul3 (c ee) (c sPK) (sub (c symB) loPK) ]

theorem keyAccessCurrent_footprint : keyAccessCurrent.all currentExpr=true ∧ keyAccessCurrent.all noEmissionExpr=true := by decide

theorem keyAccessCurrent_in_key : ∀e∈keyAccessCurrent,e∈cKey := by
  intro e he
  simp only [keyAccessCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cKey,List.mem_cons,List.not_mem_nil,or_false]
  grind only

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem receipt_key_access_current (ctx : ApplyCtx) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hi : row.index<fieldLen p.input row.state) :
    ∀e∈keyAccessCurrent,e.eval (receiptPair (booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))))
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists)
        (booleanReceiptAux (characterAux (keyAux accountId accessId fallback)))) p row row) 0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants))))
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists)
    (booleanReceiptAux (characterAux (keyAux accountId accessId fallback)))
  let tr := receiptPair cn aux p row row
  have hfields := keyAux_transport accountId accessId (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))) pub digests (receiptPlanToken ctx lists) (characterAux fallback) p row
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
  have hchars (hv : row.state=sS) : hiE.eval tr 0 0 pub=Fp.ofNat (keyByte p row/16) ∧
      loE.eval tr 0 0 pub=Fp.ofNat (keyByte p row%16) :=
    key_character_nibbles ctx lists (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))) pub digests (keyAux accountId accessId fallback) p row hw (Or.inr hv) hi
  have hee : tr.cell 0 0 ee=bitCell (systemEqual p.input.receipt) :=
    (systemIdentity_cells ctx (keyConstants accountId constants) p).1
  have hls : tr.cell 0 0 Ls=Fp.ofNat p.input.receipt.signerId.length := rfl
  have hkt : tr.cell 0 0 kt=Fp.ofNat p.input.receipt.signerPk.tag := rfl
  have hpk (hp : row.state=sPK) : hiPK.eval tr 0 0 pub=Fp.ofNat (keyByte p row/16) ∧
      loPK.eval tr 0 0 pub=Fp.ofNat (keyByte p row%16) := by
    cases row with
    | mk state i len =>
      dsimp only at hp
      subst state
      exact keyPk_character_nibbles accountId accessId _ pub digests (receiptPlanToken ctx lists) fallback p i len
  have hbp (hp : row.state=sPK) : tr.cell 0 0 b=Fp.ofNat (keyByte p row) :=
    receipt_key_pk_byte cn pub digests (fun p row col => (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterAux (keyAux accountId accessId fallback)))) p row col) p row hp
  have hbt (hp : row.state=sKT) : tr.cell 0 0 b=Fp.ofNat p.input.receipt.signerPk.tag :=
    receipt_key_tag_byte cn pub digests aux p row hp hi
  have hnib := congrArg Fp.ofNat (keyByte_nibbles p row).1
  simp only [ofNat_add_e,ofNat_mul_e,show Fp.ofNat 16=(16:Fp) from rfl] at hnib
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [keyAccessCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_mul,eval_mul3,eval_sub,eval_add,eval_not,eval_k,two,eval_smul,eval_sum_cons,eval_sum_nil,eval_c,
    htA,htB,hsA,hsB,hlA,hidx,hls,hkt,hfs,hee,
    hst sT0 (by decide) (by decide),hst sSL (by decide) (by decide),hst sS (by decide) (by decide),
    hst sKT (by decide) (by decide),hst sPK (by decide) (by decide),hst sGP (by decide) (by decide)]
  all_goals cases heq : systemEqual p.input.receipt
  all_goals by_cases h0 : row.index=0
  all_goals
    have hs : row.state=sT0 ∨ row.state=sSL ∨ row.state=sS ∨ row.state=sKT ∨ row.state=sPK ∨ row.state=sGP ∨
      (row.state≠sT0 ∧ row.state≠sSL ∧ row.state≠sS ∧ row.state≠sKT ∧ row.state≠sPK ∧ row.state≠sGP) := by grind only
    rcases hs with hs|hs|hs|hs|hs|hs|hs
  all_goals try rw [(hchars hs).1]
  all_goals try rw [(hchars hs).2]
  all_goals try rw [(hpk hs).1]
  all_goals try rw [(hpk hs).2]
  all_goals try rw [hbp hs]
  all_goals try rw [hbt hs]
  all_goals simp only [sT0,sSL,sS,sKT,sPK,sGP] at hs
  all_goals simp only [hs,h0,heq,keyState,keyFirst,keyPosA,keyPosB,keySymA,keySymB,keyLast,keyZero,bitCell,
    sV,sVL,sRID,sT0,sSL,sS,sKT,sPK,sGP,ofNat_add_e,ofNat_mul_e,
    Nat.reduceEqDiff,Nat.reduceBEq,decide_true,decide_false,Bool.true_or,Bool.false_or,Bool.or_true,Bool.or_false,
    Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_eq_true,
    beq_iff_eq,ite_true,ite_false,or_true,true_or,or_false,false_or]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 2=(2:Fp) from rfl,show Fp.ofNat 3=(3:Fp) from rfl,show Fp.ofNat 4=(4:Fp) from rfl,show Fp.ofNat 5=(5:Fp) from rfl,show Fp.ofNat 6=(6:Fp) from rfl,show Fp.ofNat 7=(7:Fp) from rfl,show Fp.ofNat 16=(16:Fp) from rfl,show Fp.ofNat 64=(64:Fp) from rfl,show Fp.ofNat 70=(70:Fp) from rfl,show Fp.ofNat SYM_END=(SYM_END:Fp) from rfl]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
