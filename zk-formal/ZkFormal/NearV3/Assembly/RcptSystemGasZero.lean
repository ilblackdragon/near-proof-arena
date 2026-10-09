import ZkFormal.NearV3.Assembly.RcptSystemGasCandidate

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Concrete zero multiplication witnesses for the native system branch. -/
def systemGasZeroCols : List Nat := [pc, burnt, ramt, c2, c3, dl 0, dl 1, dl 2, dl 3, dl 4, dl 5, dl 6, dl 7, xb 9, xb 10, xb 11, xb 12, xb 13, xb 14, xb 15, xb 16, xb 17, xb 18, xb 19, xb 20, xb 21, xb 22, xb 23, xb 24, xb 25, xb 26, xb 27, xb 28, xb 29, xb 30]

def systemGasZeroAux (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if p.input.receipt.predecessorId=AccountId.system ∧ row.state=sGP ∧ col∈systemGasZeroCols
  then 0 else fallback p row col

theorem systemGasZero_cell (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len col : Nat)
    (hs : p.input.receipt.predecessorId=AccountId.system) (hc : col∈systemGasZeroCols) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (systemGasZeroAux fallback)))
      p ⟨sGP,i,len⟩ col=0 := by
  simp only [systemGasZeroCols,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (pc) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (pc))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (burnt) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (burnt))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (ramt) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (ramt))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (c2) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (c2))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (c3) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (c3))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 0) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 0))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 1) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 1))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 2) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 2))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 3) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 3))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 4) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 4))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 5) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 5))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 6) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 6))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (dl 7) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (dl 7))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 9) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 9))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 10) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 10))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 11) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 11))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 12) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 12))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 13) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 13))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 14) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 14))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 15) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 15))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 16) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 16))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 17) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 17))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 18) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 18))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 19) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 19))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 20) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 20))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 21) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 21))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 22) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 22))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 23) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 23))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 24) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 24))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 25) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 25))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 26) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 26))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 27) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 27))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 28) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 28))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 29) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 29))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]
  · change boolInput (xb 30) (systemGasZeroAux fallback p ⟨sGP,i,len⟩ (xb 30))=0
    simp [systemGasZeroAux,hs,systemGasZeroCols,boolInput]

def gasProductConstraints (surplus : Expr) : List Expr :=
  (gasConstraintsWith surplus).drop 6 |>.take 10

theorem system_gas_product_local (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) (hi : i<16)
    (hs : p.input.receipt.predecessorId=AccountId.system)
    (next : Coord) (hn : i+1<16→next=⟨sGP,i+1,16⟩) :
    ∀e∈gasProductConstraints systemSurplus,e.eval
      (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (systemGasZeroAux fallback)))
        p ⟨sGP,i,16⟩ next) 0 0 pub=0 := by
  let cn := booleanConstants (gasEffectiveConstants ctx constants)
  let aux := tokenReceiptAux pub digests tokens (booleanReceiptAux (systemGasZeroAux fallback))
  let tr := receiptPair cn aux p ⟨sGP,i,16⟩ next
  have hz (col : Nat) (hc : col∈systemGasZeroCols) : tr.cell 0 0 col=0 :=
    systemGasZero_cell (gasEffectiveConstants ctx constants) pub digests tokens fallback p i 16 col hs hc
  have hgq : tr.cell 0 0 gq=0 := by
    change boolInput gq (bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice) &&
      !(p.input.receipt.predecessorId==AccountId.system)))=0
    simp [hs,bitCell,boolInput]
  have hsur := systemSurplus_zero tr 0 0 pub hgq
  have z0 := hz (pc) (by decide)
  have z1 := hz (burnt) (by decide)
  have z2 := hz (ramt) (by decide)
  have z3 := hz (c2) (by decide)
  have z4 := hz (c3) (by decide)
  have z5 := hz (dl 0) (by decide)
  have z6 := hz (dl 1) (by decide)
  have z7 := hz (dl 2) (by decide)
  have z8 := hz (dl 3) (by decide)
  have z9 := hz (dl 4) (by decide)
  have z10 := hz (dl 5) (by decide)
  have z11 := hz (dl 6) (by decide)
  have z12 := hz (dl 7) (by decide)
  have z13 := hz (xb 9) (by decide)
  have z14 := hz (xb 10) (by decide)
  have z15 := hz (xb 11) (by decide)
  have z16 := hz (xb 12) (by decide)
  have z17 := hz (xb 13) (by decide)
  have z18 := hz (xb 14) (by decide)
  have z19 := hz (xb 15) (by decide)
  have z20 := hz (xb 16) (by decide)
  have z21 := hz (xb 17) (by decide)
  have z22 := hz (xb 18) (by decide)
  have z23 := hz (xb 19) (by decide)
  have z24 := hz (xb 20) (by decide)
  have z25 := hz (xb 21) (by decide)
  have z26 := hz (xb 22) (by decide)
  have z27 := hz (xb 23) (by decide)
  have z28 := hz (xb 24) (by decide)
  have z29 := hz (xb 25) (by decide)
  have z30 := hz (xb 26) (by decide)
  have z31 := hz (xb 27) (by decide)
  have z32 := hz (xb 28) (by decide)
  have z33 := hz (xb 29) (by decide)
  have z34 := hz (xb 30) (by decide)
  have hb9 : (bitsX 9 11).eval tr 0 0 pub=0 := by
    simp [bitsX,bits,List.range_succ,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34]
    grind only
  have hb20 : (bitsX 20 11).eval tr 0 0 pub=0 := by
    simp [bitsX,bits,List.range_succ,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34]
    grind only
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hnz (h : i+1<16) (col : Nat) (hc : col∈systemGasZeroCols) :
      tr.cell 0 ((0+1)%(tr.height 0)) col=0 := by
    change receiptCell cn aux p next col=0
    rw [hn h]
    exact systemGasZero_cell _ _ _ _ _ p (i+1) 16 col hs hc
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [gasProductConstraints,gasConstraintsWith] at he
  change e∈[_,_,_,_,_,_,_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [conv,G_LE,List.range_succ,ovf,eval_mul3,eval_mul,eval_add,eval_sub,
    eval_sum_cons,eval_sum_nil,eval_smul,eval_c,eval_n,eval_not,hsur,hb9,hb20,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34,hfe]
  all_goals try grind only
  all_goals by_cases he : i+1=16
  all_goals try simp only [he,ite_true,ite_false]
  all_goals try grind only
  all_goals have hcn2 := hnz (by omega) c2 (by decide)
  all_goals have hcn3 := hnz (by omega) c3 (by decide)
  all_goals simp only [hcn2,hcn3]
  all_goals grind only

theorem gasProductConstraints_length (surplus : Expr) : (gasProductConstraints surplus).length=10 := rfl

theorem systemGasZero_ordinary (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hs : p.input.receipt.predecessorId≠AccountId.system) :
    systemGasZeroAux fallback p row col=fallback p row col := by
  simp [systemGasZeroAux,hs]

theorem systemGasZero_outside (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) (hc : col∉systemGasZeroCols) :
    systemGasZeroAux fallback p row col=fallback p row col := by
  simp [systemGasZeroAux,hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
