import ZkFormal.NearV3.Assembly.RcptGasTokenFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasAccumulatorConstraints : List Expr := (cGas.drop 16).take 4

theorem receipt_gasToken_local (tokens : ReceiptPlan→TokenInput)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) (hi : i<16)
    (hb : (tokens p).before+(tokens p).burnt<256^16)
    (next : Coord) (hn : i+1<16→next=⟨sGP,i+1,16⟩) :
    ∀e∈gasAccumulatorConstraints,e.eval
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)))
        p ⟨sGP,i,16⟩ next) 0 0 pub=0 := by
  let tr := receiptPair (booleanConstants constants)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback))) p ⟨sGP,i,16⟩ next
  have hg : tr.cell 0 0 sGP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have ht : tr.cell 0 0 (tok 0)=Fp.ofNat (gasByte (tokens p).before i) := by
    rw [show tr.cell 0 0 (tok 0)=Fp.ofNat ((tokenOf (tokens p) ⟨sGP,i,16⟩ 0).toNat) from
      receipt_token_cell (booleanConstants constants) pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)) p ⟨sGP,i,16⟩ 0 (by decide),gasToken_old_head (tokens p) i hi]
  have hburn : tr.cell 0 0 burnt=Fp.ofNat (gasByte (tokens p).burnt i) := rfl
  have hcarry : tr.cell 0 0 c4=Fp.ofNat (gasTokenCarry (tokens p) i) := rfl
  have hcarry' : tr.cell 0 0 (xb 39)=Fp.ofNat (gasTokenCarry (tokens p) (i+1)) :=
    gasToken_next_carry_cell tokens constants pub digests fallback p i 16
  have hnew : (bitsX 31 8).eval tr 0 0 pub=Fp.ofNat (gasByte ((tokens p).before+(tokens p).burnt) i) :=
    gasToken_new_eval tokens constants pub digests fallback p i next
  have hnCarry (h : i+1<16) : tr.cell 0 ((0+1)%tr.height 0) c4=Fp.ofNat (gasTokenCarry (tokens p) (i+1)) := by
    change receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback))) p next c4=_
    rw [hn h]
    rfl
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  · simp only [gp,eval_mul,eval_sub,eval_add,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,hg,ht,hburn,hcarry,hcarry',hnew]
    have hh := congrArg Fp.ofNat (gasToken_step (tokens p) hb i hi)
    simp only [ZkFormal.Near.Render.RcptP.ofNat_add_e,ZkFormal.Near.Render.RcptP.ofNat_mul_e] at hh
    change _+_+_=_+(256:Fp)*_ at hh
    grind only
  · simp only [gp,eval_mul,eval_c,hg,hfs,hcarry]
    by_cases hz : i=0
    · subst i
      simp only [ite_true,gasTokenCarry_zero]
      change (1:Fp)*1*0=0
      grind only
    · rw [if_neg hz];grind only
  · simp only [gp,eval_mul3,eval_not,eval_sub,eval_n,eval_c,hg,hfe,hcarry']
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnCarry (by omega)];grind only
  · simp only [gp,eval_mul3,eval_c,hg,hfe,hcarry']
    by_cases he : i+1=16
    · rw [if_pos he,he,gasTokenCarry_final (tokens p) hb]
      change (1:Fp)*1*0=0
      grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
