import ZkFormal.NearV3.Assembly.RcptGasEffectiveFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasEffectiveConstraints : List Expr :=
  [ .mul gp (sub (c pc) (.mul (Dsl.not (c sys)) pE)),
    .mul rowE (sub (c gq) (.mul (c ge) (Dsl.not (c sys)))) ]

theorem gasEffectiveConstraints_footprint :
    gasEffectiveConstraints.all currentExpr=true ∧ gasEffectiveConstraints.all noEmissionExpr=true := by decide

theorem gasEffectiveConstraints_mem : ∀e∈gasEffectiveConstraints,e∈cGas := by
  intro e he
  simp only [gasEffectiveConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> simp [cGas]

theorem receipt_gasEffective_local (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hi : row.index<fieldLen p.input row.state) :
    ∀e∈gasEffectiveConstraints,e.eval (receiptPair
      (booleanConstants (nativePriceConstants ctx (systemConstants (gasEffectiveConstants ctx constants))))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasEffectiveAux ctx fallback))) p row row) 0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants (gasEffectiveConstants ctx constants)))
  let aux := tokenReceiptAux pub digests tokens (booleanReceiptAux (gasEffectiveAux ctx fallback))
  let tr := receiptPair cn aux p row row
  have hf := gasEffective_constant_cells ctx constants p
  have hge : tr.cell 0 0 ge=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice)) := hf.1
  have hsys : tr.cell 0 0 sys=bitCell (p.input.receipt.predecessorId==AccountId.system) := hf.2.1
  have hq : tr.cell 0 0 gq=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice) && !(p.input.receipt.predecessorId==AccountId.system)) := hf.2.2
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [gasEffectiveConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · by_cases hs : row.state=sGP
    · have hi' : row.index<16 := by rw [hs] at hi;exact hi
      have hh := receipt_gas_price_bytes ctx cn pub hpub digests (tokenAux tokens (booleanReceiptAux (gasEffectiveAux ctx fallback))) p row.index row.length hi'
      have hb : tr.cell 0 0 b=Fp.ofNat (gasByte p.input.receipt.gasPrice row.index) := by
        cases row with
        | mk state i len => dsimp only at hs;subst state;exact hh.1
      have hreg : tr.cell 0 0 (reg 0)=Fp.ofNat (gasByte ctx.gasPrice row.index) := by
        cases row with
        | mk state i len => dsimp only at hs;subst state;exact hh.2
      have hpc : tr.cell 0 0 pc=Fp.ofNat (gasEffectiveByte ctx p.input.receipt row.index) := by
        cases row with
        | mk state i len => dsimp only at hs;subst state;exact gasEffective_cell ctx (nativePriceConstants ctx (systemConstants (gasEffectiveConstants ctx constants))) pub digests tokens fallback p i len
      simp only [eval_mul,eval_sub,eval_not,eval_c,pE,eval_add,hpc,hsys,hge,hreg,hb]
      have hn := gasPrice_selected_byte ctx p.input.receipt row.index
      by_cases hg : ctx.gasPrice≤p.input.receipt.gasPrice
      all_goals cases hsys' : p.input.receipt.predecessorId==AccountId.system
      all_goals simp only [hg,ite_true,ite_false] at hn
      all_goals simp only [gasEffectiveByte,hsys',hg,bitCell,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,show Fp.ofNat 0=(0:Fp) from rfl]
      all_goals try rw [←hn]
      all_goals grind only
    · have hz : tr.cell 0 0 sGP=0 := by
        apply (receipt_control_cell cn aux p row (show controlColumn sGP=true by decide)).trans
        rw [control_state row (show sGP∈states by decide),if_neg (Ne.symm hs)]
      simp only [gp,eval_mul,eval_c,hz]
      grind only
  · simp only [eval_mul,eval_sub,eval_not,eval_c,hq,hge,hsys,gasEffective_gate]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
