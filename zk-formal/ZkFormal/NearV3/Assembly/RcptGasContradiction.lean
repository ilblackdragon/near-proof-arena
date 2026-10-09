import ZkFormal.NearV3.Assembly.RcptSystemGasDomain
import ZkFormal.NearV3.Rcpt.Extract.V.GasProduct

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RcptV3Proof
open ZkFormal.Near.RcptProof (sumL sumL_lt sumL_congr)

/-- The original surplus overflow gate forbids a nonzero top difference byte,
even when system mode disables actual refunds. No ramt byte-range premise. -/
theorem old_gas_surplus_top_zero {tr : Trace Fp} {pub : List Fp} {tt s : Nat}
    {h : Bool} {Lp Lv Ls kt : Nat} (hL : TableLocal RcptV3.table tr tt pub)
    (lay : Layout tr tt s h Lp Lv Ls kt) : SN tr tt s Lp Lv Ls kt 15=0 := by
  obtain ⟨hq,hgp,_,hfe,_⟩ := gp_row hL lay 15 (by decide)
  have co := con hL hq (e:=mul3 gp (c fe) (ovf surE (fun j=>c (dl (4+j))))) (mem_gs (by simp [cGas]))
  have hx := (pE_eval hL lay 15 (by decide)).2
  have hd (j : Nat) (hj : j<3) :
      tr.cell tt (RcptV3Proof.gq s Lp Lv Ls kt 15) (dl (4+j))=
        ((SN tr tt s Lp Lv Ls kt (14-j):Nat):Fp) := by
    rw [(dl_eval hL lay 15 (by decide) j (by omega)).2,if_pos (by omega)]
  simp only [gp,ovf,eval_mul3,eval_c,eval_sum_cons,eval_sum_nil,eval_smul] at co
  rw [hgp,hfe,if_pos rfl,hx,hd 0 (by decide),hd 1 (by decide),hd 2 (by decide)] at co
  have h15 := SN_lt hL lay 15 (by decide)
  have h14 := SN_lt hL lay 14 (by decide)
  have h13 := SN_lt hL lay 13 (by decide)
  have h12 := SN_lt hL lay 12 (by decide)
  have hn : (164+183+246+51)*SN tr tt s Lp Lv Ls kt 15+
      (183+246+51)*SN tr tt s Lp Lv Ls kt 14+
      (246+51)*SN tr tt s Lp Lv Ls kt 13+51*SN tr tt s Lp Lv Ls kt 12=0 := by
    apply nat_of_fp (by unfold ZkFormal.Algebra.P;omega) (by unfold ZkFormal.Algebra.P;omega)
    simp only [natCast_add,natCast_mul]
    grind only
  omega

/-- No locally valid original receipt table can represent u128Max gas price
against a zero block price, including a native-valid system receipt. -/
theorem old_gas_max_price_impossible {tr : Trace Fp} {pub : List Fp} {tt s : Nat}
    {h : Bool} {Lp Lv Ls kt : Nat} (hL : TableLocal RcptV3.table tr tt pub)
    (lay : Layout tr tt s h Lp Lv Ls kt)
    (hgp : ∀i,i<16→cv tr tt (RcptV3Proof.gq s Lp Lv Ls kt i) b=255)
    (hbg : ∀i,i<16→pubNat pub (PH_GP+i)=0) : False := by
  let D := fun i=>bvN tr tt (RcptV3Proof.gq s Lp Lv Ls kt i) 0 8
  have hd (i : Nat) (hi : i<16) : D i<256 :=
    (bitsX_eval hL (gp_row hL lay i hi).1 0 8 (by decide)).2
  have he := gp_borrow hL lay (fun i hi=>by rw [hgp i hi];decide)
    (fun i hi=>by rw [hbg i hi];decide)
  rw [sumL_congr _ (fun _=>255) 16 hgp,sumL_congr _ (fun _=>0) 16 hbg] at he
  have hmax : sumL (fun _=>255) 16=Params.u128Max := by decide
  have hzero : sumL (fun _=>0) 16=0 := by decide
  rw [hmax,hzero,Nat.zero_add] at he
  have hdl := sumL_lt D 16 hd
  have hge := ge_bool hL lay
  have hg : cv tr tt s ge=1 := by
    change Params.u128Max+256^16*(1-cv tr tt s ge)=sumL D 16 at he
    simp only [Params.u128Max,Nat.reducePow] at he hdl
    omega
  have hz := old_gas_surplus_top_zero hL lay
  simp only [SN,hg,ite_true] at hz
  change D 15=0 at hz
  have hprefix := sumL_lt D 15 (fun i hi=>hd i (by omega))
  change Params.u128Max+256^16*(1-cv tr tt s ge)=sumL D 16 at he
  rw [hg] at he
  rw [show 16=15+1 from rfl, sumL] at he
  rw [hz] at he
  simp only [Params.u128Max,Nat.reducePow] at he hprefix
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
