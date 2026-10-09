import ZkFormal.NearV3.Assembly.RcptCandidateKeyTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptIds
import ZkFormal.NearV3.Rcpt.Link.Keynib
namespace ZkFormal.NearV3.Candidates.ProcPriorReceiptKeySymbols
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open RcptV3 RcptV3Proof Assembly.RcptSkeleton Assembly.ReceiptCandidateProof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem public_byte {tr:Trace Fp} {pub:List Fp} {tt q:Nat}
    (hL:TableLocal receiptArithmeticCandidate tr tt pub) (hq:q<tr.height tt)
    (hs:tr.cell tt q sPK=1) (he:tr.cell tt q ee=1) : cv tr tt q b<256 := by
  obtain ⟨hh,hhl⟩:=bitsX_eval hL hq 0 4 (by omega)
  obtain ⟨hl,hll⟩:=bitsX_eval hL hq 4 4 (by omega)
  have hb:=((akey_row hL hq he).2.2.2.2.1 hs).2.2.2.2.2
  change hiPK.eval tr tt q pub=_ at hh
  change loPK.eval tr tt q pub=_ at hl
  let hi:=bitsVal (fun j=>cv tr tt q (xb j)) 0 4
  let lo:=bitsVal (fun j=>cv tr tt q (xb j)) 4 4
  have hiLt:hi<16:=hhl
  have loLt:lo<16:=hll
  have hv:tr.cell tt q b=((16*hi+lo:Nat):Fp):=by
    rw [hb,hh,hl,natCast_add,natCast_mul]
    change 16*(hi:Fp)+(lo:Fp)=((16:Nat):Fp)*(hi:Fp)+(lo:Fp)
    rw [show ((16:Nat):Fp)=(16:Fp) by decide]
  rw [cv,hv,toNat_natCast,Nat.mod_eq_of_lt (by unfold P;omega)]
  omega

theorem public_bytes {tr:Trace Fp} {pub:List Fp} {tt:Nat}
    (hL:TableLocal receiptArithmeticCandidate tr tt pub) {y:RS}
    (lay:Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (he:(rcptOf tr tt y).ee=true) : Bytes8 (rcptOf tr tt y).pk := by
  have he0:tr.cell tt y.s ee=1:=by simpa only [rcptOf,decide_eq_true_eq] using he
  have hm:(sPK,46+y.Lp+y.Lv+y.Ls,32+32*y.kt)∈plan y.h y.Lp y.Lv y.Ls y.kt:=by simp [plan]
  have hf:=lay.flds _ hm
  have hfin:=lay.fin
  have hle:=Assembly.ReceiptCandidateProof.plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  intro x hx
  change x∈colAt tr tt (y.s+(46+y.Lp+y.Lv+y.Ls)) (32+32*y.kt) b at hx
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hx
  have hk:=List.mem_range.mp hk
  exact public_byte hL (by omega) (hf.fld.st k hk)
    ((hf.consts k hk ee (by simp [rconsts])).trans he0)

theorem receipt_symbols {tr:Trace Fp} {pub:List Fp} {tt:Nat}
    (hL:TableLocal receiptArithmeticCandidate tr tt pub) {y:RS}
    (lay:Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (rN:Nat) :
    ∀m∈Assembly.ReceiptCandidateProof.keyReceiptMsgs rN (rcptOf tr tt y),
      m.getD 2 0<P ∧ (m.getD 2 0<16 ∨ m.getD 2 0=SYM_END) := by
  have hids:=ids_of hL lay
  apply rcpt_keynib_syms _ _ hids.2.2.2.2.1
  intro he
  exact ⟨hids.2.2.2.2.2,public_bytes hL lay he,by change y.kt<256;have:=lay.kt1;omega⟩
theorem chain_symbols {tr:Trace Fp} {pub:List Fp} {tt e:Nat}
    (hL:TableLocal receiptArithmeticCandidate tr tt pub) {bs:List ListBlock}
    (hc:ListChain tr tt 0 bs e) :
    ∀m∈rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_KEYNIB,
      m.getD 2 0<P ∧ (m.getD 2 0<16 ∨ m.getD 2 0=SYM_END) := by
  rw [←Assembly.ReceiptCandidateProof.keyReceiptMsgs_view]
  intro m hm
  unfold Assembly.ReceiptCandidateProof.indexedReceiptMsgs at hm
  obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hm
  have hj:=List.mem_range.mp hj
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] at hm
  obtain ⟨k,hk,hm⟩:=List.mem_flatMap.mp hm
  have hk:=List.mem_range.mp hk
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] at hm
  have hy:=(hc.blocks _ (List.getElem_mem hj)).layouts _ (List.getElem_mem hk)
  exact receipt_symbols hL hy _ m hm
end ZkFormal.NearV3.Candidates.ProcPriorReceiptKeySymbols
