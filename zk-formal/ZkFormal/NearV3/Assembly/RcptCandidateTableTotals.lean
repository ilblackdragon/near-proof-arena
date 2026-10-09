import ZkFormal.NearV3.Assembly.RcptCandidateTableTokens
-- Source TableTotals.lean SHA256: c7b3957d0bdfb90b3610142129a5ebf0cbbd57eb4df650e7a38c19c65798d142.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.TableTokens

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- At the terminal row, rowE counts exactly the final receipt, if present. -/
theorem ListBlockWf.terminal_rowE {B : ListBlock} (h : ListBlockWf tr tt B) :
    rowE.eval tr tt (B.stop-1) pub=tr.cell tt (B.stop-1) rl := by
  cases he : B.receipts with
  | nil =>
    have hs : B.stop-1=B.start+11 := by simp [ListBlock.stop,he,segsOf,segEnd]
    have ha := h.header.act 11 (by omega)
    have hc := h.header.st 11 (by omega)
    have hr := (ListBlockWf.header_end hL h).2.2.1
    simp only [hs,rowE,eval_sub,eval_c,ha,hc,hr]
    grind
  | cons y ys =>
    obtain ⟨z,hz,hend⟩ := receipt_sequence_last B.receipts (B.start+12) (by simp [he])
    change B.stop=z.s+z.tot at hend
    have hz' := h.layouts z hz
    have ht : 0<z.tot := by unfold RS.tot total; split <;> omega
    have hf := Layout.row_flags hL hz' (z.tot-1) (by omega)
    have hr : tr.cell tt (z.s+z.tot-1) rl=1 := hz'.endRl
    rw [show z.s+(z.tot-1)=z.s+z.tot-1 by omega] at hf
    simp only [hend,rowE,eval_sub,eval_c,hf.1,hf.2,hr]
    grind

/-- Terminal global receipt count across every extracted list. -/
theorem ListChain.terminal_count {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    tr.cell tt (e-1) RcptV3.r+rowE.eval tr tt (e-1) pub=
      tr.cell tt s RcptV3.r+(((bs.map fun B => B.receipts.length).sum:Nat):Fp) := by
  induction h with
  | last hw _ =>
    rw [ListBlockWf.terminal_rowE hL hw,ListBlockWf.terminal_global_count hL hw]
    simp
  | @cons B tail stop hw ht ih =>
    obtain ⟨C,hs,hc⟩ := ht.first_wf
    have hn := ListBlockWf.next_global_count hL hw hc hs
    rw [hs] at hn
    rw [ih,hn]
    simp only [List.map_cons,List.sum_cons,natCast_add]
    grind

/-- Terminal global body position across every extracted list. -/
theorem ListChain.terminal_body {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    tr.cell tt (e-1) o2End=tr.cell tt s o2+(((bs.map fun B => B.refundBytes tr tt).sum:Nat):Fp) := by
  induction h with
  | last hw _ =>
    rw [ListBlockWf.body_end hL hw]
    simp
  | @cons B tail stop hw ht ih =>
    obtain ⟨C,hs,hc⟩ := ht.first_wf
    have hn := ListBlockWf.next_body_offset hL hw hc hs
    rw [hs] at hn
    rw [ih,hn]
    simp only [List.map_cons,List.sum_cons,natCast_add]
    grind

/-- Actual end constraints bind both global totals in the field. Natural decoding
requires public and extracted totals below the characteristic. -/
theorem ListChain.final_totals {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    nPubE.eval tr tt (e-1) pub=(((bs.map fun B => B.receipts.length).sum:Nat):Fp) ∧
    blenE.eval tr tt (e-1) pub=((8+(bs.map fun B => B.refundBytes tr tt).sum:Nat):Fp) := by
  obtain ⟨he,hH,hl⟩ := ListChain.last_row hL h
  have hc := con hL (r:=e-1) (by omega)
    (e:=.mul (c lastR) (sub (.add (c RcptV3.r) rowE) nPubE)) (mem_en (by simp [cEnd]))
  have hb := con hL (r:=e-1) (by omega)
    (e:=.mul (c lastR) (sub (c o2End) blenE)) (mem_en (by simp [cEnd]))
  simp only [eval_mul,eval_sub,eval_add,eval_c,hl] at hc hb
  have hz := first0 hL (by omega : 0<tr.height tt)
  have hn := ListChain.terminal_count hL h
  have ho := ListChain.terminal_body hL h
  rw [hz.2.1] at hn
  rw [hz.2.2] at ho
  rw [natCast_add]
  grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
