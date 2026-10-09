import ZkFormal.NearV3.Candidates.ProcPriorCodecGridHeader
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem header_constant (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) (x:Nat)
    (hx:x∈[tau,pres,vid,nn,NN,base,fair]) :
    ∀j,j<5→cv tr t (f+j) x=cv tr t f x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    obtain ⟨hb,hH,hp⟩:=ProcPriorCodecGridHeader.header hL hf hF (j+1) hj
    have K:=kinds hL hb
    have hF0:cv tr t (f+(j+1)) kF=0:=by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp K.2.2.2.2.2.1 with h|h
      · exact h
      · have hh:=ProcPriorCodecGridHeader.first hL hb h
        omega
    have hc:=ProcPriorCodecSoundOrigin.constant_next hL x hx
      (r:=f+j) (by simpa [Nat.add_assoc] using hb)
      (by simpa [Nat.add_assoc] using (show cv tr t (f+(j+1)) act=1 by omega))
      (by simpa [Nat.add_assoc] using hF0)
    simpa [Nat.add_assoc] using hc.trans (ih (by omega))

theorem first_constants (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) (x:Nat)
    (hx:x∈[tau,pres,vid,nn,NN,base,fair]) :
    cv tr t (f+5) x=cv tr t f x := by
  obtain ⟨hb,hs,_⟩:=ProcPriorCodecGridHeader.first_record hL hf hF
  have hS:=(ProcPriorCodecSoundGeometry.start hL hb hs).1
  have K:=kinds hL hb
  have hc:=ProcPriorCodecSoundOrigin.constant_next hL x hx
    (r:=f+4) (by omega)
    (by simpa only [show f+4+1=f+5 by omega] using (show cv tr t (f+5) act=1 by omega))
    (by simpa only [show f+4+1=f+5 by omega] using (show cv tr t (f+5) kF=0 by omega))
  rw [show f+4+1=f+5 by omega] at hc
  exact hc.trans (header_constant hL hf hF x hx 4 (by decide))

/-- The complete actual corrected Codec grid, without old-local or generated-row premises. -/
theorem records (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) (hN:cv tr t f NN≤4096) :
    ∀k,k<cv tr t f NN→f+5+24*k<tr.height t ∧ cv tr t (f+5+24*k) rs=1 ∧
      cv tr t (f+5+24*k) kidx=k ∧
      ∀x∈[tau,pres,vid,nn,NN,base,fair],cv tr t (f+5+24*k) x=cv tr t f x := by
  obtain ⟨hb,hs,hk⟩:=ProcPriorCodecGridHeader.first_record hL hf hF
  have hn:=first_constants hL hf hF NN (by simp)
  intro k hkn
  obtain ⟨hbr,hsr,hkr,hcr⟩:=ProcPriorCodecGridRecords.records hL hb hs hk (by omega) k (by omega)
  exact ⟨hbr,hsr,hkr,fun x hx=>(hcr x hx).trans (first_constants hL hf hF x hx)⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridComplete
