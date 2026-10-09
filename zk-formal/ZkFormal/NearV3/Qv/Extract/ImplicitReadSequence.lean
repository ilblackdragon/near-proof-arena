import ZkFormal.NearV3.Qv.Extract.MainQueueReads

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (tau)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
include hL

theorem last_queue_tau_public (hpos : 0<q.segs.length) :
    cv tr tt (q.segs[q.segs.length-1]'(by omega)).1 tau=(kPublic.eval tr tt 0 pub).toNat := by
  have hj : q.segs.length-1<q.segs.length := by omega
  have hp := q.valid _ (List.getElem_mem hj)
  have hfit := Nat.le_trans (seg_le_end q.segs 0 q.consecutive _ (List.getElem_mem hj)).2 q.fits
  have he := segEnd_last q.segs 0 q.consecutive hpos
  have hrow : segEnd 0 q.segs-1<tr.height tt := by have := hp.1; omega
  have hterm := (order_termination hL hrow (q.final_end hL)).1
  have hmeta := walk_metadata hL hfit hp (x:=tau) (by simp)
    (segEnd 0 q.segs-1) (by have := hp.1; omega) (by have := hp.1; omega)
  have hpub : kPublic.eval tr tt (segEnd 0 q.segs-1) pub=kPublic.eval tr tt 0 pub := rfl
  rw [hmeta,hpub] at hterm
  exact congrArg Fp.toNat hterm

/-- Exactly K implicit requests follow the final main request, including K=0. -/
theorem implicit_request_count (last : Nat) (hlast : last<q.segs.length)
    (hf : tr.cell tt q.segs[last].1 lastMain=1) :
    q.segs.length=last+1+(kPublic.eval tr tt 0 pub).toNat := by
  have hpos : 0<q.segs.length := by omega
  have hfinal := last_queue_tau_public hL q hpos
  by_cases hn : last+1<q.segs.length
  · obtain ⟨hm,ht⟩ := (WalkChain.indexed_order hL q last hn).2.1 hf
    have hc := WalkChain.implicit_counter_nat hL q (last+1) (q.segs.length-1)
      hn (by omega) (by omega) hm ht
    rw [hc] at hfinal
    omega
  · have he : q.segs.length-1=last := by omega
    have hm := (WalkChain.last_main_shape hL q last hlast hf).1
    have hc := main_tau_zero hL (q.start_lt last hlast) hm
    simp only [he] at hfinal
    rw [hc] at hfinal
    omega

/-- Each implicit ordinal exists once, in transition order, and carries its
ordinary transition counter rather than a caller-supplied instance hint. -/
theorem implicit_request_at (last t : Nat) (hlast : last<q.segs.length)
    (hf : tr.cell tt q.segs[last].1 lastMain=1)
    (ht : 1≤t) (hK : t≤(kPublic.eval tr tt 0 pub).toNat) :
    ∃ hi : last+t<q.segs.length,
      tr.cell tt (q.segs[last+t]'hi).1 main=0 ∧ cv tr tt (q.segs[last+t]'hi).1 tau=t := by
  have hc := implicit_request_count hL q last hlast hf
  have hi : last+t<q.segs.length := by omega
  have hn : last+1<q.segs.length := by omega
  obtain ⟨hm,hfirst⟩ := (WalkChain.indexed_order hL q last hn).2.1 hf
  refine ⟨hi,WalkChain.implicit_suffix hL q (last+1) (last+t) hn hi (by omega) hm,?_⟩
  have hv := WalkChain.implicit_counter_nat hL q (last+1) (last+t) hn hi (by omega) hm hfirst
  rw [hv]
  omega

/-- Every native missing-chunk delayed read is available at its own transition
head. Raw mode permits any present value as well as absence. -/
theorem implicit_queue_reads (vs : List NodeS3) (es : List ValE) (hs : List HeadE)
    (hread : ∀ i (hi : i<q.segs.length),
      (queueTree vs es hs (cv tr tt (q.segs[i]'hi).1 tau)).find
        (NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))=
        some (queueValue vs es tr tt (q.segs[i]'hi).1)) :
    ∀ t, 1≤t → t≤(kPublic.eval tr tt 0 pub).toNat →
      (missingRequest (queueTree vs es hs t)).Holds (queueTree vs es hs t) := by
  obtain ⟨last,hlast,hf⟩ := WalkChain.last_main_exists hL q
  intro t ht hK
  obtain ⟨hi,hm,hct⟩ := implicit_request_at hL q last t hlast hf ht hK
  have hr := hread (last+t) hi
  rw [hct,implicit_fixed_key hL q _ (List.getElem_mem hi) hm] at hr
  simp [missingRequest,ReadRequest.Holds,ParseMode.Accepts,hr]

end ZkFormal.NearV3.Qv.Extract
