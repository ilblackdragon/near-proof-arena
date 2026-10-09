import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractBlockSize

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3

/-- The semantic traffic contract of an extracted candidate source sequence.
Only root repetition metadata is still read from its trace; public SRC matching
must bind that metadata to prepared keys before concluding source semantics. -/
def sourceMsgs (tr : Trace Fp) (tt : Nat) (bs : List SrcpB) (bb : Nat) (sd : Bool) : List Msg :=
  if bb=B_SIZE then
    if sd then [[2, (bs.map fun B => B.L+33*B.path.length).sum]] else []
  else chainMsgs tr tt 0 bs bb sd

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem BlockChain.all_traffic {e : Nat} {bs : List SrcpB} (h : BlockChain tr tt 0 bs e)
    (bb : Nat) (sd : Bool) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub bb sd) =
      (sourceMsgs tr tt bs bb sd).map Msg.toFp := by
  by_cases hb : bb=B_SIZE
  · subst bb
    cases sd
    · simpa [sourceMsgs] using (h.size_traffic hL).2
    · simpa [sourceMsgs] using (h.size_traffic hL).1
  · simpa only [sourceMsgs, hb, ite_false] using h.full_traffic hL bb hb sd

/-- Complete combinatorial extraction from arbitrary logical candidate AIR.
No byte-range, SHA correctness, public-source matching, or global size-bound
assumption is hidden here; those remain explicit semantic assembly obligations. -/
theorem extract_source : ∃ bs : List SrcpB,
    bs≠[] ∧ DedupRender.R bs≤tr.height tt ∧
    (∀ i (hi : i<bs.length), bs[i].j=i) ∧
    (∀ hb : 0<bs.length, bs[0].ql=1) ∧
    (∀ i (hi : i+1<bs.length), bs[i+1].ql=bs[i].qe+1) ∧
    (∀ B∈bs, if B.dup then B.L=12 ∧ B.path=[] ∧ B.le=0 ∧ B.qe+1=B.ql else BlockWf B) ∧
    (∀ bb sd, (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub bb sd) =
      (sourceMsgs tr tt bs bb sd).map Msg.toFp) := by
  obtain ⟨bs, e, hc⟩ := extract_blocks hL
  refine ⟨bs, hc.nonempty, ?_, ?_, ?_, hc.q_next hL, hc.local hL, hc.all_traffic hL⟩
  · have he := hc.bound
    have hr := hc.rows
    omega
  · intro i hi
    have hh := hc.j_indices hL i hi
    rw [(row0 hL).2.1] at hh
    simpa only [show Fp.toNat 0=0 from rfl, Nat.zero_add] using hh
  · intro hb
    have hh := hc.q_start hL hb
    rw [(row0 hL).2.2.1] at hh
    simpa only [show Fp.toNat 0=0 from rfl, Nat.zero_add] using hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
