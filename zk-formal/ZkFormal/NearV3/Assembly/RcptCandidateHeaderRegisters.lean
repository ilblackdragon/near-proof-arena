import ZkFormal.NearV3.Assembly.RcptCandidateListView
-- Source HeaderRegisters.lean SHA256: e46fa00ad3d8eb2270c5be897e01a45978ec8380f2b1a1f4de98a683fe85c031.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ListView

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Header registers shift under the same active-field constraint as receipt fields. -/
theorem ListBlockWf.header_shift {B : ListBlock} (h : ListBlockWf tr tt B)
    (k : Nat) (hk : k<12) (i : Nat) (hi : i+k<32) :
    tr.cell tt (B.start+k) (reg i)=tr.cell tt B.start (reg (i+k)) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    have hf := h.header
    have hfin := h.header_fin
    have he : tr.cell tt (B.start+k) fe=0 := by
      rw [hf.fe k (by omega),if_neg (by omega)]
    rw [show B.start+(k+1)=B.start+k+1 by omega,
      reg_shift hL (by omega) (hf.act k (by omega)) he i (by omega),
      ih (by omega) (i+1) (by omega),show i+1+k=i+(k+1) by omega]

/-- The first eight header registers equal the public own-shard bytes. -/
theorem ListBlockWf.header_own {B : ListBlock} (h : ListBlockWf tr tt B)
    (k : Nat) (hk : k<8) : tr.cell tt B.start (reg k)=pub.getD (PH_OWN+k) 0 := by
  have hf := h.header
  have hfin := h.header_fin
  have hc : tr.cell tt B.start sCL=1 := by simpa using hf.st 0 (by decide)
  have hs : tr.cell tt B.start fs=1 := by simpa using hf.fs 0 (by decide)
  have hh := reg_load hL (q := B.start) (by omega) (X := sCL) (l := pubs PH_OWN 8)
    (by simp [loads]) hc hs k (by simpa [pubs] using hk)
  simpa [pubs,List.getElem_map,List.getElem_range] using hh

/-- The physical header's twelve loaded bytes equal the concrete list-view header. -/
theorem ListBlockWf.header_registers {B : ListBlock} (h : ListBlockWf tr tt B) :
    ((List.range 12).map fun k => (tr.cell tt B.start (reg k)).toNat)=hdrBytes pub (B.view tr tt) := by
  have hown : ((List.range 8).map fun k => (tr.cell tt B.start (reg k)).toNat)=pubBytes pub PH_OWN 8 := by
    apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.mp hk
    simp only [ListBlockWf.header_own hL h k hk,pubNat]
  have hc := ListBlockWf.count_registers hL h
  rw [show 12=8+4 from rfl,List.range_add,List.map_append,hown]
  simp only [hdrBytes,List.map_map,Function.comp_def,ListBlock.view]
  congr 1
  simp only [show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil]
  simp only [show 8+0=8 from rfl,show 8+1=9 from rfl,show 8+2=10 from rfl,show 8+3=11 from rfl,
    hc.2.1,hc.2.2,show Fp.toNat 0=0 from rfl]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
