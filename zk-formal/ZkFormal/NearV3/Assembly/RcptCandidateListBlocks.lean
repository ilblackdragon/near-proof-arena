import ZkFormal.NearV3.Assembly.RcptCandidateTable
import ZkFormal.NearV3.Rcpt.Extract.V.ListBlocks
-- Source ListBlocks.lean SHA256: 0b28297dad8291f22746749072005cb6a10c5f92fa403297c267017a25fe2b13.
-- Reuses original data types and migrates only table-local proofs.
namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Every header starts an actual complete list block, including empty lists. -/
theorem list_block_from {s : Nat} (hs : s<tr.height tt) (hc : tr.cell tt s sCL=1)
    (hfs : tr.cell tt s fs=1) (hi : tr.cell tt s idx=0) :
    ∃ rcs, ListBlockWf tr tt ⟨s,rcs⟩ := by
  obtain ⟨len, hfin, hf⟩ := fld_from hL hs (by simp [states]) hc hi hfs
  have hlen : len=12 := fld_len_k hL (by omega) hf (by simp [lastIdx]) (by decide)
  subst len
  have hlast : tr.cell tt (s+11) sCL=1 := hf.st 11 (by omega)
  have hfe : tr.cell tt (s+11) fe=1 := by simpa using hf.fe 11 (by omega)
  have hrl : tr.cell tt (s+11) rl=0 := by
    have hh := (bounds hL (r := s+11) (by omega)).1
    have ho := (oneHot hL (r := s+11) (by omega) (by simp [states]) hlast).2
    rw [ho sXRZ (by simp [states]) (by decide), ho sXLH (by simp [states]) (by decide)] at hh
    rw [hh]; grind
  have hbrk : tr.cell tt (s+11) rl+tr.cell tt (s+11) sCL*tr.cell tt (s+11) fe=1 := by
    rw [hrl, hlast, hfe]; grind
  have hab := after_brk hL hfin (by omega)
    (by simpa only [show s+12-1=s+11 by omega] using hbrk)
    (by simpa only [show s+12-1=s+11 by omega] using hfe)
  rcases hab with hp | ⟨ha, hr⟩ | ⟨ha, hr, hn, hnf, hni⟩
  · exact ⟨[], hf, hfin, trivial, by simp, hfin, Or.inl hp⟩
  · obtain ⟨rcs, _, hcon, hlays, _, _, hend⟩ := rcpts_from hL
      (tr.height tt-(s+12)) (s+12) (tr.cell tt (s+12) RcptV3.r).toNat
      (tr.cell tt (s+12) cj).toNat (by omega) hfin hr
      (by exact (Fp.ofNat_toNat _).symm) (by exact (Fp.ofNat_toNat _).symm)
    exact ⟨rcs, hf, hfin, hcon, hlays, hend⟩
  · exact ⟨[], hf, hfin, trivial, by simp, hfin, Or.inr ⟨hn, hnf, hni⟩⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
