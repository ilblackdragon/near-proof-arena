import ZkFormal.NearV3.Rcpt.Extract.V.Table

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- One actual receipt-list block: a twelve-row header and possibly no receipts. -/
structure ListBlock where
  start : Nat
  receipts : List RS

def ListBlock.stop (B : ListBlock) : Nat := segEnd (B.start+12) (segsOf B.receipts)
def ListBlock.rows (B : ListBlock) : Nat := 12+(B.receipts.map RS.tot).sum

structure ListBlockWf (tr : Trace Fp) (tt : Nat) (B : ListBlock) : Prop where
  header : Fld tr tt B.start 12 sCL
  header_fin : B.start+12<tr.height tt
  consecutive : Consec (B.start+12) (segsOf B.receipts)
  layouts : ∀ x∈B.receipts, Layout tr tt x.s x.h x.Lp x.Lv x.Ls x.kt
  boundary : BlockEnd tr tt B.stop

/-- Consecutive receipt intervals account for every physical row in the block. -/
theorem receipt_end_sum (rcs : List RS) (s : Nat) (hc : Consec s (segsOf rcs)) :
    segEnd s (segsOf rcs)=s+(rcs.map RS.tot).sum := by
  induction rcs generalizing s with
  | nil => simp [segsOf, segEnd]
  | cons x xs ih =>
    obtain ⟨hs, hc⟩ := hc
    change segEnd (x.s+x.tot) (segsOf xs) = s+(x.tot+(xs.map RS.tot).sum)
    have ht : Consec (x.s+x.tot) (segsOf xs) := by simpa only [hs, segsOf] using hc
    rw [ih (x.s+x.tot) ht, hs]
    omega

theorem ListBlockWf.stop_eq {tr : Trace Fp} {tt : Nat} {B : ListBlock} (h : ListBlockWf tr tt B) :
    B.stop=B.start+B.rows := by
  have hh := receipt_end_sum B.receipts (B.start+12) h.consecutive
  simpa only [ListBlock.stop, ListBlock.rows, Nat.add_assoc] using hh

theorem ListBlockWf.bound {tr : Trace Fp} {tt : Nat} {B : ListBlock} (h : ListBlockWf tr tt B) :
    B.start+12≤B.stop ∧ B.stop<tr.height tt := by
  have hh := h.stop_eq
  have hb := h.boundary.1
  unfold ListBlock.rows at hh
  omega

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
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

end ZkFormal.NearV3.RcptV3Proof
