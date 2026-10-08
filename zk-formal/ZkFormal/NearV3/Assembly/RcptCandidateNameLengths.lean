import ZkFormal.NearV3.Assembly.RcptCandidateBounds
import ZkFormal.NearV3.Assembly.RcptCandidateStrField
-- Source NameLengths.lean SHA256: 578bd5fd09ee601b24ae87ecfaff3450d70af1b84b49632170f08c16a9e804dc.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.StrField

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Length bounds `2 ≤ L ≤ 64` of a string field. -/
theorem str_len {s r0 L X Lc : Nat} (F : RFld tr tt s r0 L X) (hH : r0 + L < tr.height tt)
    (hc : ∀ k, k < L → tr.cell tt (r0 + k) Lc = ((L : Nat) : Fp))
    (m1 : mul3 (c fe) (c X) (sub (sub (c Lc) (k 2)) (bitsX 0 6)) ∈ receiptArithmeticCandidate.constraints)
    (m2 : mul3 (c fe) (c X) (sub (sub (k 64) (c Lc)) (bitsX 6 6)) ∈ receiptArithmeticCandidate.constraints) :
    2 ≤ L ∧ L ≤ 64 := by
  have hp := F.fld.pos
  have hq : r0 + (L - 1) < tr.height tt := by omega
  have c1 := con hL hq m1
  have c2 := con hL hq m2
  obtain ⟨b1, l1⟩ := bitsX_eval hL hq 0 6 (by omega)
  obtain ⟨b2, l2⟩ := bitsX_eval hL hq 6 6 (by omega)
  simp only [eval_mul3, eval_c, eval_sub, eval_k] at c1 c2
  rw [F.fld.fe (L - 1) (by omega), if_pos (by omega), F.fld.st (L - 1) (by omega), hc (L - 1) (by omega), b1] at c1
  rw [F.fld.fe (L - 1) (by omega), if_pos (by omega), F.fld.st (L - 1) (by omega), hc (L - 1) (by omega), b2] at c2
  have hLP : L < P := by have := hP hL; omega
  have e1 : L = 2 + bitsVal (fun j => cv tr tt (r0 + (L - 1)) (xb j)) 0 6 := by
    apply ofNat_inj hLP (by simp at l1; unfold P; omega); rw [natCast_add]; grind
  have e2 : 64 = L + bitsVal (fun j => cv tr tt (r0 + (L - 1)) (xb j)) 6 6 := by
    apply ofNat_inj (by unfold P; omega) (by simp at l2; unfold P; omega); rw [natCast_add]; grind
  omega


end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
