import ZkFormal.NearV3.Assembly.RcptCandidateTotalBounds
-- Source NaturalTotals.lean SHA256: 60bf02877a3783a65fc4b84a1b2bb799b8525874c2e7f53c6f0bf5a3a14ad3db.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.TotalBounds
import ZkFormal.Near.Extract.RcptCount

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Public four-byte compression represents the native little-endian value
when its four public cells are bytes. No table constraints are assumed here. -/
theorem public_u32_eval (tr : Trace Fp) (tt q : Nat) (pub : List Fp) (off : Nat)
    (hb : ∀ i,i<4 → pubNat pub (off+i)<256) :
    (sum ((List.range 4).map fun x => smul (256^x) (.pub (off+x)))).eval tr tt q pub=
      ((leN' (pubBytes pub off 4):Nat):Fp) := by
  rw [ZkFormal.Near.RcptProof.leN'4]
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [Nat.add_zero] at h0
  rw [Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2,Nat.mod_eq_of_lt h3]
  simp [List.range_succ,eval_sum_cons,eval_sum_nil,eval_smul,eval_pub,
    ZkFormal.Near.RcptProof.pub_eq_cast,natCast_add,natCast_mul]
  simp only [pubNat,natCast_eq,Fp.ofNat_toNat,List.getD,show Fp.ofNat 1=(1:Fp) from rfl]
  grind

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Exact count with only its own public byte/range premises. -/
theorem ListChain.natural_count {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : leN' (pubBytes pub PH_N 4)<P)
    (hc : ∀ i,i<4 → pubNat pub (PH_N+i)<256) :
    (bs.map fun B => B.receipts.length).sum=leN' (pubBytes pub PH_N 4) := by
  have hf := (ListChain.final_totals hL h).1
  have he := public_u32_eval tr tt (e-1) pub PH_N hc
  change nPubE.eval tr tt (e-1) pub=_ at he
  rw [he] at hf
  exact (ofNat_inj hp (ListChain.total_bounds hL h).1 hf).symm

/-- Exact body length with only its own public byte/range premises. -/
theorem ListChain.natural_body {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : leN' (pubBytes pub PH_BLEN 4)<P)
    (hb : ∀ i,i<4 → pubNat pub (PH_BLEN+i)<256) :
    8+(bs.map fun B => B.refundBytes tr tt).sum=leN' (pubBytes pub PH_BLEN 4) := by
  have hf := (ListChain.final_totals hL h).2
  have he := public_u32_eval tr tt (e-1) pub PH_BLEN hb
  change blenE.eval tr tt (e-1) pub=_ at he
  rw [he] at hf
  exact (ofNat_inj hp (ListChain.total_bounds hL h).2 hf).symm

/-- The exact natural global totals, with the necessary public admissibility
premise visible. Extracted-side no-wrap follows entirely from the actual AIR. -/
theorem ListChain.natural_totals {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub)
    (hc : ∀ i,i<4 → pubNat pub (PH_N+i)<256)
    (hb : ∀ i,i<4 → pubNat pub (PH_BLEN+i)<256) :
    (bs.map fun B => B.receipts.length).sum=leN' (pubBytes pub PH_N 4) ∧
    8+(bs.map fun B => B.refundBytes tr tt).sum=leN' (pubBytes pub PH_BLEN 4) := by
  have hf := ListChain.final_totals hL h
  have hn := ListChain.total_bounds hL h
  have hce := public_u32_eval tr tt (e-1) pub PH_N hc
  have hbe := public_u32_eval tr tt (e-1) pub PH_BLEN hb
  change nPubE.eval tr tt (e-1) pub=_ at hce
  change blenE.eval tr tt (e-1) pub=_ at hbe
  rw [hce,hbe] at hf
  exact ⟨(ofNat_inj hp.count hn.1 hf.1).symm,(ofNat_inj hp.body hn.2 hf.2).symm⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
