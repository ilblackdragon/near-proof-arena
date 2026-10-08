import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTable

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The repaired table entails exactly the arithmetic candidate, not the old
system-gas and nine-bit-age equations. -/
theorem repaired_local_base (h : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub) :
    TableLocal receiptArithmeticCandidate tr tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,h.bits⟩
  intro pos hp e he
  exact h.constr pos hp e (List.mem_append_left _ he)

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem bitsX_eval {q : Nat} (hq : q<tr.height tt) (off len : Nat) (hb : off+len≤66) :
    (bitsX off len).eval tr tt q pub = ((bitsVal (fun j => cv tr tt q (xb j)) off len : Nat) : Fp) ∧
    bitsVal (fun j => cv tr tt q (xb j)) off len < 2^len := by
  have hbits : ∀ j, j<len → tr.cell tt q (xb (off+j))=0 ∨ tr.cell tt q (xb (off+j))=1 := by
    intro j hj
    apply isBool hL hq
    have hm : xb (off+j)∈(List.range 66).map xb := List.mem_map.mpr ⟨off+j,List.mem_range.mpr (by omega),rfl⟩
    simp only [boolCols,List.mem_append]
    exact Or.inl (Or.inr hm)
  exact ⟨eval_bits tr tt q pub xb off len hbits, bitsVal_lt _ off len (fun j hj => cv_bool (hbits j hj))⟩

/-- Exact natural previous-version order. A provider bound prevents modular
wrap; the obsolete P-512 guard is not reused for the wider age window. -/
theorem deposit_previous_row {pos : Nat} (hp : pos<tr.height tt)
    (hs : tr.cell tt pos sDEP=1) (hf : tr.cell tt pos fs=1)
    (ht : cv tr tt pos tprev<P-8192) : cv tr tt pos tprev≤cv tr tt pos r := by
  have he := con hL hp (mem_dp (show
    mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13))∈depositAgeConstraints by
      simp [depositAgeConstraints,depositConstraintsWith]))
  obtain ⟨hb,hlt⟩ := bitsX_eval hL hp 53 13 (by decide)
  simp only [dp,eval_mul3,eval_c,eval_sub,hs,hf] at he
  rw [hb,cell_eq_cast tr tt pos r,cell_eq_cast tr tt pos tprev] at he
  have eq : (cv tr tt pos r:Fp)=((cv tr tt pos tprev+bitsVal (fun j=>cv tr tt pos (xb j)) 53 13:Nat):Fp) := by
    rw [natCast_add];grind
  have hn := ofNat_inj (tr.cell tt pos r).toNat_lt (by unfold P at *;omega) eq
  simp only [cv] at *
  omega

theorem deposit_previous_provider_bound {pos : Nat} (hp : pos<tr.height tt)
    (hs : tr.cell tt pos sDEP=1) (hf : tr.cell tt pos fs=1)
    (ht : cv tr tt pos tprev≤2^22) : cv tr tt pos tprev≤cv tr tt pos r :=
  deposit_previous_row hL hp hs hf (by unfold P;omega)

theorem repaired_first_receiver_q {pos : Nat}
    (h : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    (hp : pos<tr.height tt) (hs : tr.cell tt pos sV=1) (hf : tr.cell tt pos fs=1) :
    cv tr tt pos q<128 := by
  have he := h.constr pos hp RoutingQCandidate.qBound (by simp [ReceiptCandidateRouting.candidateTable])
  obtain ⟨hb,hl⟩ := bitsX_eval (repaired_local_base h) hp 12 7 (by decide)
  simp only [RoutingQCandidate.qBound,eval_mul3,eval_c,eval_sub,hs,hf] at he
  rw [hb,cell_eq_cast tr tt pos q] at he
  have eq : (cv tr tt pos q:Fp)=((bitsVal (fun j=>cv tr tt pos (xb j)) 12 7:Nat):Fp) := by grind
  have hn := ofNat_inj (tr.cell tt pos q).toNat_lt (by unfold P;omega) eq
  simp only [cv] at *
  omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
