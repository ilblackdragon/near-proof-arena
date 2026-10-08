import ZkFormal.NearV3.Rcpt.Extract.V.NameLengths

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open RcptV3 RcptV3Proof

/-- Isolated repair: reuse seven existing boolean scratch columns on the first
receiver row. The active receipt table and frozen spec remain untouched. -/
def qBound : Expr := mul3 (c sV) (c fs) (sub (c q) (bitsX 12 7))
def candidateTable : Table :=
  { RcptV3.table with constraints := RcptV3.constraints ++ [qBound] }

theorem unchanged_shape : candidateTable.width=RcptV3.table.width ∧
    candidateTable.maxLog=RcptV3.table.maxLog ∧
    candidateTable.interactions=RcptV3.table.interactions ∧
    candidateTable.constraints.length=RcptV3.constraints.length+1 := by
  simp [candidateTable]

theorem local_base {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal candidateTable tr t pub) : TableLocal RcptV3.table tr t pub := by
  refine ⟨h.log_ge,h.log_le,?_,h.bits⟩
  intro r hr e he
  exact h.constr r hr e (List.mem_append_left _ he)

theorem first_receiver_q_lt {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (h : TableLocal candidateTable tr t pub) (hr : r<tr.height t)
    (hs : tr.cell t r sV=1) (hf : tr.cell t r fs=1) : cv tr t r q<128 := by
  have he := h.constr r hr qBound (by simp [candidateTable])
  obtain ⟨be,bl⟩ := bitsX_eval (local_base h) hr 12 7 (by decide)
  simp only [qBound,eval_mul3,eval_c,eval_sub,hs,hf] at he
  rw [be,cell_eq_cast tr t r q] at he
  have hq : cv tr t r q=bitsVal (fun j=>cv tr t r (xb j)) 12 7 := by
    apply ofNat_inj (tr.cell t r q).toNat_lt (by unfold P;omega)
    simp only [cv] at he ⊢
    grind
  rw [hq]
  exact bl

/-- Existing BND physical capacity suffices for honest seven-bit q. This is NOT
an accepted-input BND capacity theorem; that independent coverage gap stays open. -/
theorem q_bound_of_bnd_capacity (count q : Nat) (hcap : 65*count≤2^13) (hq : q<count) :
    q<128 := by omega

/-- A bounded q removes modular aliases in the packed boundary lookup address. -/
theorem packed_address_exact {q pos x : Nat} (hq : q<128) (hp : pos<65)
    (hx : x<2^13) (he : (65*q+pos : Nat)=x) : q=x/65 ∧ pos=x%65 := by omega

theorem packed_field_address_exact {q pos x : Nat} (hq : q<128) (hp : pos<65)
    (hx : x<2^13) (he : ((65*q+pos : Nat):Fp)=(x: Fp)) : q=x/65 ∧ pos=x%65 := by
  apply packed_address_exact hq hp hx
  exact ofNat_inj (by unfold P;omega) (by unfold P;omega) he

/-- Rejects the identified q alias for EVERY possible filling of the scratch bits
in an otherwise locally valid candidate trace, not just the original fixture. -/
theorem alias_rejected {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (h : TableLocal candidateTable tr t pub) (hr : r<tr.height t)
    (hs : tr.cell t r sV=1) (hf : tr.cell t r fs=1) : cv tr t r q≠1796452668 := by
  have hh := first_receiver_q_lt h hr hs hf
  omega

end ZkFormal.NearV3.Assembly.RoutingQCandidate
