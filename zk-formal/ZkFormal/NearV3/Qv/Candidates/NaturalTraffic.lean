import ZkFormal.NearV3.Qv.Candidates.NaturalEval
import ZkFormal.Near.Extract.BusCount

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

def natMultBits (row : List Nat) : List Expr → Nat → Nat
  | [], _ => 0
  | b::bs, k => (if rowNatEval row b=1 then 2^k else 0) + natMultBits row bs (k+1)

def natRowTraffic (is : List Interaction) (row : List Nat) (bus : Nat) (sd : Bool) : List Msg :=
  is.flatMap fun i => if i.bus=bus ∧ i.send=sd then
    List.replicate (natMultBits row i.mult 0) (i.msg.map (rowNatEval row)) else []

theorem cast_bit_eq_one (n : Nat) (hn : n≤1) :
    (@Nat.cast Fp Lean.Grind.Semiring.natCast n = 1) ↔ n=1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> decide

theorem multNat_go_nat (tr : Trace Fp) (t r : Nat) (pub : List Fp) (row : List Nat)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat (row.getD c 0)) (bs : List Expr)
    (hb : ∀ b ∈ bs, rowNatExpr b=true ∧ rowNatEval row b≤1) (k : Nat) :
    Interaction.multNat.go tr t r pub bs k=natMultBits row bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
    have h := hb b (by simp)
    simp only [Interaction.multNat.go,natMultBits]
    simp only [eval_nat_row b tr t r pub row h.1 hc,cast_bit_eq_one _ h.2]
    rw [ih (by intro e he; exact hb e (by simp [he]))]

theorem msgVal_nat (tr : Trace Fp) (t r : Nat) (pub : List Fp) (row : List Nat)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat (row.getD c 0)) (i : Interaction)
    (hi : ∀ e ∈ i.msg, rowNatExpr e=true) :
    i.msgVal tr t r pub=Msg.toFp (i.msg.map (rowNatEval row)) := by
  simp only [Interaction.msgVal,Msg.toFp,List.map_map]
  apply List.map_congr_left
  intro e he
  exact eval_nat_row e tr t r pub row (hi e he) hc

/-- Field row traffic equals the modular image of independently evaluated natural
messages whenever its natural multiplicity digits are bits. -/
theorem rowTraffic_nat (is : List Interaction) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (row : List Nat)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat (row.getD c 0))
    (hi : ∀ i ∈ is, (∀ b ∈ i.mult, rowNatExpr b=true ∧ rowNatEval row b≤1) ∧
      (∀ e ∈ i.msg, rowNatExpr e=true)) (bus : Nat) (sd : Bool) :
    rowTraffic is tr t r pub bus sd = (natRowTraffic is row bus sd).map Msg.toFp := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have h := hi i (by simp)
    have ht := ih (by intro j hj; exact hi j (by simp [hj]))
    simp only [rowTraffic,natRowTraffic,List.flatMap_cons,List.map_append] at ht ⊢
    rw [ht]
    congr 1
    by_cases hg : i.bus=bus ∧ i.send=sd
    · simp only [hg,and_self,ite_true,Interaction.multNat,
        multNat_go_nat tr t r pub row hc i.mult h.1 0,msgVal_nat tr t r pub row hc i h.2,
        List.map_replicate]
    · simp [hg]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
