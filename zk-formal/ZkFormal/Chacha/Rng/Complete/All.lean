import ZkFormal.Chacha.Rng.Complete.Bus

/-!
# ZkFormal.Chacha.Rng.Complete.All — completeness of the stream / `gen_index` table `genV3`

For any list of supported `gen_index` calls that fits the table, the honest trace
(ZkFormal.Chacha.Rng.Gen) has a legal height, satisfies every constraint on every row
(including padding rows and the cyclic wrap), has boolean multiplicity bits, receives on
`busChacha` exactly `expectedWords calls` (one `chachaMsg key (k/16) (k%16) (streamWord key k)`
per draw) and provides on `busGen` exactly `expectedGen calls` (one
`genMsg key kstart n j kend` per call, `genAt 64 n key kstart = some (j, kend)`).
-/

namespace ZkFormal.Chacha.Rng.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Gen

theorem constraints_ok (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (t : Nat) (pub : List Fp)
    (r : Nat) (hr : r < (honestTrace calls).height t) :
    ∀ e ∈ Rng.Table.constraints, e.eval (honestTrace calls) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  refine row_ok (honest_env calls hok t r pub) (step_at calls hok t r hr) ?_ e he
  show (if r = 0 then 1 else 0 : Int) = 0 ∨ ((if r = 0 then 1 else 0 : Int) = 1 ∧ _)
  by_cases h0 : r = 0
  · right; subst h0; exact ⟨rfl, row0_start calls hok⟩
  · left; rw [if_neg h0]

/-- **Completeness of the stream / `gen_index` table.** -/
theorem gen_complete (calls : List Gen.Call) (hok : ∀ C ∈ calls, Gen.CallOk C)
    (hrows : (Gen.honestRows calls).length ≤ 2 ^ Rng.Table.maxLog) (busChacha busGen : Nat)
    (hne : busChacha ≠ busGen) :
    (∀ t, 1 ≤ (Gen.honestTrace calls).log t ∧ (Gen.honestTrace calls).log t ≤ Rng.Table.maxLog) ∧
    (∀ t pub r, r < (Gen.honestTrace calls).height t → ∀ e ∈ Rng.Table.constraints,
       e.eval (Gen.honestTrace calls) t r pub = 0) ∧
    (∀ t pub r, r < (Gen.honestTrace calls).height t → ∀ i ∈ Rng.Table.interactions busChacha busGen,
       ∀ b ∈ i.mult,
       b.eval (Gen.honestTrace calls) t r pub = 0 ∨ b.eval (Gen.honestTrace calls) t r pub = 1) ∧
    (∀ t pub m,
       tableBusCount (Rng.Table.interactions busChacha busGen) (Gen.honestTrace calls) t pub busChacha
         false m = (Gen.expectedWords calls).count m ∧
       tableBusCount (Rng.Table.interactions busChacha busGen) (Gen.honestTrace calls) t pub busChacha
         true m = 0 ∧
       tableBusCount (Rng.Table.interactions busChacha busGen) (Gen.honestTrace calls) t pub busGen
         true m = (Gen.expectedGen calls).count m ∧
       tableBusCount (Rng.Table.interactions busChacha busGen) (Gen.honestTrace calls) t pub busGen
         false m = 0) := by
  refine ⟨log_bounds calls hrows, fun t pub r hr => constraints_ok calls hok t pub r hr,
    fun t pub r _ => multBits calls busChacha busGen t r pub, fun t pub m => ?_⟩
  have hne' : busGen ≠ busChacha := fun h => hne h.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [count_rows calls hok] <;> simp [hne, hne']

/-- The honest trace is a legal `genV3` table (the hypothesis of the soundness theorems). -/
theorem gLocal_honest (calls : List Gen.Call) (hok : ∀ C ∈ calls, Gen.CallOk C) (t : Nat)
    (pub : List Fp) : Rng.GLocal (Gen.honestTrace calls) t pub :=
  fun r hr => constraints_ok calls hok t pub r hr

end ZkFormal.Chacha.Rng.Complete
