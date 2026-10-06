import ZkFormal.Chacha.Shuffle.Complete.Count

/-!
# ZkFormal.Chacha.Shuffle.Complete.All — completeness of the shuffle table `shufV3`

For any list of supported instances (`InstOk`) that fits the table (`≤ 2^maxLog` rows; a
completely full table is allowed), the honest trace (ZkFormal.Chacha.Shuffle.Gen) has a legal
height, satisfies every constraint on every row (padding rows and the cyclic wrap included),
has boolean multiplicity bits, and its memory bus balances inside the table
(`shuffle_complete`).  With pairwise distinct buses its traffic on the other buses is exactly
the expected lists (`shuffle_traffic`): receives `expectedIn` on `busIn` and `expectedGen` on
`busGen`, sends `expectedOut` on `busOut` and `expectedShuf` on `busShuf`.
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table

/-- **Completeness of the shuffle table.** -/
theorem shuffle_complete (insts : List Gen.SInst) (hok : ∀ I ∈ insts, InstOk I)
    (hrows : (Gen.honestRows insts).length ≤ 2 ^ Shuffle.Table.maxLog) (B : Shuffle.Buses) (hB : B.ok) :
    (∀ t, 1 ≤ (Gen.honestTrace insts).log t ∧ (Gen.honestTrace insts).log t ≤ Shuffle.Table.maxLog) ∧
    (∀ t pub r, r < (Gen.honestTrace insts).height t → ∀ e ∈ Shuffle.Table.constraints,
       e.eval (Gen.honestTrace insts) t r pub = 0) ∧
    (∀ t pub r, r < (Gen.honestTrace insts).height t → ∀ i ∈ B.is, ∀ b ∈ i.mult,
       b.eval (Gen.honestTrace insts) t r pub = 0 ∨ b.eval (Gen.honestTrace insts) t r pub = 1) ∧
    (∀ t pub, Shuffle.MemBal B (Gen.honestTrace insts) t pub) :=
  ⟨log_bounds insts hrows, fun t pub r hr => constraints_ok insts hok hrows t pub r hr,
    fun t pub r hr => multBits insts hok hrows B t r pub hr, fun t pub => memBal insts hok hrows B hB t pub⟩

/-- The honest trace is a legal `shufV3` table (the hypothesis `SLocal` of the soundness theorems). -/
theorem sLocal_honest (insts : List Gen.SInst) (hok : ∀ I ∈ insts, InstOk I)
    (hrows : (Gen.honestRows insts).length ≤ 2 ^ Shuffle.Table.maxLog) (t : Nat) (pub : List Fp) :
    Shuffle.SLocal (Gen.honestTrace insts) t pub :=
  fun r hr => constraints_ok insts hok hrows t pub r hr

/-- **Traffic on the external buses** (all five buses pairwise distinct). -/
theorem shuffle_traffic (insts : List Gen.SInst) (hok : ∀ I ∈ insts, InstOk I)
    (hrows : (Gen.honestRows insts).length ≤ 2 ^ Shuffle.Table.maxLog) (B : Shuffle.Buses)
    (hd : [B.bin, B.bout, B.mem, B.gen, B.shuf].Nodup) (t : Nat) (pub : List Fp) (m : List Fp) :
    tableBusCount B.is (Gen.honestTrace insts) t pub B.bin false m = (expectedIn insts).count m ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.bin true m = 0 ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.bout true m = (expectedOut insts).count m ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.bout false m = 0 ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.gen false m = (expectedGen insts).count m ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.gen true m = 0 ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.shuf true m = (expectedShuf insts).count m ∧
    tableBusCount B.is (Gen.honestTrace insts) t pub B.shuf false m = 0 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1, -⟩ := hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [count_rows insts hok hrows] <;>
    simp [a1, a2, a3, a4, b1, b2, b3, c1, c2, d1, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
      Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm c1, Ne.symm c2, Ne.symm d1]

end ZkFormal.Chacha.Shuffle.Complete
