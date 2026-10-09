import ZkFormal.NearV3.Rcpt.Candidates.ReceiptConsumption
import ZkFormal.NearV3.Rcpt.Candidates.SourceEncodingBudget

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

/-- Every actual parsed Merkle path item consumes exactly 33 raw bytes. -/
theorem pPathItem_consumption {bs rest : Bytes} {step : Bytes × Nat}
    (h : pPathItem bs = .ok (step, rest)) : bs.length = 33 + rest.length := by
  unfold pPathItem at h
  obtain ⟨⟨hash, tail⟩, hh, h⟩ := bind_ok h
  obtain ⟨⟨d, last⟩, hd, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, he, _⟩ := bind_ok h; cases he
  · cases h
    have h1 := pHash_consumption hh
    have h2 := pU8_consumption hd
    omega

/-- Accumulate a lower bound on consumed bytes across the actual vector decoder. -/
theorem pMany_cost {α : Type} (p : NearSpecV3.P α) (cost : α → Nat)
    (hp : ∀ bs a rest, p bs = .ok (a, rest) → cost a + rest.length ≤ bs.length) :
    ∀ n bs xs rest, pMany p n bs = .ok (xs, rest) →
      (xs.map cost).sum + rest.length ≤ bs.length := by
  intro n
  induction n with
  | zero => intro bs xs rest h; cases h; simp
  | succ n ih =>
    intro bs xs rest h
    unfold pMany at h
    obtain ⟨⟨a, tail⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨ys, last⟩, hy, h⟩ := bind_ok h
    cases h
    have h1 := hp _ _ _ ha
    have h2 := ih _ _ _ hy
    simp only [List.map_cons, List.sum_cons]
    omega

theorem pVec_cost {α : Type} (p : NearSpecV3.P α) (cost : α → Nat)
    (hp : ∀ bs a rest, p bs = .ok (a, rest) → cost a + rest.length ≤ bs.length)
    {w : String} {bs rest : Bytes} {xs : List α} (h : pVec w p bs = .ok (xs, rest)) :
    (xs.map cost).sum + rest.length ≤ bs.length := by
  unfold pVec at h
  obtain ⟨⟨n, tail⟩, hn, h⟩ := bind_ok h
  have h1 := pMany_cost p cost hp n _ _ _ h
  have h2 := pUInt_le 4 _ _ _ _ hn
  omega

private theorem const_sum {α : Type} (xs : List α) (c : Nat) :
    (xs.map fun _ => c).sum = c * xs.length := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add, Nat.mul_one]; omega

theorem pPathVec_cost {w : String} {bs rest : Bytes} {path : List (Bytes × Nat)}
    (h : pVec w pPathItem bs = .ok (path, rest)) : 33 * path.length + rest.length ≤ bs.length := by
  have hh := pVec_cost pPathItem (fun _ => 33)
    (fun _ _ _ hp => Nat.le_of_eq (pPathItem_consumption hp).symm) h
  simpa only [const_sum] using hh

/-- Parsed path bytes are charged even if receipt data or keys precede them. -/
theorem pEntry_path_cost {bs rest : Bytes} {e : ProofEntry}
    (h : pEntry bs = .ok (e, rest)) : 33 * e.proof.path.length + rest.length ≤ bs.length := by
  unfold pEntry at h
  obtain ⟨⟨key, r1⟩, hk, h⟩ := bind_ok h
  obtain ⟨⟨rs, r2⟩, hrs, h⟩ := bind_ok h
  obtain ⟨⟨f, r3⟩, hf, h⟩ := bind_ok h
  obtain ⟨⟨t, r4⟩, ht, h⟩ := bind_ok h
  obtain ⟨⟨path, r5⟩, hp, h⟩ := bind_ok h
  cases h
  have h1 := pHash_le _ _ _ _ hk
  have h2 := pVec_le NearSpecV3.pReceipt pReceipt_le _ _ _ _ hrs
  have h3 := pUInt_le 8 _ _ _ _ hf
  have h4 := pUInt_le 8 _ _ _ _ ht
  have h5 := pPathVec_cost hp
  dsimp only
  omega

private theorem path_cost_sum (entries : List ProofEntry) :
    (entries.map fun e => 33 * e.proof.path.length).sum = 33 * pathCount entries := by
  induction entries with
  | nil => simp [pathCount]
  | cons e rest ih => simp only [pathCount, List.map_cons, List.sum_cons] at *; omega

/-- Every encoded dictionary path item is counted once, regardless of later lookup reuse. -/
theorem pEntries_cost {w : String} {bs rest : Bytes} {entries : List ProofEntry}
    (h : pVec w pEntry bs = .ok (entries, rest)) :
    33 * pathCount entries + rest.length ≤ bs.length := by
  have hh := pVec_cost pEntry (fun e => 33 * e.proof.path.length)
    (fun _ _ _ he => pEntry_path_cost he) h
  simpa only [path_cost_sum] using hh

end ZkFormal.NearV3.Rcpt.Candidates
