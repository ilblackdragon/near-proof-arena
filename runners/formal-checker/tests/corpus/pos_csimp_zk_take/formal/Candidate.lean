import ArenaStandIn.Admission

/-! Honest `@[csimp]` copied verbatim from `zk-formal/ZkFormal/Stark/Bcs.lean`
(`take?_eq_takeF`, the compiled fast path of the ZK verifier). -/

namespace Candidate.Bcs

abbrev Bytes := List UInt8

/-- Take exactly `n` bytes. -/
def take? (n : Nat) (r : Bytes) : Option (Bytes × Bytes) :=
  if n ≤ r.length then some (r.take n, r.drop n) else none

/-- `take?` without measuring the input. -/
def takeF : Nat → Bytes → Option (Bytes × Bytes)
  | 0, r => some ([], r)
  | _ + 1, [] => none
  | n + 1, b :: r =>
    match takeF n r with
    | none => none
    | some (p, s) => some (b :: p, s)

theorem takeF_eq : ∀ (n : Nat) (r : Bytes), takeF n r = take? n r
  | 0, r => by simp [takeF, take?]
  | _ + 1, [] => by simp [takeF, take?]
  | n + 1, b :: r => by
    have ih := takeF_eq n r
    simp only [takeF, ih, take?, List.length_cons, Nat.add_le_add_iff_right]
    by_cases h : n ≤ r.length <;> simp [h]

@[csimp] theorem take?_eq_takeF : @take? = @takeF := by
  funext n r; exact (takeF_eq n r).symm

/-- A compiled caller (uses `takeF` at runtime). -/
def firstTwo (r : Bytes) : Option (Bytes × Bytes) := take? 2 r

end Candidate.Bcs

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
