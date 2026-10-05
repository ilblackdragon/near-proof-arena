import ArenaStandIn.Admission

/-- Slow reference function (what proofs talk about). -/
def Candidate.slowSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + Candidate.slowSum xs

/-- Tail-recursive implementation. -/
def Candidate.fastSum (xs : List Nat) : Nat := go 0 xs
where go (acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => go (acc + x) xs

/-- "Accept everything" replacement an attacker wants the compiler to use. -/
def Candidate.bogusSum (_ : List Nat) : Nat := 42

axiom Candidate.sumsAgree : @Candidate.slowSum = @Candidate.bogusSum

@[csimp] theorem Candidate.slowSum_eq_bogus : @Candidate.slowSum = @Candidate.bogusSum := Candidate.sumsAgree

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
