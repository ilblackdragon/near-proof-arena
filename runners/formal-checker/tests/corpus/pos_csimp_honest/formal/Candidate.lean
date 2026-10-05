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

theorem Candidate.fastSum_go (acc : Nat) (xs : List Nat) :
    Candidate.fastSum.go acc xs = acc + Candidate.slowSum xs := by
  induction xs generalizing acc with
  | nil => simp [Candidate.fastSum.go, Candidate.slowSum]
  | cons x xs ih => simp [Candidate.fastSum.go, Candidate.slowSum, ih]; omega

@[csimp] theorem Candidate.slowSum_eq_fastSum : @Candidate.slowSum = @Candidate.fastSum := by
  funext xs; simp [Candidate.fastSum, Candidate.fastSum_go]

/-- Compiled code uses `fastSum` (via csimp); proofs use `slowSum`. -/
def Candidate.total : Nat := Candidate.slowSum [1, 2, 3]

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
