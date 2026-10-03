import ArenaStandIn.Admission
import Lean
open Lean Elab Tactic in
elab "arena_auto" : tactic => do
  evalTactic (← `(tactic| exact ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩))

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } := by
  arena_auto
