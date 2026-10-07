import ZkFormal.V2.Log23.Basic
import ZkFormal.V2.Verifier

/-! Executable isolated candidate. Soundness, honest completeness, and admission
are not inherited from the deployed verifier's log22 certificate. -/
namespace ZkFormal.V2.Log23

open Lean.Grind ZkFormal.Stark

def verifierHeader (AP : AirP) (g : Nat) (hdr : List Nat) : Bool :=
  decide (1 ≤ g) && decide (g ≤ 3) && publicWf 23 AP (2 ^ (params g).logBlowup) &&
  headerOk AP.toAir (params g) hdr &&
  decide (minQueryLog ≤ queryLog AP.toAir (params g) hdr)

def iop (F K : Type) [Field F] [Field K] [StarkField F K]
    [DecidableEq F] [DecidableEq K] [PubVal F] (AP : AirP) (g : Nat) : IopSpec F K :=
  { Iop.verifierP F K AP (params g) with headerOk := verifierHeader AP g }

def verifier (F K : Type) [Field F] [Field K] [StarkField F K]
    [DecidableEq F] [DecidableEq K] [PubVal F] (AP : AirP) (g : Nat) : ZkFormal.TreeVerifier :=
  ⟨fun pub cb pb => Bcs.compile (F := F) (iop F K AP g) pub cb pb⟩

theorem verifierHeader_bounds {AP : AirP} {g : Nat} {hdr : List Nat}
    (h : verifierHeader AP g hdr = true) :
    1 ≤ g ∧ g ≤ 3 ∧ publicWf 23 AP 16 = true ∧
    headerOk AP.toAir (params g) hdr = true ∧
    8 ≤ queryLog AP.toAir (params g) hdr ∧ queryLog AP.toAir (params g) hdr ≤ 27 := by
  simp only [verifierHeader, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2, queryLog_bound h.1.2⟩

end ZkFormal.V2.Log23
