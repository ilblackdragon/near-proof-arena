import NearSpecV3.Logged.WasmCRHostCall
import NearSpecV3.Wasm.CryptoHost

/-! # The successor curve hosts leave the trie store alone (`CR_cryptoHostCall`, `CR_dispatchArm`)

`callHost` dispatches through `dispatchArm`, which adds `cryptoHostCall` (W05: `ecrecover`,
`p256_verify`, the three `alt_bn128_*` and the nine `bls12381_*` hosts) when `St.curveHosts` is set.
None of them touches storage: each is base/per-element charging, a memory-or-register read, a pure
curve computation and a register write or a return value. So each commutes with `E σ` exactly as the
non-storage `hostCall` arms do (`CR_hostCall`), and `dispatchArm`'s arm does too. -/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm

set_option maxHeartbeats 4000000

theorem CR_blsWriter (σ : TTN.Store) (base element : Cost) (itemSize : Nat) (fnName : String)
    (decode : ArenaCore.Bytes → Option ArenaCore.Bytes) (a : Vector Nat 3) :
    CR σ (blsWriter base element itemSize fnName decode a)
      (blsWriter base element itemSize fnName decode a) := by
  unfold blsWriter; cr

theorem CR_altBn128Writer (σ : TTN.Store) (base element : Cost) (itemSize : Nat)
    (decode : ArenaCore.Bytes → Option ArenaCore.Bytes) (a : Vector Nat 3) :
    CR σ (altBn128Writer base element itemSize decode a) (altBn128Writer base element itemSize decode a) := by
  unfold altBn128Writer; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_blsWriter)
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_altBn128Writer)

theorem CR_hostEcrecover (σ : TTN.Store) (a : Vector Nat 7) : CR σ (hostEcrecover a) (hostEcrecover a) := by
  unfold hostEcrecover; cr
theorem CR_hostP256Verify (σ : TTN.Store) (a : Vector Nat 6) : CR σ (hostP256Verify a) (hostP256Verify a) := by
  unfold hostP256Verify; cr
theorem CR_hostPairingCheck (σ : TTN.Store) (a : Vector Nat 2) :
    CR σ (hostPairingCheck a) (hostPairingCheck a) := by
  unfold hostPairingCheck; cr
theorem CR_hostAltBn128PairingCheck (σ : TTN.Store) (a : Vector Nat 2) :
    CR σ (hostAltBn128PairingCheck a) (hostAltBn128PairingCheck a) := by
  unfold hostAltBn128PairingCheck; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hostEcrecover)
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hostP256Verify)
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hostPairingCheck)
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hostAltBn128PairingCheck)

set_option maxRecDepth 100000 in
/-- Every curve-host arm commutes with `E σ`. -/
theorem CR_cryptoHostCall (σ : TTN.Store) (name : String) (h : HM Unit)
    (hh : cryptoHostCall name = some h) : CR σ h h := by
  by_cases h1 : name = "ecrecover"
  · subst h1; rw [cryptoHostCall.eq_1] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_hostEcrecover σ _)
  by_cases h2 : name = "p256_verify"
  · subst h2; rw [cryptoHostCall.eq_2] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_hostP256Verify σ _)
  by_cases h3 : name = "alt_bn128_g1_multiexp"
  · subst h3; rw [cryptoHostCall.eq_3] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_altBn128Writer σ _ _ _ _ _)
  by_cases h4 : name = "alt_bn128_g1_sum"
  · subst h4; rw [cryptoHostCall.eq_4] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_altBn128Writer σ _ _ _ _ _)
  by_cases h5 : name = "alt_bn128_pairing_check"
  · subst h5; rw [cryptoHostCall.eq_5] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_hostAltBn128PairingCheck σ _)
  by_cases h6 : name = "bls12381_p1_sum"
  · subst h6; rw [cryptoHostCall.eq_6] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h7 : name = "bls12381_p2_sum"
  · subst h7; rw [cryptoHostCall.eq_7] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h8 : name = "bls12381_g1_multiexp"
  · subst h8; rw [cryptoHostCall.eq_8] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h9 : name = "bls12381_g2_multiexp"
  · subst h9; rw [cryptoHostCall.eq_9] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h10 : name = "bls12381_p1_decompress"
  · subst h10; rw [cryptoHostCall.eq_10] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h11 : name = "bls12381_p2_decompress"
  · subst h11; rw [cryptoHostCall.eq_11] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h12 : name = "bls12381_map_fp_to_g1"
  · subst h12; rw [cryptoHostCall.eq_12] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h13 : name = "bls12381_map_fp2_to_g2"
  · subst h13; rw [cryptoHostCall.eq_13] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_blsWriter σ _ _ _ _ _ _)
  by_cases h14 : name = "bls12381_pairing_check"
  · subst h14; rw [cryptoHostCall.eq_14] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2
    exact CR_bind (CR_popArgs σ _) (fun _ => CR_hostPairingCheck σ _)
  rw [cryptoHostCall.eq_15 name h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14] at hh; cases hh

/-- `dispatchArm` does not read the store. -/
theorem dispatchArm_E (σ : TTN.Store) (s : St) (name : String) :
    dispatchArm (E σ s) name = dispatchArm s name := rfl

/-- **Every non-storage dispatch arm commutes with `E σ`**, signed (`hostCall`) or successor
(`cryptoHostCall`). -/
theorem CR_dispatchArm (σ : TTN.Store) (s : St) (name : String) (h : HM Unit)
    (hh : dispatchArm s name = some h) (hn : storageHosts.contains name = false) : CR σ h h := by
  unfold dispatchArm at hh
  cases hc : hostCall name with
  | some h' =>
    rw [hc] at hh; simp only [Option.some.injEq] at hh; subst hh; exact CR_hostCall σ name _ hc hn
  | none =>
    rw [hc] at hh
    simp only at hh
    split at hh
    · exact CR_cryptoHostCall σ name h hh
    · cases hh

end NearSpecV3.Logged.W
