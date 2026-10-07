import ReexecV3D3.Canon
import ReexecV3D3.Logged.API

/-!
Candidate-local read-set normal form. The verifier performs one logged execution
and requires byte equality with the encoding of precisely the recorded-store
answers read by that execution. This module defines the new path separately
while its re-encoding/completeness proof is assembled; the deployed Model is not
switched until those obligations are closed.
-/
namespace ReexecV3D3.Read

open NearSpec NearSpecV3 NearSpecV3.D2

/-- Reads of transition `tag`; tag zero is the merged main/code store. -/
def readHashes (keys : List (Nat × Bytes)) (tag : Nat) : List Bytes :=
  keys.filterMap fun (t, h) => if t == tag then some h else none

/-- Filter canonical, last-wins pools to exactly the successful lookup answers.
Missing lookup answers contribute no value. Filtering preserves the pool order
and keeps one value per hash without trusting a collision-freedom assumption. -/
def restrictPools (keys : List (Nat × Bytes)) (X : Pools) : Pools :=
  (X.1.filter (fun v => (readHashes keys 0).contains (sha256 v)),
   X.2.zipIdx.map fun (vs, k) =>
     vs.filter (fun v => (readHashes keys (k + 1)).contains (sha256 v)))

/-- Encode a witness using an already-computed read set. No validator execution
occurs here. Invalid input cannot become an accepted proof through this function. -/
def encodeReads (cb w : Bytes) (keys : List (Nat × Bytes)) : Bytes :=
  match decodeWitnessFile w with
  | .error _ => w
  | .ok (sw, codes) =>
    match decodeStateWitnessD2 sw with
    | .error _ => w
    | .ok s => encP cb sw (restrictPools keys (initPools s codes))

/-- Prover normalisation: one logged check followed by re-encoding. -/
def canonW (cb w : Bytes) : Bytes :=
  encodeReads cb w (Logged.checkD3Reads cb w).2

/-- Verifier: one logged execution and exact equality with its read-set encoding.
There is no fallback branch accepting noncanonical witness bytes. -/
def check (cb w : Bytes) : Bool :=
  let (result, keys) := Logged.checkD3Reads cb w
  match result with
  | .error _ => false
  | .ok () => encodeReads cb w keys == w

/-- A successful read-set check still establishes the original frozen relation. -/
theorem check_sound {cb w : Bytes} (h : check cb w = true) :
    D3.checkD3 cb w = .ok () := by
  unfold check at h
  cases he : Logged.checkD3Reads cb w with
  | mk result keys =>
    rw [he] at h
    cases result with
    | error e => cases h
    | ok u =>
      cases u
      have hf := Logged.checkD3Reads_fst cb w
      rw [he] at hf
      exact hf.symm

/-- Acceptance requires literal equality, not merely store equivalence. -/
theorem check_normal {cb w : Bytes} (h : check cb w = true) : canonW cb w = w := by
  unfold check at h
  unfold canonW
  cases he : Logged.checkD3Reads cb w with
  | mk result keys =>
    rw [he] at h
    cases result with
    | error e => cases h
    | ok u =>
      cases u
      simpa using h

end ReexecV3D3.Read
