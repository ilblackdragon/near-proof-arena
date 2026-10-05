import ZkFormal.Bcs.Final
import ZkFormal.Udr.Rbr

/-!
# ZkFormal.Bcs.TransDefs — decoding byte transcripts into L3/L4 transcripts

`decodePT V τ` reads a byte-level transcript `τ : Bcs.PT mmcs` (as the BCS
extractor produces it) as lane L4's `Stark.PT K (Oracle F)`:
* the header is read from the first message, which must be admissible;
* each message's clear bytes are parsed along the schedule (`parseClear`),
  and each oracle part becomes the matrices read from the extracted MMCS
  oracle: the row of matrix `(m, w)` at index `i` is the slot of that
  matrix in the level-`m` bytes at `(m, i)`, normalized to width `w`
  (missing or malformed → zeros), exactly as the verifier's `rowAt`;
* challenges are decoded with `decodeChal`/`decodeOod` per the schedule.
Anything that does not fit gives `none`.

`DoomedB V D τ := ∀ σ, decodePT V τ = some σ → D σ`: an undecodable
transcript is doomed (and stays undecodable).
-/

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- Matrices of an oracle read from an extracted MMCS oracle. -/
def decMats (mats : List (Nat × Nat)) (o : Nat × Nat → Option Bytes) :
    List (Nat × Nat) → List Nat → List (Stark.Mat F)
  | [], _ => []
  | (m, w) :: ms, seen =>
    ⟨m, w, fun i => match o (m, i) with
      | some v => Adapter.rowAt (F := F) mats m w (seen.count m) v
      | none => List.replicate w 0⟩ :: decMats mats o ms (m :: seen)

def decOracle (mats : List (Nat × Nat)) (o : Nat × Nat → Option Bytes) : Stark.Oracle F :=
  decMats mats o mats []

/-- The parts of a decoded message, oracle parts filled from the extracted oracles. -/
def fill (os : List (Nat × Nat → Option Bytes)) :
    List Stark.Part → List (Stark.PartV K Unit) → Nat → List (Stark.PartV K (Stark.Oracle F))
  | .oracle mats :: ps, .oracle _ :: vs, t =>
    .oracle (decOracle mats (os.getD t fun _ => none)) :: fill os ps vs (t + 1)
  | _ :: ps, .header l :: vs, t => .header l :: fill os ps vs t
  | _ :: ps, .elems xs :: vs, t => .elems xs :: fill os ps vs t
  | _, _, _ => []

/-- Decode entries along the schedule (prefixes allowed). -/
noncomputable def decEntries (hdr : List Nat) : List Stark.Slot → List (Entry mmcs) →
    Option (List (Stark.Entry K (Stark.Oracle F)))
  | _, [] => some []
  | .msg parts :: ss, .msg _ clear os :: es =>
    match Adapter.parseClear (F := F) (K := K) hdr parts clear with
    | some (vs, []) => (decEntries hdr ss es).map (.msg (fill os parts vs 0) :: ·)
    | _ => none
  | .chal ood :: ss, .chal y :: es =>
    (decEntries hdr ss es).map
      (.chal (if ood then Stark.decodeOod (F := F) y else Stark.decodeChal (F := F) y) :: ·)
  | _, _ => none

/-- **Decoding a byte transcript.** -/
noncomputable def decodePT (V : Stark.IopSpec F K) (τ : PT mmcs) : Option (Stark.PT K (Stark.Oracle F)) :=
  match τ.entries with
  | [] => some (Stark.PT.init τ.cb)
  | _ :: _ =>
    match Adapter.viewHeader V τ.view.entries [] with
    | some hdr =>
      if V.headerOk hdr then (decEntries (F := F) hdr (V.schedule hdr) τ.entries).map (⟨τ.cb, ·⟩)
      else none
    | none => none

/-- The byte-level doomed predicate. -/
def DoomedB (V : Stark.IopSpec F K) (D : Stark.PT K (Stark.Oracle F) → Prop) (τ : PT mmcs) : Prop :=
  ∀ σ, decodePT V τ = some σ → D σ

/-- The challenge decoder of a slot. -/
def decChal (ood : Bool) (y : Bytes) : K :=
  if ood then Stark.decodeOod (F := F) y else Stark.decodeChal (F := F) y

end

end ZkFormal.Bcs.Transport
