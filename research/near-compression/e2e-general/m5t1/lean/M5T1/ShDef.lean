import M5T1.Se
import M5T1.AccSem

/-!
# M5T1.ShDef — what the `SH` rows establish, stated (F-7)

Definitions shared by `ShSem*` (the proof from the circuit, `ShSem.sh_sound`) and `SeOpen`:

* `shC tr r s j`: cell `s.j` of `SH` row `r` (table 2 of `Se.fullSe xtape`); `blkOf tr r` its block;
* `ShRun tr f ℓ`: rows `f ≤ ℓ` of `SH` form one hash (a first row, a last row, active non-first
  rows in between);
* `ChipOK tr` (**named premise**, lane B's `Sha512IfContract`, as `AccDef.ChipOK`): every send of
  the chip stub (table 3) is a message of a faithful SHA-512 compression chip;
* `HashOK pub tr s` (proved by `ShSem.sh_sound` for every hash `SE` demands): some byte message `m`
  (a whole number of blocks) hashes to `s`'s digest bytes, and for a fixed-content hash `m` **is**
  `SE`'s padded message `Se.padE s.msg` evaluated on row 0.
-/

namespace M5T1.ShDef

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound M5T1 M5T1.SegRt NearSpecV3.E2E.Bnd
open StateM5a.Sha512If M5T1.AccDef

def shC (tr : Trace Fp) (r : Nat) (s : String) (j : Nat := 0) : Nat := nv tr 2 r (Sh.L.off s + j)

/-- Row `r`'s 128 block bytes. -/
def blkOf (tr : Trace Fp) (r : Nat) : List Nat := (List.range 128).map fun j => shC tr r "blk" j

/-- **One hash of `SH`**: rows `f ≤ ℓ`, `f` first, `ℓ` last, the rows after `f` up to `ℓ` active and
not first. -/
def ShRun (tr : Trace Fp) (f ℓ : Nat) : Prop :=
  f ≤ ℓ ∧ ℓ < tr.height 2 ∧ shC tr f "fst" = 1 ∧ shC tr ℓ "act" = 1 ∧ shC tr ℓ "lst" = 1 ∧
    ∀ i, f < i → i ≤ ℓ → shC tr i "act" = 1 ∧ shC tr i "fst" = 0

/-- The block bytes of rows `f .. f + k − 1`. -/
def msg (tr : Trace Fp) (f k : Nat) : List Nat := (List.range k).flatMap fun i => blkOf tr (f + i)

/-- The chip stub's row `r` (table 3), decoded as an `IF384` message. -/
def chipRow (tr : Trace Fp) (r : Nat) : IfMsg :=
  ⟨nv tr 3 r 1, nv tr 3 r 2, [nv tr 3 r 3, nv tr 3 r 4, nv tr 3 r 5],
    [nv tr 3 r 6, nv tr 3 r 7, nv tr 3 r 8]⟩

/-- **Named premise (lane B's chip contract)**, as `AccDef.ChipOK` on this AIR's stub (table 3). -/
def ChipOK (tr : Trace Fp) : Prop :=
  ∃ chip : List IfMsg, Sha512IfContract cW chip ∧
    ∀ r < tr.height 3, nv tr 3 r 0 ≠ 0 → chipRow tr r ∈ chip

/-- The 42 digest bytes of a hash spec on `SE` row 0. -/
def digOf (pub : List Fp) (tr : Trace Fp) (s : Se.HSpec) : ArenaCore.Bytes :=
  (List.range 42).map fun j => UInt8.ofNat (ev tr 0 0 pub (s.dig j))

/-- **What `SH` establishes for one demanded hash.** -/
def HashOK (pub : List Fp) (tr : Trace Fp) (s : Se.HSpec) : Prop :=
  ∃ m : List Nat, m.length % 128 = 0 ∧ 0 < m.length ∧ (∀ x ∈ m, x < 256) ∧
    (s.fx = true → m = (Se.padE s.msg).map (ev tr 0 0 pub)) ∧ chainDig m = digOf pub tr s

end M5T1.ShDef
