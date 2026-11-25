import M5T1.RbSem
import StateM5a.Sha512If

/-!
# M5T1.AccDef — what the `ACC` rows establish, stated (F-4)

Definitions shared by `AccSem` (the proof from the circuit, `acc_sound`) and `ResumeC` (its use):

* `accIn pub h`, `accOut pub h`: the input / output record's accumulator of `hid = h`
  (`0`: `outcomeAcc`, `1`: `outRcpt0`), as public bytes;
* `chainDig m`: SHA-384 over SHA-512 compressions of the block sequence `m` (128 byte values per
  block) from `IV384`, truncated to the 42-B boundary digest — `bdigest e` when `m = pad e`
  (`chainDig_pad`);
* `AccRun tr h f ℓ`: rows `f ≤ ℓ` of `ACC` (table 7) form one hash for `hid = h` (a first row, a
  last row with `hid = h`, active non-first rows in between); `msgOf tr h`: the block bytes of a
  run (chosen), `[]` if there is none;
* `IsAccMsg pub h m`: `m` is a whole number of blocks of bytes whose first 42 bytes are `accIn h`
  and whose chained digest is `accOut h`;
* `ChipOK tr` (**named premise**, lane B's `Sha512IfContract` on the `IF384` stub's sends):
  every send of the chip stub (table 8) is a message of a faithful SHA-512 compression chip
  (`cW`: the spec's `SHA512.compress` on the words' big-endian bytes);
* `AccOK pub tr` (proved by `AccSem.acc_sound`): for both `hid`, the run's message is an
  `IsAccMsg`.
-/

namespace M5T1.AccDef

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View M5T1 M5T1.BndLay M5T1.SegRt M5T1.RbSem
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd StateM5a.Sha512If

/-- The accumulator field of `hid = h`. -/
def accF (h : Nat) : String := if h = 0 then "outcomeAcc" else "outRcpt0"

def accIn (pub : List Fp) (h : Nat) : ArenaCore.Bytes := bytesOf pub (BIN + callF.off (accF h)) 42
def accOut (pub : List Fp) (h : Nat) : ArenaCore.Bytes := bytesOf pub (BOUT + engF.off (accF h)) 42

/-- The chained SHA-384 digest of a block sequence, truncated to 42 bytes. -/
def chainDig (m : List Nat) : ArenaCore.Bytes :=
  (SHA512.digestBytes (SHA512.blocks (m.length / 128) IV384 m)).take 42

/-- **`chainDig` of a padded message is the boundary digest.** -/
theorem chainDig_pad (e : ArenaCore.Bytes) : chainDig (SHA512.pad (e.map UInt8.toNat)) = bdigest e := by
  simp only [chainDig, bdigest, sha384, digestLen, List.take_take]
  rfl

/-- The message of one accumulator append. -/
def IsAccMsg (pub : List Fp) (h : Nat) (m : List Nat) : Prop :=
  m.length % 128 = 0 ∧ 0 < m.length ∧ (∀ x ∈ m, x < 256) ∧
    (m.take 42).map UInt8.ofNat = accIn pub h ∧ accOut pub h = chainDig m

/-! ## `ACC` cells (table 7 of `fullAir`) -/

def accC (tr : Trace Fp) (r : Nat) (s : String) (j : Nat := 0) : Nat := nv tr 7 r (Acc.L.off s + j)

/-- Row `r`'s 128 block bytes. -/
def blkOf (tr : Trace Fp) (r : Nat) : List Nat := (List.range 128).map fun j => accC tr r "blk" j

/-- **One hash of `ACC`**: rows `f ≤ ℓ`, `f` first, `ℓ` last with `hid = h`, the rows after `f` up
to `ℓ` active and not first. -/
def AccRun (tr : Trace Fp) (h f ℓ : Nat) : Prop :=
  f ≤ ℓ ∧ ℓ < tr.height 7 ∧ accC tr f "fst" = 1 ∧ accC tr ℓ "act" = 1 ∧ accC tr ℓ "lst" = 1 ∧
    accC tr ℓ "hid" = h ∧ ∀ i, f < i → i ≤ ℓ → accC tr i "act" = 1 ∧ accC tr i "fst" = 0

/-- The block bytes of a run for `hid = h` (a chosen one; `[]` if there is none). -/
noncomputable def msgOf (tr : Trace Fp) (h : Nat) : List Nat := by
  classical
  exact if hx : ∃ f ℓ, AccRun tr h f ℓ then
    let f := Classical.choose hx
    let ℓ := Classical.choose (Classical.choose_spec hx)
    (List.range (ℓ + 1 - f)).flatMap fun i => blkOf tr (f + i)
  else []

/-- Big-endian bytes of 64-bit words. -/
def wbytes (ws : List Nat) : List Nat :=
  ws.flatMap fun w => (List.range 8).map fun i => w / 256 ^ (7 - i) % 256

/-- **The native chip's compression** at the word level: the spec's SHA-512 compression of the
words' big-endian bytes. -/
def cW (h ws : List Nat) : List Nat := SHA512.compress h (wbytes ws)

/-- The chip stub's row `r` (table 8), decoded as an `IF384` message. -/
def chipRow (tr : Trace Fp) (r : Nat) : IfMsg :=
  ⟨nv tr 8 r 1, nv tr 8 r 2, [nv tr 8 r 3, nv tr 8 r 4, nv tr 8 r 5],
    [nv tr 8 r 6, nv tr 8 r 7, nv tr 8 r 8]⟩

/-- **Named premise (lane B's chip contract)**: the chip stub's sends are messages of a faithful
SHA-512 compression chip. In the deployment the native chip (`s384/`) replaces the stub; its
faithfulness is `results/pq384-sha-air3/FAITHFUL-v4.md` (lane B's `Sha512If`). -/
def ChipOK (tr : Trace Fp) : Prop :=
  ∃ chip : List IfMsg, Sha512IfContract cW chip ∧
    ∀ r < tr.height 8, nv tr 8 r 0 ≠ 0 → chipRow tr r ∈ chip

/-- **What `ACC` establishes** (`AccSem.acc_sound`): both appends hash a message of the right shape
from the input accumulator to the output accumulator. -/
def AccOK (pub : List Fp) (tr : Trace Fp) : Prop := ∀ h < 2, IsAccMsg pub h (msgOf tr h)

#print axioms chainDig_pad

end M5T1.AccDef
