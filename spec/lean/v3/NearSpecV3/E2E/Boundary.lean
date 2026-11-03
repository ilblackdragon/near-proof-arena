import NearSpecV3.E2E.Refined
import NearSpecV3.SHA512

set_option linter.unusedVariables false

/-!
# E2E-M11b, part 4: the concrete boundary encoding (plan §3.2) and `abs`

**The record.** `BndRec` is the plan §3.2 boundary: chunk constants (`claimDigest`), position
(phase tag, block, receipt and action index, `inCall`), clock `t`, state root `stRoot`, gas and
balance totals with the in-flight receipt's counters, the output accumulators, the digest of the
VM answers so far (`vmAcc`, the `K` of `RCM`), and, when `inCall`, the Wasm part (`WasmBnd`: `pc`,
`S`, `stackRem`, frame-chain digest, `memRoot` and `memPages`, globals, registers, VMContext and
promises digests, `codeRoot`/`funcRoot`, the remaining fuel).

**The encoding.** `BndRec.codec` is fixed-width: every counter is 8 big-endian bytes (`u64`), the
balance 16 (`u128`), every digest 42 bytes (U-10), lists carry a `u64` count, the Wasm part a
presence byte. `BndRec.decode_encode` is the round trip on well-formed records (`BndRec.WF`: every
counter in range, every digest 42 bytes), and `BndRec.encode_inj` its injectivity corollary.

**The digest.** `sha384` is FIPS 180-4 §6.5: the SHA-512 compression of `NearSpecV3.SHA512`
with the §5.3.4 initial value, truncated to 48 bytes (`sha384_length`). `bdigest` is its 42-byte
truncation (U-10). The public boundary of a segment is `bdigest (encode (view x))`.

**The abstraction.** What a configuration commits to (`view : RConf → BndRec`: working-set root,
accumulators, Wasm digests) is computed by the circuit lanes; here it is a parameter.
`absD view d` opens a digest to the configuration it commits to (classical choice).
* `absD_bndOf`: `absD view (bndOf view x) = some x`, or `BndCollision view`;
* `bndCollision_split`: a boundary collision is a SHA-384 collision on two distinct encodings, or
  a `view` collision (two configurations with the same record: a binding failure of the
  working-set root or of an accumulator), given `WF` records — the encoding itself is injective;
* `segSoundR_digest`: a segment system whose rows open their two boundary digests to `RCM`
  configurations connected by `RSteps` satisfies `SegSoundR` for the digest boundary with
  `abs := absD view`, with `Bad := BndCollision view`. This is the `Bad` convention of `e2e_sound`.
-/

namespace NearSpecV3.E2E.Bnd
open NearSpec NearSpecV3 NearSpecV3.E2E
open ArenaCore ArenaCore.Bytes

/-! ## SHA-384 -/

/-- SHA-384 initial hash value (FIPS 180-4 §5.3.4). -/
def IV384 : List Nat :=
  [0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
   0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- SHA-384 (FIPS 180-4 §6.5): SHA-512's computation from `IV384`, truncated to 384 bits. -/
def sha384 (m : ArenaCore.Bytes) : ArenaCore.Bytes :=
  let p := SHA512.pad (m.map UInt8.toNat)
  (SHA512.digestBytes (SHA512.blocks (p.length / 128) IV384 p)).take 48

theorem sha384_length (m : ArenaCore.Bytes) : (sha384 m).length = 48 := by
  simp only [sha384, List.length_take,
    SHA512.digestBytes_length _ (SHA512.blocks_length _ IV384 _ rfl)]
  rfl

/-- FIPS 180-4 example: SHA-384 of "abc", evaluated by the kernel. -/
theorem sha384_abc : sha384 (ArenaCore.Bytes.ofString "abc") =
    (ArenaCore.Bytes.ofHex? ("cb00753f45a35e8bb5a03d699ac65007272c32ab0eded163" ++
      "1a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7")).getD [] := by
  decide +kernel

/-- Digest width (U-10: 42-byte SHA-384 digests, 14 BabyBear limbs of 3 bytes). -/
def digestLen : Nat := 42

/-- The boundary digest: SHA-384 truncated to `digestLen` bytes. -/
def bdigest (m : ArenaCore.Bytes) : ArenaCore.Bytes := (sha384 m).take digestLen

theorem bdigest_length (m : ArenaCore.Bytes) : (bdigest m).length = digestLen := by
  simp only [bdigest, List.length_take, sha384_length]; decide

/-! ## Codecs with a round trip -/

/-- An encoder, a prefix decoder, a well-formedness predicate and the round-trip law. -/
structure Codec (α : Type) where
  enc : α → ArenaCore.Bytes
  dec : ArenaCore.Bytes → Option (α × ArenaCore.Bytes)
  ok : α → Prop
  law : ∀ a rest, ok a → dec (enc a ++ rest) = some (a, rest)

theorem take_append_eq {l rest : ArenaCore.Bytes} {w : Nat} (h : l.length = w) :
    (l ++ rest).take w = l := by subst h; simp

theorem drop_append_eq {l rest : ArenaCore.Bytes} {w : Nat} (h : l.length = w) :
    (l ++ rest).drop w = rest := by subst h; simp

/-- Fixed-width big-endian naturals. -/
def natC (w : Nat) : Codec Nat where
  enc n := beN w n
  dec b := if w ≤ b.length then some (beToNat (b.take w), b.drop w) else none
  ok n := n < 256 ^ w
  law := by
    intro n rest h
    have hl := beN_length w n
    simp only [List.length_append, hl, Nat.le_add_right, ite_true, take_append_eq hl,
      drop_append_eq hl, beToNat_beN, Nat.mod_eq_of_lt h]

/-- Fixed-width byte strings (digests). -/
def bytesC (w : Nat) : Codec ArenaCore.Bytes where
  enc d := d
  dec b := if w ≤ b.length then some (b.take w, b.drop w) else none
  ok d := d.length = w
  law := by
    intro d rest h
    simp only [List.length_append, h, Nat.le_add_right, ite_true, take_append_eq h,
      drop_append_eq h]

/-- Booleans as one byte. -/
def boolC : Codec Bool where
  enc x := [if x then 1 else 0]
  dec b := match b with
    | x :: rest => some (x == 1, rest)
    | [] => none
  ok _ := True
  law := by intro x rest _; cases x <;> rfl

/-- Pairs. -/
def pairC {α β : Type} (A : Codec α) (B : Codec β) : Codec (α × β) where
  enc p := A.enc p.1 ++ B.enc p.2
  dec b := match A.dec b with
    | some (a, r) => match B.dec r with
      | some (x, r') => some ((a, x), r')
      | none => none
    | none => none
  ok p := A.ok p.1 ∧ B.ok p.2
  law := by
    intro ⟨a, x⟩ rest ⟨ha, hx⟩
    simp only [List.append_assoc, A.law a _ ha, B.law x rest hx]

/-- Lists with a `u64` count. -/
def listItems {α : Type} (A : Codec α) : Nat → ArenaCore.Bytes → Option (List α × ArenaCore.Bytes)
  | 0, b => some ([], b)
  | n + 1, b => match A.dec b with
    | some (a, r) => match listItems A n r with
      | some (as, r') => some (a :: as, r')
      | none => none
    | none => none

def listC {α : Type} (A : Codec α) : Codec (List α) where
  enc l := beN 8 l.length ++ (l.map A.enc).flatten
  dec b := match (natC 8).dec b with
    | some (n, r) => listItems A n r
    | none => none
  ok l := l.length < 256 ^ 8 ∧ ∀ a ∈ l, A.ok a
  law := by
    intro l rest ⟨hn, ha⟩
    have h1 := (natC 8).law l.length ((l.map A.enc).flatten ++ rest) hn
    simp only [natC] at h1
    simp only [List.append_assoc]
    rw [show (natC 8).dec = fun b => if 8 ≤ b.length then some (beToNat (b.take 8), b.drop 8) else none
      from rfl]
    simp only at h1 ⊢
    rw [h1]
    simp only
    clear h1 hn
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_cons, listItems, List.append_assoc,
        A.law a _ (ha a (by simp))]
      rw [ih (fun x hx => ha x (by simp [hx]))]

/-- Options with a presence byte. -/
def optC {α : Type} (A : Codec α) : Codec (Option α) where
  enc o := match o with
    | none => [0]
    | some a => 1 :: A.enc a
  dec b := match b with
    | 0 :: rest => some (none, rest)
    | 1 :: rest => match A.dec rest with
      | some (a, r) => some (some a, r)
      | none => none
    | _ => none
  ok o := match o with
    | none => True
    | some a => A.ok a
  law := by
    intro o rest h
    cases o with
    | none => rfl
    | some a =>
      show (match (1 : UInt8) :: (A.enc a ++ rest) with
        | 0 :: rest => some (none, rest)
        | 1 :: rest => match A.dec rest with
          | some (a, r) => some (some a, r)
          | none => none
        | _ => none) = _
      simp only [A.law a rest h]

/-- A codec transported along a map with a left inverse. -/
def mapC {α β : Type} (A : Codec α) (f : β → α) (g : α → β) (hgf : ∀ b, g (f b) = b) : Codec β where
  enc b := A.enc (f b)
  dec x := (A.dec x).map fun (a, r) => (g a, r)
  ok b := A.ok (f b)
  law := by intro b rest h; simp only [A.law _ rest h, Option.map_some, hgf]

/-! ## The boundary record (plan §3.2) -/

/-- The Wasm part of a boundary (present iff `inCall`). -/
structure WasmBnd where
  pc : Nat
  sp : Nat
  stackRem : Nat
  fuel : Nat
  framesDigest : ArenaCore.Bytes
  memRoot : ArenaCore.Bytes
  memPages : Nat
  globalsDigest : ArenaCore.Bytes
  registersDigest : ArenaCore.Bytes
  vmCtxDigest : ArenaCore.Bytes
  promisesDigest : ArenaCore.Bytes
  codeRoot : ArenaCore.Bytes
  funcRoot : ArenaCore.Bytes
  deriving DecidableEq

/-- The public boundary `B` of a segment (plan §3.2). -/
structure BndRec where
  claimDigest : ArenaCore.Bytes
  phase : Nat
  blockIdx : Nat
  receiptIdx : Nat
  actionIdx : Nat
  inCall : Bool
  t : Nat
  stRoot : ArenaCore.Bytes
  gasUsed : Nat
  gasBurnt : Nat
  balanceBurnt : Nat
  compute : Nat
  rPrepaid : Nat
  rBurnt : Nat
  rUsed : Nat
  outcomeAcc : ArenaCore.Bytes
  outRcptAcc : List ArenaCore.Bytes
  proposalsAcc : ArenaCore.Bytes
  bwAcc : ArenaCore.Bytes
  vmAcc : ArenaCore.Bytes
  wasm : Option WasmBnd
  deriving DecidableEq

abbrev u64C : Codec Nat := natC 8
abbrev u128C : Codec Nat := natC 16
abbrev digC : Codec ArenaCore.Bytes := bytesC digestLen

def WasmBnd.codec : Codec WasmBnd :=
  mapC (pairC u64C (pairC u64C (pairC u64C (pairC u64C (pairC digC (pairC digC (pairC u64C
      (pairC digC (pairC digC (pairC digC (pairC digC (pairC digC digC))))))))))))
    (fun w => (w.pc, w.sp, w.stackRem, w.fuel, w.framesDigest, w.memRoot, w.memPages,
      w.globalsDigest, w.registersDigest, w.vmCtxDigest, w.promisesDigest, w.codeRoot, w.funcRoot))
    (fun (a, b, c, d, e, f, g, h, i, j, k, l, m) => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩)
    (fun _ => rfl)

def BndRec.codec : Codec BndRec :=
  mapC (pairC digC (pairC u64C (pairC u64C (pairC u64C (pairC u64C (pairC boolC (pairC u64C
      (pairC digC (pairC u64C (pairC u64C (pairC u128C (pairC u64C (pairC u64C (pairC u64C
      (pairC u64C (pairC digC (pairC (listC digC) (pairC digC (pairC digC (pairC digC
      (optC WasmBnd.codec)))))))))))))))))))))
    (fun r => (r.claimDigest, r.phase, r.blockIdx, r.receiptIdx, r.actionIdx, r.inCall, r.t,
      r.stRoot, r.gasUsed, r.gasBurnt, r.balanceBurnt, r.compute, r.rPrepaid, r.rBurnt, r.rUsed,
      r.outcomeAcc, r.outRcptAcc, r.proposalsAcc, r.bwAcc, r.vmAcc, r.wasm))
    (fun (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u) =>
      ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u⟩)
    (fun _ => rfl)

/-- The encoding of a boundary record. -/
def BndRec.encode (r : BndRec) : ArenaCore.Bytes := BndRec.codec.enc r

/-- The decoding (the whole input must be consumed). -/
def BndRec.decode (b : ArenaCore.Bytes) : Option BndRec :=
  match BndRec.codec.dec b with
  | some (r, []) => some r
  | _ => none

/-- Well-formed records: counters in range, digests of `digestLen` bytes, and `inCall` exactly
when the Wasm part is present. -/
def BndRec.WF (r : BndRec) : Prop := BndRec.codec.ok r ∧ (r.inCall = r.wasm.isSome)

/-- **Round trip.** -/
theorem BndRec.decode_encode (r : BndRec) (h : r.WF) : BndRec.decode r.encode = some r := by
  unfold BndRec.decode BndRec.encode
  have := BndRec.codec.law r [] h.1
  rw [List.append_nil] at this
  rw [this]

/-- **The encoding is injective on well-formed records.** -/
theorem BndRec.encode_inj {r s : BndRec} (hr : r.WF) (hs : s.WF) (h : r.encode = s.encode) :
    r = s := by
  have h1 := BndRec.decode_encode r hr
  rw [h, BndRec.decode_encode s hs] at h1
  exact (Option.some.inj h1).symm

/-! ## The digest boundary and its abstraction -/

/-- The public boundary of a configuration under the commitment `view`. -/
def bndOf (view : RConf → BndRec) (x : RConf) : ArenaCore.Bytes := bdigest (view x).encode

/-- **A boundary collision**: two distinct configurations with the same boundary digest. -/
def BndCollision (view : RConf → BndRec) : Prop :=
  ∃ x y, x ≠ y ∧ bndOf view x = bndOf view y

/-- Open a digest to the configuration it commits to. -/
noncomputable def absD (view : RConf → BndRec) (d : ArenaCore.Bytes) : Option RConf :=
  open Classical in
  if h : ∃ x, bndOf view x = d then some (Classical.choose h) else none

/-- **`abs` round trip**: a configuration's own boundary opens to it, or there is a collision. -/
theorem absD_bndOf (view : RConf → BndRec) (x : RConf) :
    absD view (bndOf view x) = some x ∨ BndCollision view := by
  unfold absD
  split
  · rename_i hex
    by_cases hy : Classical.choose hex = x
    · exact .inl (by rw [hy])
    · exact .inr ⟨_, x, hy, Classical.choose_spec hex⟩
  · rename_i hn
    exact absurd ⟨x, rfl⟩ hn

/-- **A boundary collision is a SHA-384 collision or a commitment (`view`) collision.** -/
theorem bndCollision_split (view : RConf → BndRec) (hwf : ∀ x, (view x).WF)
    (h : BndCollision view) :
    (∃ m m' : ArenaCore.Bytes, m ≠ m' ∧ bdigest m = bdigest m') ∨
      (∃ x y, x ≠ y ∧ view x = view y) := by
  obtain ⟨x, y, hne, hd⟩ := h
  by_cases he : (view x).encode = (view y).encode
  · exact .inr ⟨x, y, hne, BndRec.encode_inj (hwf x) (hwf y) he⟩
  · exact .inl ⟨_, _, he, hd⟩

/-- A segment system over digest boundaries: what a segment's rows prove is that its two
boundary digests open to `RCM` configurations connected by a run. -/
def SegOpens {T Tr : Type} (view : RConf → BndRec)
    (Holds : T → ArenaCore.Bytes → ArenaCore.Bytes → Tr → Prop) : Prop :=
  ∀ k d d' tr, Holds k d d' tr → ∃ x x', bndOf view x = d ∧ bndOf view x' = d' ∧ RSteps x x'

/-- The digest segment system with the concrete `abs`. -/
noncomputable def digestSys (T Tr : Type) (view : RConf → BndRec)
    (Holds : T → ArenaCore.Bytes → ArenaCore.Bytes → Tr → Prop) : RSegSystem where
  Template := T
  Bnd := ArenaCore.Bytes
  Trace := Tr
  abs := absD view
  Holds := Holds

/-- **Obligation 2 at the digest boundary**: opening segments give `SegSoundR` with the
collision event as `Bad`. -/
theorem segSoundR_digest {T Tr : Type} (view : RConf → BndRec)
    (Holds : T → ArenaCore.Bytes → ArenaCore.Bytes → Tr → Prop) (h : SegOpens view Holds) :
    SegSoundR (digestSys T Tr view Holds) (BndCollision view) := by
  intro k d d' tr hh
  obtain ⟨x, x', rfl, rfl, hs⟩ := h k d d' tr hh
  rcases absD_bndOf view x with hx | hc
  · rcases absD_bndOf view x' with hx' | hc
    · exact .inr ⟨x, x', hx, hx', hs⟩
    · exact .inl hc
  · exact .inl hc

#print axioms sha384_length
#print axioms sha384_abc
#print axioms BndRec.decode_encode
#print axioms BndRec.encode_inj
#print axioms absD_bndOf
#print axioms bndCollision_split
#print axioms segSoundR_digest

end NearSpecV3.E2E.Bnd
