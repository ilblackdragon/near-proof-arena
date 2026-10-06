import ZkFormal.V3.Fast.Hash
import ZkFormal.V3.Fast.GF
import NearSpecV3.ReedSolomon

/-!
# Compiled fast path for the Reed–Solomon parity (A5-style `@[csimp]`, V3-D0-DESIGN §5.4)

`RSCode.encodeParts` computes each parity part as a fold of `mulSliceXor` over `List UInt8`
(one fresh list per data part and parity row: `(t−d)·d` lists of length `L`). Here the same
fold runs over `Array UInt8` (`Array.zipWith`), and the kernel-checked theorem
`encodeParts_eq_fast : @RSCode.encodeParts = @RSCode.encodePartsFast` is registered with
`@[csimp]`: compiled code calls the array version; every statement and proof still sees the
specification. `encodedMerkleRoot_eq_fast` (proved by `rfl`: same body, compiled after the
`csimp` lemma) redirects the spec entry point called by `checkD0` / `prepD0`.
No axioms beyond Lean's core ones.
-/

namespace ZkFormal.V3.Fast

open NearSpec NearSpecV3

/-- `mulSliceXor` on arrays. -/
def mulSliceXorA (tbl : Array UInt8) (input out : Array UInt8) : Array UInt8 :=
  Array.zipWith (fun x o => o ^^^ tbl[x.toNat]?.getD 0) input out

theorem mulSliceXorA_toList (tbl : Array UInt8) (input out : Array UInt8) :
    (mulSliceXorA tbl input out).toList = mulSliceXor tbl input.toList out.toList := by
  simp [mulSliceXorA, mulSliceXor, Array.toList_zipWith]

/-- `parityPart` on arrays. -/
def parityPartA (L : Nat) (tbls : List (Array UInt8)) (data : List (Array UInt8)) : Array UInt8 :=
  (List.zip tbls data).foldl (fun acc (tbl, part) => mulSliceXorA tbl part acc) (Array.replicate L 0)

theorem parityFold_toList (tbls : List (Array UInt8)) (data : List (List UInt8)) (acc : Array UInt8) :
    ((List.zip tbls (data.map List.toArray)).foldl
        (fun acc (p : Array UInt8 × Array UInt8) => mulSliceXorA p.1 p.2 acc) acc).toList =
    (List.zip tbls data).foldl (fun acc (p : Array UInt8 × List UInt8) => mulSliceXor p.1 p.2 acc)
      acc.toList := by
  induction tbls generalizing data acc with
  | nil => simp
  | cons t ts ih =>
    cases data with
    | nil => simp
    | cons p ps =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih ps (mulSliceXorA t p.toArray acc), mulSliceXorA_toList]

theorem parityPartA_toList (L : Nat) (tbls : List (Array UInt8)) (data : List (List UInt8)) :
    (parityPartA L tbls (data.map List.toArray)).toList = parityPart L tbls data := by
  unfold parityPartA parityPart
  rw [parityFold_toList]
  simp

/-- `RSCode.encodeParts` with the parity computed on arrays. -/
def RSCode.encodePartsFast (rs : RSCode) (B : List UInt8) : Option (List (List UInt8)) :=
  let L := rsPartLength B.length rs.d
  if L = 0 then none else
  let padded := B ++ List.replicate (rs.d * L - B.length) 0
  let data := chunksExact L rs.d padded
  let dataA := data.map List.toArray
  some (data ++ rs.parityTables.map fun tbls => (parityPartA L tbls dataA).toList)

@[csimp] theorem encodeParts_eq_fast : @RSCode.encodeParts = @RSCode.encodePartsFast := by
  funext rs B
  simp only [RSCode.encodeParts, RSCode.encodePartsFast, parityPartA_toList]

/-- Same body as `partsMerkleRoot`, compiled with the fast SHA-256 and `merkleRoot`. -/
def partsMerkleRootF (parts : List (List UInt8)) : Bytes :=
  merkleRoot (parts.map fun p => sha256 (u32 p.length ++ p))

@[csimp] theorem partsMerkleRoot_eq_F : @partsMerkleRoot = @partsMerkleRootF := rfl

/-- Same body as `encodedMerkleRoot`, compiled after `encodeParts_eq_fast`. -/
def encodedMerkleRootFast (d t : Nat) (B : List UInt8) : Option (NearSpec.Bytes × Nat) := do
  let rs ← RSCode.new d t
  let parts ← rs.encodeParts B
  pure (partsMerkleRoot parts, B.length)

@[csimp] theorem encodedMerkleRoot_eq_fast : @encodedMerkleRoot = @encodedMerkleRootFast := by
  funext d t B
  simp only [encodedMerkleRoot, encodedMerkleRootFast, rsEncode, bind, Option.bind]
  cases RSCode.new d t <;> simp
  rename_i rs
  cases rs.encodeParts B <;> simp

end ZkFormal.V3.Fast
