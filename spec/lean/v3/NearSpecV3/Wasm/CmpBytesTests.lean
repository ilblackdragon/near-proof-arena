import NearSpecV3.Wasm.TrieStore
/-!
# `cmpBytesImpl` agrees with the reference order of `cmpBytes`

`cmpBytes` (the key order of `TTN.BMap`) is the list comparison, which the kernel reduces; compiled
code runs `cmpBytesImpl` (`@[implemented_by]`). The build checks them equal on every pair of byte
arrays of length ≤ 3 over the bytes {0, 1, 127, 128, 255} (156 arrays, 24,336 pairs: equal, prefix,
first/middle/last-byte differences and signedness edges).
-/
namespace NearSpecV3.Wasm.TTN.CmpBytesTests

def alphabet : List UInt8 := [0, 1, 127, 128, 255]

def arrays : List ByteArray :=
  ((List.range 4).flatMap fun n =>
    (List.range n).foldl (fun acc _ => acc.flatMap fun l => alphabet.map (· :: l)) [[]]).map
    fun l => ⟨l.toArray⟩

def mismatches : Nat :=
  arrays.foldl (fun k a => arrays.foldl (fun k b =>
    if cmpBytesImpl a b == compare a.data.toList b.data.toList then k else k + 1) k) 0

#guard arrays.length == 156
#guard mismatches == 0

end NearSpecV3.Wasm.TTN.CmpBytesTests
