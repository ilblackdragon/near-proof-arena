
/-! B-T4 item 1 (lane B): appended to lane E's `join/StViewE.lean` by `join-check/run.sh`.
**`stD .none` for the view's state instance** (`stViewParams_B stViewE`): the 42-byte constant `stRoot`
of `init cb wb` and `done H o` (`ViewE.viewE`), as lane G's INIT / FINAL wrappers and lane I's
`t1/chain.py` (`ST_NONE`) use it. `StNone.stD_none_eq` reduces it to `bdigest (noneCommit E).ser`
(the empty depth-24 tree, `wsLen = 0`, trie `.hash 0³²`, `idx = 0`, `rest = bdigest (encRestB …)`);
here the kernel evaluates that record for lane E's `stViewE` (25 SHA-384 node hashes of the zero
chain, the remainder and the 139-byte record). -/
namespace LaneB.StNoneE
open NearSpecV3.E2E NearSpecV3.E2E.Bnd StateM5a.StateView StateM5a.StateViewParams StateM5a.StNone
open LaneE.StViewEJoin

/-- `stD .none` for `stViewE` (hex `ST_NONE` in `t1/chain.py`). -/
def stNoneHex : String :=
  "799a6864c921b6955b6a85356d65c7a612fa488d824fcb1d79623dac5a750e820ff93e8510b26828fe9e"

def nib (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
def unhex : List Char → List UInt8
  | a :: b :: r => (nib a * 16 + nib b).toUInt8 :: unhex r
  | _ => []

/-- The constant as bytes. -/
def stNone : List UInt8 := unhex stNoneHex.toList

theorem stViewE_idx : stViewE.idxOf StV.none < 2 ^ 64 := by decide

theorem noneCommit_viewE : bdigest (noneCommit stViewE).ser = stNone := by decide +kernel

/-- **`stD .none` of the view's state instance is the constant `stNone`.** -/
theorem stD_none_viewE : stD (stViewParams_B stViewE) StV.none = stNone := by
  rw [stD_none_eq stViewE stViewE_idx, noneCommit_viewE]

end LaneB.StNoneE
#print axioms LaneB.StNoneE.stD_none_viewE
