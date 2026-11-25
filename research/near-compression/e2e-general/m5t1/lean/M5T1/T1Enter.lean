import M5T1.EnterC

/-!
# M5T1.T1Enter — non-vacuity of `enter_relC` on T1's real enter leaf (F-3)

T1's enter leaf (`run.sh … leaves`, lane D's base configuration; 87,739 B) has the public values
`t1EntBytes` (1,284 bytes: `B_in` 450 B, `B_out` 834 B, from lane I's plan in the M11i record shape,
`rtbnd.py`). This file shows that **every hypothesis of `EnterC.enter_relC` holds together** on them:

* `t1_ent_holds` — `Holds Ent.entAir t1EntPub t1EntTr` (the exported AIR, on the leaf's own public
  values and its one-column trace; kernel evaluation of the 762 constraints on the 4 rows);
* `t1_checks` — the named checks: the remainder digest and `rPrepaid` are the query's, the
  `codeRoot`'s first 32 bytes are **`SHA-256` of T1's contract code** (`t1Code`, the 345-B
  `d3tiny` module, hashed in the kernel), the input `stRoot` passes `posOK`;
* `t1_rtView` — a view `V1` meeting every law of `RtView` (store-blind, well-formed, the S2 `.pre`
  record, the clear-field law, the singleton outgoing accumulator, a position check that excludes
  `done`); `V1`'s component values are T1's records (its digests are lane I's placeholders where
  no component exists yet — that is the driver's status, not a property used here);
* `t1_enter_nonvac` — at every non-final engine configuration `eng I c` and every query `q` whose
  code is T1's, all premises hold with `bndOf V1.bnd (eng I c)` = the leaf's input digest, and
  **`t1_enter_opens`** — the conclusion's opening exists: `call I c [] q' .pre` (canonical, `q'` =
  `q` with the context's store) has the leaf's output digest.

(`Intake`, `EConf`, `CallArgs` are inhabited by T1's own run, lane E's `t1_honest_chain`; the
statements are universal in them so that this file needs no 27-GB kernel run.)
-/

namespace M5T1.T1Enter

open ZkFormal.Air ZkFormal.Algebra M5T1 M5T1.BndLay M5T1.SegRt M5T1.EnterC
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1 NearSpecV3.E2E.SB
open NearSpecV3.Wasm NearSpecV3.Wasm.CallCut
open ArenaCore.Bytes (beN)

abbrev Bytes := ArenaCore.Bytes

def t1EntBytesN : List Nat :=
  [187, 90, 173, 17, 186, 107, 163, 45, 145, 115, 159, 19, 162, 219, 213, 68, 242, 66, 13, 119, 11, 205, 44, 63,
   222, 157, 220, 14, 28, 2, 113, 12, 174, 226, 142, 94, 158, 78, 41, 159, 47, 1, 0, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 249, 179, 114, 121, 211, 45, 26, 207, 166, 208, 122, 196, 178,
   224, 19, 36, 8, 117, 197, 44, 241, 162, 114, 135, 34, 241, 85, 42, 88, 61, 48, 103, 121, 63, 19, 109, 35,
   82, 192, 240, 21, 247, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 132, 96, 83, 57, 112, 0, 0, 0, 132, 96, 83, 57, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132, 96, 83, 57, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 90, 173, 17, 186, 107,
   163, 45, 145, 115, 159, 19, 162, 219, 213, 68, 242, 66, 13, 119, 11, 205, 44, 63, 222, 157, 220, 14, 28, 2,
   113, 12, 174, 226, 142, 94, 158, 78, 41, 159, 47, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 0, 249, 179, 114, 121, 211, 45, 26, 207, 166, 208, 122, 196, 178, 224, 19, 36, 8, 117, 197,
   44, 241, 162, 114, 135, 34, 241, 85, 42, 88, 61, 48, 103, 121, 63, 19, 109, 35, 82, 192, 240, 21, 247, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132, 96, 83, 57,
   112, 0, 0, 0, 132, 96, 83, 57, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 132, 96, 83, 57, 112, 0, 0, 49, 28, 218, 209, 96, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 56, 176, 96, 167, 81, 172, 150, 56, 76, 217, 50, 126, 177, 177, 227, 106, 33, 253, 183, 17,
   20, 190, 7, 67, 76, 12, 199, 191, 99, 246, 225, 218, 39, 78, 222, 191, 231, 111, 101, 251, 213, 26, 56, 176,
   96, 167, 81, 172, 150, 56, 76, 217, 50, 126, 177, 177, 227, 106, 33, 253, 183, 17, 20, 190, 7, 67, 76, 12,
   199, 191, 99, 246, 225, 218, 39, 78, 222, 191, 231, 111, 101, 251, 213, 26, 0, 0, 0, 0, 0, 0, 0, 0,
   56, 176, 96, 167, 81, 172, 150, 56, 76, 217, 50, 126, 177, 177, 227, 106, 33, 253, 183, 17, 20, 190, 7, 67,
   76, 12, 199, 191, 99, 246, 225, 218, 39, 78, 222, 191, 231, 111, 101, 251, 213, 26, 56, 176, 96, 167, 81, 172,
   150, 56, 76, 217, 50, 126, 177, 177, 227, 106, 33, 253, 183, 17, 20, 190, 7, 67, 76, 12, 199, 191, 99, 246,
   225, 218, 39, 78, 222, 191, 231, 111, 101, 251, 213, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 56, 176, 96, 167, 81, 172, 150, 56, 76, 217, 50, 126, 177, 177, 227, 106, 33, 253,
   183, 17, 20, 190, 7, 67, 76, 12, 199, 191, 99, 246, 225, 218, 39, 78, 222, 191, 231, 111, 101, 251, 213, 26,
   129, 82, 190, 210, 85, 84, 213, 33, 211, 252, 221, 145, 159, 68, 87, 182, 110, 6, 183, 32, 144, 111, 221, 64,
   253, 111, 208, 114, 62, 211, 107, 249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 176, 96, 167, 81, 172,
   150, 56, 76, 217, 50, 126, 177, 177, 227, 106, 33, 253, 183, 17, 20, 190, 7, 67, 76, 12, 199, 191, 99, 246,
   225, 218, 39, 78, 222, 191, 231, 111, 101, 251, 213, 26]
def t1EntBytes : Bytes := t1EntBytesN.map UInt8.ofNat

def t1CodeN : List Nat :=
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 27, 5, 96, 1, 126, 0, 96, 1, 126, 1, 126, 96, 2, 126, 126,
   0, 96, 5, 126, 126, 126, 126, 126, 1, 126, 96, 0, 0, 2, 106, 6, 3, 101, 110, 118, 5, 105, 110, 112,
   117, 116, 0, 0, 3, 101, 110, 118, 12, 114, 101, 103, 105, 115, 116, 101, 114, 95, 108, 101, 110, 0, 1, 3,
   101, 110, 118, 13, 114, 101, 97, 100, 95, 114, 101, 103, 105, 115, 116, 101, 114, 0, 2, 3, 101, 110, 118, 13,
   115, 116, 111, 114, 97, 103, 101, 95, 119, 114, 105, 116, 101, 0, 3, 3, 101, 110, 118, 8, 108, 111, 103, 95,
   117, 116, 102, 56, 0, 2, 3, 101, 110, 118, 12, 118, 97, 108, 117, 101, 95, 114, 101, 116, 117, 114, 110, 0,
   2, 3, 2, 1, 4, 5, 3, 1, 0, 1, 7, 12, 2, 3, 114, 117, 110, 0, 6, 2, 99, 98, 0, 6,
   10, 63, 1, 61, 1, 1, 126, 66, 0, 16, 0, 66, 0, 16, 1, 33, 0, 32, 0, 66, 224, 212, 3, 86,
   4, 64, 66, 224, 212, 3, 33, 0, 11, 66, 0, 66, 16, 16, 2, 66, 1, 66, 0, 32, 0, 66, 16, 66,
   1, 16, 3, 26, 66, 4, 66, 1, 16, 4, 32, 0, 66, 16, 16, 5, 11, 11, 11, 1, 0, 65, 0, 11,
   5, 116, 116, 105, 110, 121, 0, 97, 4, 110, 97, 109, 101, 1, 82, 7, 0, 5, 105, 110, 112, 117, 116, 1,
   12, 114, 101, 103, 105, 115, 116, 101, 114, 95, 108, 101, 110, 2, 13, 114, 101, 97, 100, 95, 114, 101, 103, 105,
   115, 116, 101, 114, 3, 13, 115, 116, 111, 114, 97, 103, 101, 95, 119, 114, 105, 116, 101, 4, 8, 108, 111, 103,
   95, 117, 116, 102, 56, 5, 12, 118, 97, 108, 117, 101, 95, 114, 101, 116, 117, 114, 110, 6, 4, 109, 97, 105,
   110, 2, 6, 1, 6, 1, 0, 1, 110]
def t1Code : Bytes := t1CodeN.map UInt8.ofNat

def t1_claimDigestN : List Nat :=
  [187, 90, 173, 17, 186, 107, 163, 45, 145, 115, 159, 19, 162, 219, 213, 68, 242, 66, 13, 119, 11, 205, 44, 63,
   222, 157, 220, 14, 28, 2, 113, 12, 174, 226, 142, 94, 158, 78, 41, 159, 47, 1]
def t1_claimDigest : Bytes := t1_claimDigestN.map UInt8.ofNat

def t1_stRootN : List Nat :=
  [249, 179, 114, 121, 211, 45, 26, 207, 166, 208, 122, 196, 178, 224, 19, 36, 8, 117, 197, 44, 241, 162, 114, 135,
   34, 241, 85, 42, 88, 61, 48, 103, 121, 63, 19, 109, 35, 82, 192, 240, 21, 247]
def t1_stRoot : Bytes := t1_stRootN.map UInt8.ofNat

def t1_ctxRootN : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_ctxRoot : Bytes := t1_ctxRootN.map UInt8.ofNat

def t1_outcomeAccN : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_outcomeAcc : Bytes := t1_outcomeAccN.map UInt8.ofNat

def t1_proposalsAccN : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_proposalsAcc : Bytes := t1_proposalsAccN.map UInt8.ofNat

def t1_bwAccN : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_bwAcc : Bytes := t1_bwAccN.map UInt8.ofNat

def t1_vmAccN : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_vmAcc : Bytes := t1_vmAccN.map UInt8.ofNat

def t1_outRcpt0N : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_outRcpt0 : Bytes := t1_outRcpt0N.map UInt8.ofNat

def t1_vmCtxN : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def t1_vmCtx : Bytes := t1_vmCtxN.map UInt8.ofNat

/-- The leaf's public values as field elements (one byte per value). -/
def t1EntPub : List Fp :=
  [Fp.ofNat 187, Fp.ofNat 90, Fp.ofNat 173, Fp.ofNat 17, Fp.ofNat 186, Fp.ofNat 107, Fp.ofNat 163, Fp.ofNat 45, Fp.ofNat 145, Fp.ofNat 115, Fp.ofNat 159, Fp.ofNat 19,
   Fp.ofNat 162, Fp.ofNat 219, Fp.ofNat 213, Fp.ofNat 68, Fp.ofNat 242, Fp.ofNat 66, Fp.ofNat 13, Fp.ofNat 119, Fp.ofNat 11, Fp.ofNat 205, Fp.ofNat 44, Fp.ofNat 63,
   Fp.ofNat 222, Fp.ofNat 157, Fp.ofNat 220, Fp.ofNat 14, Fp.ofNat 28, Fp.ofNat 2, Fp.ofNat 113, Fp.ofNat 12, Fp.ofNat 174, Fp.ofNat 226, Fp.ofNat 142, Fp.ofNat 94,
   Fp.ofNat 158, Fp.ofNat 78, Fp.ofNat 41, Fp.ofNat 159, Fp.ofNat 47, Fp.ofNat 1, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 1, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 1, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 249,
   Fp.ofNat 179, Fp.ofNat 114, Fp.ofNat 121, Fp.ofNat 211, Fp.ofNat 45, Fp.ofNat 26, Fp.ofNat 207, Fp.ofNat 166, Fp.ofNat 208, Fp.ofNat 122, Fp.ofNat 196, Fp.ofNat 178,
   Fp.ofNat 224, Fp.ofNat 19, Fp.ofNat 36, Fp.ofNat 8, Fp.ofNat 117, Fp.ofNat 197, Fp.ofNat 44, Fp.ofNat 241, Fp.ofNat 162, Fp.ofNat 114, Fp.ofNat 135, Fp.ofNat 34,
   Fp.ofNat 241, Fp.ofNat 85, Fp.ofNat 42, Fp.ofNat 88, Fp.ofNat 61, Fp.ofNat 48, Fp.ofNat 103, Fp.ofNat 121, Fp.ofNat 63, Fp.ofNat 19, Fp.ofNat 109, Fp.ofNat 35,
   Fp.ofNat 82, Fp.ofNat 192, Fp.ofNat 240, Fp.ofNat 21, Fp.ofNat 247, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 132, Fp.ofNat 96, Fp.ofNat 83, Fp.ofNat 57, Fp.ofNat 112, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 132, Fp.ofNat 96,
   Fp.ofNat 83, Fp.ofNat 57, Fp.ofNat 112, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 132, Fp.ofNat 96,
   Fp.ofNat 83, Fp.ofNat 57, Fp.ofNat 112, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 1, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 187, Fp.ofNat 90, Fp.ofNat 173, Fp.ofNat 17, Fp.ofNat 186, Fp.ofNat 107,
   Fp.ofNat 163, Fp.ofNat 45, Fp.ofNat 145, Fp.ofNat 115, Fp.ofNat 159, Fp.ofNat 19, Fp.ofNat 162, Fp.ofNat 219, Fp.ofNat 213, Fp.ofNat 68, Fp.ofNat 242, Fp.ofNat 66,
   Fp.ofNat 13, Fp.ofNat 119, Fp.ofNat 11, Fp.ofNat 205, Fp.ofNat 44, Fp.ofNat 63, Fp.ofNat 222, Fp.ofNat 157, Fp.ofNat 220, Fp.ofNat 14, Fp.ofNat 28, Fp.ofNat 2,
   Fp.ofNat 113, Fp.ofNat 12, Fp.ofNat 174, Fp.ofNat 226, Fp.ofNat 142, Fp.ofNat 94, Fp.ofNat 158, Fp.ofNat 78, Fp.ofNat 41, Fp.ofNat 159, Fp.ofNat 47, Fp.ofNat 1,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 6, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 1,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 1, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 249, Fp.ofNat 179, Fp.ofNat 114, Fp.ofNat 121, Fp.ofNat 211, Fp.ofNat 45, Fp.ofNat 26,
   Fp.ofNat 207, Fp.ofNat 166, Fp.ofNat 208, Fp.ofNat 122, Fp.ofNat 196, Fp.ofNat 178, Fp.ofNat 224, Fp.ofNat 19, Fp.ofNat 36, Fp.ofNat 8, Fp.ofNat 117, Fp.ofNat 197,
   Fp.ofNat 44, Fp.ofNat 241, Fp.ofNat 162, Fp.ofNat 114, Fp.ofNat 135, Fp.ofNat 34, Fp.ofNat 241, Fp.ofNat 85, Fp.ofNat 42, Fp.ofNat 88, Fp.ofNat 61, Fp.ofNat 48,
   Fp.ofNat 103, Fp.ofNat 121, Fp.ofNat 63, Fp.ofNat 19, Fp.ofNat 109, Fp.ofNat 35, Fp.ofNat 82, Fp.ofNat 192, Fp.ofNat 240, Fp.ofNat 21, Fp.ofNat 247, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 132, Fp.ofNat 96, Fp.ofNat 83, Fp.ofNat 57,
   Fp.ofNat 112, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 132, Fp.ofNat 96, Fp.ofNat 83, Fp.ofNat 57, Fp.ofNat 112, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 132, Fp.ofNat 96, Fp.ofNat 83, Fp.ofNat 57, Fp.ofNat 112, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 49,
   Fp.ofNat 28, Fp.ofNat 218, Fp.ofNat 209, Fp.ofNat 96, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 1, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 1,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 56, Fp.ofNat 176, Fp.ofNat 96, Fp.ofNat 167, Fp.ofNat 81, Fp.ofNat 172, Fp.ofNat 150, Fp.ofNat 56,
   Fp.ofNat 76, Fp.ofNat 217, Fp.ofNat 50, Fp.ofNat 126, Fp.ofNat 177, Fp.ofNat 177, Fp.ofNat 227, Fp.ofNat 106, Fp.ofNat 33, Fp.ofNat 253, Fp.ofNat 183, Fp.ofNat 17,
   Fp.ofNat 20, Fp.ofNat 190, Fp.ofNat 7, Fp.ofNat 67, Fp.ofNat 76, Fp.ofNat 12, Fp.ofNat 199, Fp.ofNat 191, Fp.ofNat 99, Fp.ofNat 246, Fp.ofNat 225, Fp.ofNat 218,
   Fp.ofNat 39, Fp.ofNat 78, Fp.ofNat 222, Fp.ofNat 191, Fp.ofNat 231, Fp.ofNat 111, Fp.ofNat 101, Fp.ofNat 251, Fp.ofNat 213, Fp.ofNat 26, Fp.ofNat 56, Fp.ofNat 176,
   Fp.ofNat 96, Fp.ofNat 167, Fp.ofNat 81, Fp.ofNat 172, Fp.ofNat 150, Fp.ofNat 56, Fp.ofNat 76, Fp.ofNat 217, Fp.ofNat 50, Fp.ofNat 126, Fp.ofNat 177, Fp.ofNat 177,
   Fp.ofNat 227, Fp.ofNat 106, Fp.ofNat 33, Fp.ofNat 253, Fp.ofNat 183, Fp.ofNat 17, Fp.ofNat 20, Fp.ofNat 190, Fp.ofNat 7, Fp.ofNat 67, Fp.ofNat 76, Fp.ofNat 12,
   Fp.ofNat 199, Fp.ofNat 191, Fp.ofNat 99, Fp.ofNat 246, Fp.ofNat 225, Fp.ofNat 218, Fp.ofNat 39, Fp.ofNat 78, Fp.ofNat 222, Fp.ofNat 191, Fp.ofNat 231, Fp.ofNat 111,
   Fp.ofNat 101, Fp.ofNat 251, Fp.ofNat 213, Fp.ofNat 26, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 56, Fp.ofNat 176, Fp.ofNat 96, Fp.ofNat 167, Fp.ofNat 81, Fp.ofNat 172, Fp.ofNat 150, Fp.ofNat 56, Fp.ofNat 76, Fp.ofNat 217, Fp.ofNat 50, Fp.ofNat 126,
   Fp.ofNat 177, Fp.ofNat 177, Fp.ofNat 227, Fp.ofNat 106, Fp.ofNat 33, Fp.ofNat 253, Fp.ofNat 183, Fp.ofNat 17, Fp.ofNat 20, Fp.ofNat 190, Fp.ofNat 7, Fp.ofNat 67,
   Fp.ofNat 76, Fp.ofNat 12, Fp.ofNat 199, Fp.ofNat 191, Fp.ofNat 99, Fp.ofNat 246, Fp.ofNat 225, Fp.ofNat 218, Fp.ofNat 39, Fp.ofNat 78, Fp.ofNat 222, Fp.ofNat 191,
   Fp.ofNat 231, Fp.ofNat 111, Fp.ofNat 101, Fp.ofNat 251, Fp.ofNat 213, Fp.ofNat 26, Fp.ofNat 56, Fp.ofNat 176, Fp.ofNat 96, Fp.ofNat 167, Fp.ofNat 81, Fp.ofNat 172,
   Fp.ofNat 150, Fp.ofNat 56, Fp.ofNat 76, Fp.ofNat 217, Fp.ofNat 50, Fp.ofNat 126, Fp.ofNat 177, Fp.ofNat 177, Fp.ofNat 227, Fp.ofNat 106, Fp.ofNat 33, Fp.ofNat 253,
   Fp.ofNat 183, Fp.ofNat 17, Fp.ofNat 20, Fp.ofNat 190, Fp.ofNat 7, Fp.ofNat 67, Fp.ofNat 76, Fp.ofNat 12, Fp.ofNat 199, Fp.ofNat 191, Fp.ofNat 99, Fp.ofNat 246,
   Fp.ofNat 225, Fp.ofNat 218, Fp.ofNat 39, Fp.ofNat 78, Fp.ofNat 222, Fp.ofNat 191, Fp.ofNat 231, Fp.ofNat 111, Fp.ofNat 101, Fp.ofNat 251, Fp.ofNat 213, Fp.ofNat 26,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 56, Fp.ofNat 176, Fp.ofNat 96, Fp.ofNat 167, Fp.ofNat 81, Fp.ofNat 172,
   Fp.ofNat 150, Fp.ofNat 56, Fp.ofNat 76, Fp.ofNat 217, Fp.ofNat 50, Fp.ofNat 126, Fp.ofNat 177, Fp.ofNat 177, Fp.ofNat 227, Fp.ofNat 106, Fp.ofNat 33, Fp.ofNat 253,
   Fp.ofNat 183, Fp.ofNat 17, Fp.ofNat 20, Fp.ofNat 190, Fp.ofNat 7, Fp.ofNat 67, Fp.ofNat 76, Fp.ofNat 12, Fp.ofNat 199, Fp.ofNat 191, Fp.ofNat 99, Fp.ofNat 246,
   Fp.ofNat 225, Fp.ofNat 218, Fp.ofNat 39, Fp.ofNat 78, Fp.ofNat 222, Fp.ofNat 191, Fp.ofNat 231, Fp.ofNat 111, Fp.ofNat 101, Fp.ofNat 251, Fp.ofNat 213, Fp.ofNat 26,
   Fp.ofNat 129, Fp.ofNat 82, Fp.ofNat 190, Fp.ofNat 210, Fp.ofNat 85, Fp.ofNat 84, Fp.ofNat 213, Fp.ofNat 33, Fp.ofNat 211, Fp.ofNat 252, Fp.ofNat 221, Fp.ofNat 145,
   Fp.ofNat 159, Fp.ofNat 68, Fp.ofNat 87, Fp.ofNat 182, Fp.ofNat 110, Fp.ofNat 6, Fp.ofNat 183, Fp.ofNat 32, Fp.ofNat 144, Fp.ofNat 111, Fp.ofNat 221, Fp.ofNat 64,
   Fp.ofNat 253, Fp.ofNat 111, Fp.ofNat 208, Fp.ofNat 114, Fp.ofNat 62, Fp.ofNat 211, Fp.ofNat 107, Fp.ofNat 249, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0,
   Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 0, Fp.ofNat 56, Fp.ofNat 176, Fp.ofNat 96, Fp.ofNat 167, Fp.ofNat 81, Fp.ofNat 172,
   Fp.ofNat 150, Fp.ofNat 56, Fp.ofNat 76, Fp.ofNat 217, Fp.ofNat 50, Fp.ofNat 126, Fp.ofNat 177, Fp.ofNat 177, Fp.ofNat 227, Fp.ofNat 106, Fp.ofNat 33, Fp.ofNat 253,
   Fp.ofNat 183, Fp.ofNat 17, Fp.ofNat 20, Fp.ofNat 190, Fp.ofNat 7, Fp.ofNat 67, Fp.ofNat 76, Fp.ofNat 12, Fp.ofNat 199, Fp.ofNat 191, Fp.ofNat 99, Fp.ofNat 246,
   Fp.ofNat 225, Fp.ofNat 218, Fp.ofNat 39, Fp.ofNat 78, Fp.ofNat 222, Fp.ofNat 191, Fp.ofNat 231, Fp.ofNat 111, Fp.ofNat 101, Fp.ofNat 251, Fp.ofNat 213, Fp.ofNat 26]

/-- The leaf's trace (one zero column, 4 rows). -/
def t1EntTr : Trace Fp := ⟨fun _ => 2, fun _ _ _ => Fp.ofNat 0⟩

/-- Every `ENT` constraint is `isFirst`-gated. -/
def isGate : Expr → Bool
  | .mul .isFirst _ => true
  | _ => false

theorem ent_gates : ∀ e ∈ Ent.table.constraints, isGate e = true := by decide +kernel

theorem gate_row {e : Expr} (h : isGate e = true) {r : Nat} (hr : r ≠ 0) (tr : Trace Fp)
    (pub : List Fp) : e.eval tr 0 r pub = 0 := by
  match e, h with
  | .mul .isFirst x, _ =>
    show (if r = 0 then (1 : Fp) else 0) * x.eval tr 0 r pub = 0
    simp only [hr, if_false]
    exact Lean.Grind.Semiring.zero_mul _

theorem mem_chunks {α : Type} (n : Nat) : ∀ (m : Nat) (l : List α), l.length ≤ n * m →
    ∀ e ∈ l, ∃ k < m, e ∈ (l.drop (n * k)).take n
  | 0, l, h, e, he => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp at he
  | m + 1, l, h, e, he => by
    rw [← List.take_append_drop n l, List.mem_append] at he
    rcases he with he | he
    · exact ⟨0, by omega, by simpa using he⟩
    · obtain ⟨k, hk, he'⟩ := mem_chunks n m (l.drop n)
        (by rw [List.length_drop]; rw [Nat.mul_succ] at h; omega) e he
      refine ⟨k + 1, by omega, ?_⟩
      rwa [List.drop_drop, show n + n * k = n * (k + 1) by rw [Nat.mul_succ]; omega] at he'

/-! Row 0: the 762 constraints on T1's public values, by kernel evaluation in chunks of 100 (each
chunk is one declaration, which bounds the kernel's memory). -/
theorem t1_row0_0 : ∀ e ∈ (Ent.table.constraints.drop 0).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_1 : ∀ e ∈ (Ent.table.constraints.drop 100).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_2 : ∀ e ∈ (Ent.table.constraints.drop 200).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_3 : ∀ e ∈ (Ent.table.constraints.drop 300).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_4 : ∀ e ∈ (Ent.table.constraints.drop 400).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_5 : ∀ e ∈ (Ent.table.constraints.drop 500).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_6 : ∀ e ∈ (Ent.table.constraints.drop 600).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel
theorem t1_row0_7 : ∀ e ∈ (Ent.table.constraints.drop 700).take 100,
    e.eval t1EntTr 0 0 t1EntPub = 0 := by decide +kernel

theorem t1_row0 : ∀ e ∈ Ent.table.constraints, e.eval t1EntTr 0 0 t1EntPub = 0 := by
  intro e he
  obtain ⟨k, hk, he⟩ := mem_chunks 100 8 _ (by decide +kernel) e he
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t1_row0_0 e he
  · exact t1_row0_1 e he
  · exact t1_row0_2 e he
  · exact t1_row0_3 e he
  · exact t1_row0_4 e he
  · exact t1_row0_5 e he
  · exact t1_row0_6 e he
  · exact t1_row0_7 e he

/-- **The exported enter AIR holds on T1's leaf.** -/
theorem t1_ent_holds : Holds Ent.entAir t1EntPub t1EntTr where
  logBound := by decide +kernel
  constr := by
    intro t ht r _ e he
    have : t = 0 := by simp [Ent.entAir] at ht; omega
    subst this
    by_cases hr : r = 0
    · subst hr; exact t1_row0 e he
    · exact gate_row (ent_gates e he) hr _ _
  bits := by
    intro t ht r _ i hi
    have : t = 0 := by simp [Ent.entAir] at ht; omega
    subst this
    simp [Ent.entAir, Ent.table] at hi
  balance := by
    intro b m
    simp [busCount, busCount.go, tableBusCount, Ent.entAir, Ent.table]

theorem t1_pub_map : t1EntPub = t1EntBytesN.map Fp.ofNat := by decide +kernel
theorem t1_lt : ∀ x ∈ t1EntBytesN, x < 256 := by decide +kernel

theorem t1_bytes : ∀ i < 1284, pv t1EntPub i < 256 := by
  intro i _
  simp only [pv, t1_pub_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : t1EntBytesN[i]? with
  | none => show (Fp.ofNat 0).toNat < 256; rw [Fp.toNat_ofNat]; decide
  | some x =>
    have hx := t1_lt x (List.mem_of_getElem? h)
    simp only [Option.map_some, Option.getD_some, Fp.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx

/-! ## The view `V1` -/

def zero42 : Bytes := List.replicate 42 0

/-- The clear fields of T1's `B_in` (lane I's driver: the Lean run's counters). -/
def t1Clear : ClearF := ⟨t1_claimDigest, 0, 1, 0, 0, 568551750000, 568551750000, 0, 568551750000, 0, 0, 0⟩

def vmc1 (_ : CallArgs) : Bytes := t1_vmCtx
def pre1 (_ : CallArgs) : Nat := 54000000000000
def posOK1 (b : Bytes) : Prop := b = t1_stRoot

def stD1 : StV → Bytes
  | .eng (.done _) _ => zero42
  | _ => t1_stRoot

def V1 : ViewImpl where
  keys := fun _ => []
  clear := fun x => match x with
    | .call .. => { t1Clear with rPrepaid := 54000000000000 }
    | .base _ => t1Clear
  ctxD := fun _ => t1_ctxRoot
  stD := stD1
  outD := fun _ => (t1_outcomeAcc, [t1_outRcpt0], t1_proposalsAcc, t1_bwAcc)
  vmD := fun _ => t1_vmAcc
  wasmD := fun w => w.map fun e => preRec (vmc1 e.1) e.1

theorem len42 : t1_claimDigest.length = 42 ∧ t1_stRoot.length = 42 ∧ t1_ctxRoot.length = 42 ∧
    t1_outcomeAcc.length = 42 ∧ t1_outRcpt0.length = 42 ∧ t1_proposalsAcc.length = 42 ∧
    t1_bwAcc.length = 42 ∧ t1_vmAcc.length = 42 ∧ t1_vmCtx.length = 42 ∧ zero42.length = 42 := by
  decide +kernel

theorem stD1_len (v : StV) : (stD1 v).length = 42 := by
  unfold stD1; split
  · exact len42.2.2.2.2.2.2.2.2.2
  · exact len42.2.1

theorem preRec_ok (q : CallArgs) : WasmBnd.codec.ok (preRec (vmc1 q) q) := by
  simp only [WasmBnd.codec, mapC, pairC, natC, bytesC, preRec, vmc1, bdigest_length,
    preCodeRoot_length, len42.2.2.2.2.2.2.2.2.1]
  decide

theorem t1_wf (x : RConf) : (V1.bnd x).WF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ := len42
  refine ⟨?_, rfl⟩
  cases x with
  | base c =>
    cases c <;>
      simp [ViewImpl.bnd, V1, split, BndRec.codec, mapC, pairC, natC, bytesC, listC, optC, boolC,
        t1Clear, digestLen, h1, h3, h4, h5, h6, h7, h8, stD1_len]
  | call I c K q cc =>
    have := preRec_ok q
    simp [ViewImpl.bnd, V1, split, BndRec.codec, mapC, pairC, natC, bytesC, listC, optC, boolC,
      t1Clear, digestLen, h1, h3, h4, h5, h6, h7, h8, stD1_len, this]

theorem zero42_ne : zero42 ≠ t1_stRoot := by decide +kernel

/-- **`V1` meets every view law of `RtView`.** -/
theorem t1_rtView : RtView V1 vmc1 pre1 posOK1 where
  wf := t1_wf
  blind := by
    intro x
    cases x with
    | base c => rfl
    | call I c K q cc => rfl
  noWasm := rfl
  preW := fun _ => rfl
  clearEnter := fun _ _ _ => rfl
  outOne := fun _ => rfl
  pos := by
    intro I c h out hc
    simp only [posOK1, V1, stOfI, hc, eposMap, stD1] at h
    exact zero42_ne h

/-! ## The named checks and the input opening -/

theorem t1_checks (q : CallArgs) (hq : q.code = ⟨t1Code.toArray⟩) :
    EntChecks vmc1 pre1 posOK1 t1EntPub q where
  vm := by show bytesOf t1EntPub (450 + callF.off "vmCtxDigest") 42 = t1_vmCtx; decide +kernel
  prepaid := by show bytesOf t1EntPub (450 + callF.off "rPrepaid") 8 = beN 8 54000000000000; decide +kernel
  code := by
    rw [hq]
    show bytesOf t1EntPub (450 + callF.off "codeRoot") 32 = ArenaCore.sha256 t1Code.toArray.toList
    rw [List.toList_toArray]
    decide +kernel
  pos := by show bytesOf t1EntPub (engF.off "stRoot") 42 = t1_stRoot; decide +kernel

/-- `V1`'s record of a non-final engine configuration. -/
def R1 : BndRec :=
  { claimDigest := t1_claimDigest, phase := 1, blockIdx := 0, receiptIdx := 1, actionIdx := 0,
    inCall := false, t := 0, stRoot := t1_stRoot, ctxRoot := t1_ctxRoot, gasUsed := 568551750000,
    gasBurnt := 568551750000, balanceBurnt := 0, compute := 568551750000, rPrepaid := 0, rBurnt := 0,
    rUsed := 0, outcomeAcc := t1_outcomeAcc, outRcptAcc := [t1_outRcpt0],
    proposalsAcc := t1_proposalsAcc, bwAcc := t1_bwAcc, vmAcc := t1_vmAcc, wasm := none }

theorem R1_enc : R1.encode = bytesOf t1EntPub 0 450 := by decide +kernel

theorem t1_in (I : Intake) (c : EConf) (hc : ∀ out, c.pos ≠ .done out) :
    V1.bnd (.base (.eng I c)) = R1 := by
  have hs : stD1 (stOfI (fun _ => []) I c) = t1_stRoot := by
    unfold stOfI
    cases h : c.pos with
    | done out => exact absurd h (hc out)
    | _ => rfl
  simp only [ViewImpl.bnd, V1, split, hs]
  rfl

/-- **Every premise of `enter_relC` holds on T1's enter leaf.** -/
theorem t1_enter_nonvac (sf : Intake → TTN.Store) (I : Intake) (c : EConf)
    (hc : ∀ out, c.pos ≠ .done out) (q : CallArgs) (hq : q.code = ⟨t1Code.toArray⟩) :
    RtView V1 vmc1 pre1 posOK1 ∧
      EntHoldsC vmc1 pre1 posOK1 (bdigest (bytesOf t1EntPub 0 450)) (bdigest (bytesOf t1EntPub 450 834))
        (t1EntPub, t1EntTr, q) ∧
      Canon sf (.base (.eng I c)) ∧ bndOf V1.bnd (.base (.eng I c)) = bdigest (bytesOf t1EntPub 0 450) :=
  ⟨t1_rtView, ⟨t1_ent_holds, t1_bytes, rfl, rfl, t1_checks q hq⟩, trivial,
    by simp only [bndOf]; rw [t1_in I c hc, R1_enc]⟩

/-- **The conclusion's opening exists on T1**: the canonical `call I c [] q' .pre` has the leaf's
output digest and is an `MRt.enter` successor. -/
theorem t1_enter_opens (sf : Intake → TTN.Store) (I : Intake) (c : EConf)
    (hc : ∀ out, c.pos ≠ .done out) (q : CallArgs) (hq : q.code = ⟨t1Code.toArray⟩) :
    ∃ x', Canon sf x' ∧ bndOf V1.bnd x' = bdigest (bytesOf t1EntPub 450 834) ∧
      Meaning .rt (.base (.eng I c)) x' := by
  have he : (V1.bnd (.base (.eng I c))).encode = bytesOf t1EntPub 0 450 := by rw [t1_in I c hc, R1_enc]
  obtain ⟨I', c', hx, hnf, hcan, ho⟩ := enter_open t1_rtView sf t1_ent_holds (t1_checks q hq) _ he
  simp only [RConf.base.injEq, Conf.eng.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  exact ⟨_, hcan, by simp only [bndOf]; rw [ho], .enter I c _ hnf⟩

#print axioms t1_ent_holds
#print axioms t1_rtView
#print axioms t1_checks
#print axioms t1_enter_nonvac
#print axioms t1_enter_opens

end M5T1.T1Enter
