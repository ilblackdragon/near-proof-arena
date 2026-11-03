import WasmBase.M2Air
/-!
# WasmBase.SegAir — the E2E M4 segment AIR (`wasmBaseSegAir`): a Wasm call cut mid-call

A long call is proved as a chain of **segments**.  A segment proves the instruction rows with
global timestamps `t_in + 1 … t_out` (the M2 chips, unchanged) between two public **boundaries**.
Inside a segment memory, locals, the operand stack, globals, call records, the stack budget and
the registers stay channel messages (bus CH), exactly as in `wasmBaseM2Air`.  Nothing crosses a
segment except the public values.

## The boundary (public values)

| field | where |
|---|---|
| `pc, t, S, sb, cid` (STATE), `halted` (out only) | `SEGB` sends the first STATE message `[pc_in, t_in+1, S_in, 0, sb_in, cid_in]` and receives the last one |
| the gas segment `(S_seg, segb)` (spec `g = segb − R·(S − S_seg)`) | channel space 7 (the *gas register*): `SEGB` produces it at `t_in`; every HOST row consumes it and produces `(S + fee, g_after)` (`HostG`); `SEGB` consumes the final one |
| `ctxDigest`: SHA-384 of the sorted list of every live non-memory channel message | `CUTI` (produces the messages at `tp = t_in` from the hashed rows), `CUTO` (consumes the live messages, hashes them) |
| `memRoot`: SHA-384 Merkle root over the 1 KiB memory blocks, depth `D` (public) | `MEMB` (one row per 128 bytes of a touched block: produces the block's bytes at `t_in`, consumes them at the end, hashes both), `MPATH` (one row per touched block and level: the old and the new Merkle path, a root chain from `memRoot_in` to `memRoot_out`) |

Hashing is SHA-384 (FIPS 180-4 §6.5) through the native SHA-512 compression chip (`native/sha384-air4`,
interface bus 103: per compression 16 messages `[cid, m, limbs(w_2m), limbs(w_2m+1)]` over the 32
words `h_in ‖ block ‖ h_out`, limbs `[0,21) [21,42) [42,64)`).

## Activation ids are relabelled to depths at every cut

`cid` (the CALL row's time) is an AIR artefact, not spec state.  `CUTO` relabels it: the call
records (space 4) are consumed in increasing `cid` order and get depths `1, 2, …` (`dep`); the
entry frame keeps `0`.  `CIDMAP` (bus 14) is the lookup `cid ↦ depth` they offer (`SEGB` offers
`0 ↦ 0`).  Locals of activation `cid` (space `16 + cid`) are hashed in space `16 + depth`, a
record's caller field likewise, and the final STATE's `cid` is published as a depth.  The next
segment produces them with `cid = depth`; every later CALL gets `cid = ts > t_in ≥ depth`, so ids
stay unique.  So the boundary is a function of the spec state (plus `t`).

**Dead locals.**  A returned activation's locals stay in the channel.  `RET` sends a tombstone
`[cid]` (bus 12); `DROP` turns it into a lookup (bus 13) and consumes locals of tombstoned
activations only.  A live activation's locals can only be kept by `CUTO` (it needs `CIDMAP` of a
live record), a dead one's only dropped, so the hashed list is exactly the live frames' locals.

## Canonical encoding of `ctxDigest`

Each kept message is the 7 fields `space, slot, tag, v0, v1, v2, v3` (relabelled), each `< 2^30`,
written as one 64-bit word `lo + 2^21·hi + 2^42·mark` (`lo < 2^16`, `hi < 2^14`; `mark = 1` on the
first word of a real message) plus a zero word: 8 words per message, 2 messages per SHA-512 block,
the last block completed by one all-zero filler message, then the SHA-384 padding block (length
`1024·#blocks` bits).  The list is strictly increasing in `(space, slot)`, so it is canonical.
`CUTO` range-checks every half and the order; `CUTI` needs no check (its digest is the previous
segment's, so its rows are that preimage unless SHA-384 collides).
-/
namespace WasmBase
namespace Chips
namespace Seg
open Expr

/-! ## Buses, public values, constants -/

/-- The SHA-512 compression chip's interface bus (`native/sha384-air4`, `BUS_IF`). -/
def busIf : Nat := 103
def busTomb : Nat := 12
def busDLook : Nat := 13
def busCidm : Nat := 14
def busLeaf : Nat := 15
def busRch : Nat := 16
/-- Channel space of the gas register `[7, 0, S_seg, segb limbs…]`. -/
def spaceGas : Nat := 7

/-- Public values.  Indices 0–10 keep `Boundary`'s meaning where a kept table reads them: REG-C's
`cPubR`/`cPubRTrap` read `nres` (2), `R` (4–7, all 0 here) and `status` (8 = `halted_out`). -/
def pubPcIn : Nat := 11
def pubTIn : Nat := 12
def pubSIn : Nat := 13
def pubSbIn : Nat := 14
def pubCidIn : Nat := 15
def pubSsegIn : Nat := 16
def pubGbIn : Nat := 17
def pubPcOut : Nat := 21
def pubTOut : Nat := 22
def pubSOut : Nat := 23
def pubSbOut : Nat := 24
def pubCidOut : Nat := 25
def pubSsegOut : Nat := 26
def pubGbOut : Nat := 27
def pubCtxIn : Nat := 31
def pubCtxOut : Nat := 49
def pubMemIn : Nat := 67
def pubMemOut : Nat := 85
def pubDepth : Nat := 103
def pubNblk : Nat := 104
def numPub : Nat := 105

/-- The chip's limbs of a 64-bit word. -/
def wl (x : Nat) : List Nat := [x % 2 ^ 21, x / 2 ^ 21 % 2 ^ 21, x / 2 ^ 42]

/-- SHA-384 initial hash value (FIPS 180-4 §5.3.4). -/
def IV384 : List Nat :=
  [0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
   0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

def ivLimbs : List Nat := IV384.flatMap wl

theorem ivLimbs_len : ivLimbs.length = 24 := by decide

/-- A word as its three limb expressions. -/
abbrev W3 := List Expr

def constW (x : Nat) : W3 := (wl x).map Expr.c
def zeroW : W3 := [0, 0, 0]

/-- The 16 interface receives of one compression over the 32 words `h_in ‖ block ‖ h_out`. -/
def comp (cid : Expr) (ws : List W3) (cnt : Expr) : List Inter :=
  (List.range 16).map fun m =>
    ⟨busIf, false, cnt, [cid, Expr.c m] ++ ws.getD (2 * m) zeroW ++ ws.getD (2 * m + 1) zeroW⟩

/-- Column index by name. -/
def ix (cs : List String) (n : String) : Nat := cs.idxOf n

def names (p : String) (n : Nat) : List String := (List.range n).map fun i => s!"{p}{i}"

/-- 8 words (24 limb columns) starting at the column named `p0`. -/
def wordsAt (col : String → Expr) (p : String) (n : Nat) : List W3 :=
  (List.range n).map fun i => [col s!"{p}{3 * i}", col s!"{p}{3 * i + 1}", col s!"{p}{3 * i + 2}"]

def sumE (l : List Expr) : Expr := l.foldl (· + ·) 0

/-! ## SEGB: the boundary row (height 4, interactions on the first row) -/

namespace Segb
def cols : List String := ["cidf", "m0", "gtpf", "nbt"]
def c (n : String) : Expr := v (ix cols n)
def pubs (b n : Nat) : List Expr := (List.range n).map fun i => pv (b + i)
def inters : List Inter :=
  [stateOut (pv pubPcIn) (pv pubTIn + 1) (pv pubSIn) 0 (pv pubSbIn) (pv pubCidIn) .first,
   ⟨busState, false, .first, [pv pubPcOut, pv pubTOut + 1, pv pubSOut, pv Boundary.pubStatus, pv pubSbOut,
     c "cidf"]⟩,
   ⟨busCidm, false, .first, [c "cidf", pv pubCidOut]⟩,
   ⟨busCidm, true, c "m0", [0, 0]⟩,
   chSend (Expr.c spaceGas) 0 (pv pubSsegIn) (pubs pubGbIn 4) (pv pubTIn) .first,
   chRecv (Expr.c spaceGas) 0 (pv pubSsegOut) (pubs pubGbOut 4) (c "gtpf") .first,
   ⟨busRch, true, .first, [0] ++ pubs pubMemIn 18⟩,
   ⟨busRch, false, .first, [c "nbt"] ++ pubs pubMemOut 18⟩]
def table : Table := ⟨"SEGB", cols, [], inters⟩
end Segb

/-! ## RET with the tombstone -/

namespace RetT
open Ret
def inters : List Inter := Ret.inters ++ [⟨busTomb, true, tk, [v kCid]⟩]
def table : Table := ⟨"RET", Ret.cols, Ret.constraints, inters⟩
theorem inters_prefix : Ret.inters <+: inters := List.prefix_append _ _
end RetT

/-! ## The call-key bus (E2E M4c, LINK)

`busHKey` links every active `HOSTB` row and every active `REG-C` row to the HOST row of its call:
HOST *offers* its call key `[ts, hid]` with a witness multiplicity `nk` (zero on inactive rows),
`HOSTB` and `REG-C` *look it up* with their activity flag.  So a byte or register group cannot carry
a key that no active HOST row has (`HostBLinked.linked`, `RegCLinked`; `Main/SegKey.lean`).  The
honest `nk` is the number of active `HOSTB` and `REG-C` rows of the call. -/
def busHKey : Nat := 214

/-! ## HOST with the gas register (`HOST'` + 7 columns) and the call-key offer (`nk`) -/

namespace HostG
open Host
def gS : Nat := 95
def gb : Nat := 96     -- 96..99
def gtp : Nat := 100
def ghi : Nat := 101
/-- The call-key multiplicity (E2E M4c): how many `HOSTB`/`REG-C` rows look this call's key up. -/
def nk : Nat := 102
def cols : List String := HostR.cols ++ ["gS", "gb0", "gb1", "gb2", "gb3", "gtp", "ghi", "nk"]
/-- An inactive HOST row offers no key. -/
def cNk : Expr := (1 - v act) * v nk
/-- The call-key offer `[ts, hid]` with multiplicity `nk`. -/
def keyRecv : Inter := ⟨busHKey, false, v nk, [v cTs, v hid]⟩
def constraints : List Expr := HostR.constraints ++ [cNk]
def inters : List Inter :=
  HostR.inters ++
  [chRecv (Expr.c spaceGas) 0 (v gS) (limbsOf gb) (v gtp) (v act)] ++
  timeChk (v cTs) (v gtp) (v ghi) (v act) ++
  [chSend (Expr.c spaceGas) 0 (v cS + v cFee) (limbsOf ga) (v cTs) (v act)] ++
  [keyRecv]
def table : Table := ⟨"HOST", cols, constraints, inters⟩
theorem cols_len : cols.length = 103 := by decide
theorem gS_name : cols[gS]? = some "gS" := by decide
theorem gtp_name : cols[gtp]? = some "gtp" := by decide
theorem nk_name : cols[nk]? = some "nk" := by decide
theorem inters_prefix : HostR.inters <+: inters := by
  simp only [inters, List.append_assoc]; exact List.prefix_append _ _
theorem constraints_prefix : HostR.constraints <+: constraints := List.prefix_append _ _
end HostG

/-! ## HOSTB and REG-C with the call-key lookup (E2E M4c, LINK) -/

namespace HostBK
/-- An active `HOSTB` row looks its call key up. -/
def keySend : Inter := ⟨busHKey, true, v HostB.act, [v HostB.ts, v HostB.hid]⟩
def inters : List Inter := HostB.inters ++ [keySend]
def table : Table := ⟨"HOSTB", HostB.cols, HostB.constraints, inters⟩
theorem inters_prefix : HostB.inters <+: inters := List.prefix_append _ _
end HostBK

namespace RegCK
/-- An active `REG-C` row looks its call key up. -/
def keySend : Inter := ⟨busHKey, true, v Reg.act, [v Reg.ts, v Reg.hid]⟩
def inters : List Inter := RegC.inters ++ [keySend]
def table : Table := ⟨"REG", RegC.cols, RegC.constraints, inters⟩
theorem inters_prefix : RegC.inters <+: inters := List.prefix_append _ _
end RegCK

/-! ## DROP: tombstones and dead-local drops -/

namespace Drop
def cols : List String := ["act", "isT", "c", "m", "slot", "tag", "x0", "x1", "x2", "x3", "tp"]
def c (n : String) : Expr := v (ix cols n)
def constraints : List Expr :=
  [bool (c "act"), bool (c "isT"), (1 - c "act") * c "isT", (1 - c "isT") * c "m", (1 - c "act") * c "m"]
def inters : List Inter :=
  [⟨busTomb, false, c "act" * c "isT", [c "c"]⟩,
   ⟨busDLook, true, c "m", [c "c"]⟩,
   chRecv (16 + c "c") (c "slot") (c "tag") [c "x0", c "x1", c "x2", c "x3"] (c "tp") (c "act" * (1 - c "isT")),
   ⟨busDLook, false, c "act" * (1 - c "isT"), [c "c"]⟩]
def table : Table := ⟨"DROP", cols, constraints, inters⟩
end Drop

/-! ## CUTI / CUTO: the small-state stream -/

namespace Cut
/-- The stream columns shared by `CUTI` and `CUTO`. -/
def streamCols : List String :=
  ["act", "j", "kD", "kP", "kX"] ++ names "lo" 7 ++ names "hi" 7 ++ ["gi", "gl", "gh", "cid"] ++ names "h" 24

section
variable (cs : List String)
def c (n : String) : Expr := v (ix cs n)
def n (s : String) : Expr := nv (ix cs s)
/-- Field `k` of the message (relabelled for `CUTO`): `lo_k + 2^16·hi_k`. -/
def F (k : Nat) : Expr := c cs s!"lo{k}" + 65536 * c cs s!"hi{k}"
def Fn (k : Nat) : Expr := n cs s!"lo{k}" + 65536 * n cs s!"hi{k}"

/-- The row's 8 block words (one message, or the padding block's halves on a `kP` row).  The
message limbs are gated by `act` (not `kD`), so a data row without a message (the odd stream's
filler, `kD = 1`, `act = 0`) hashes the all-zero message (M4b fix: `cuto_filler_counterexample`). -/
def rowWords : List W3 :=
  let act := c cs "act"; let kP := c cs "kP"; let j := c cs "j"
  ((List.range 7).map fun k =>
    [act * c cs s!"lo{k}", act * c cs s!"hi{k}",
     if k = 0 then c cs "act" + kP * (1 - j) * Expr.c (2 ^ 21) else 0]) ++
  [[kP * j * 1024 * c cs "gl", kP * j * c cs "gh", 0]]

/-- Interface receives: 4 chaining-value pairs (`h_in` on `j = 0`, `h_out` on `j = 1`) and 4 block pairs. -/
def ifInters : List Inter :=
  let j := c cs "j"; let cnt := c cs "kD" + c cs "kP"
  let hw := wordsAt (c cs) "h" 8
  let bw := rowWords cs
  ((List.range 4).map fun i =>
    ⟨busIf, false, cnt, [c cs "cid", Expr.c i + 12 * j] ++ hw.getD (2 * i) zeroW ++ hw.getD (2 * i + 1) zeroW⟩) ++
  ((List.range 4).map fun i =>
    ⟨busIf, false, cnt, [c cs "cid", Expr.c (4 + i) + 4 * j] ++ bw.getD (2 * i) zeroW ++ bw.getD (2 * i + 1) zeroW⟩)

/-- Row kinds (data groups, one padding group, dead rows), the group counter, the chaining value. -/
def streamConstraints (digestBase : Nat) : List Expr :=
  let act := c cs "act"; let j := c cs "j"; let kD := c cs "kD"; let kP := c cs "kP"; let kX := c cs "kX"
  [bool act, bool j, bool kD, bool kP, bool kX, kD + kP + kX - 1, (1 - kD) * act,
   .first * j, .first * kX,
   .trans * (1 - kX) * (1 - j) * (n cs "j" - 1),
   .trans * (1 - kX) * (1 - j) * (n cs "kD" - kD),
   .trans * (1 - kX) * (1 - j) * (n cs "kP" - kP),
   .trans * j * kD * n cs "kX",
   .trans * j * kP * (1 - n cs "kX"),
   .trans * kX * (1 - n cs "kX"),
   .trans * j * (1 - n cs "kX") * n cs "j",
   .last * kD, .last * (1 - kX) * (1 - j),
   kD * (1 - act) * (1 - j),
   .trans * kD * (1 - act) * (1 - n cs "kP"),
   .first * c cs "gi",
   .trans * (1 - n cs "kX") * (n cs "gi" - c cs "gi" - j),
   kP * j * (c cs "gi" - c cs "gl" - 2048 * c cs "gh"),
   .trans * (1 - kX) * (1 - j) * (n cs "cid" - c cs "cid")] ++
  ((List.range 24).map fun i => .first * (c cs s!"h{i}" - Expr.c (ivLimbs.getD i 0))) ++
  ((List.range 24).map fun i => .trans * j * (1 - n cs "kX") * (n cs s!"h{i}" - c cs s!"h{i}")) ++
  ((List.range 18).map fun i => kP * j * (c cs s!"h{i}" - pv (digestBase + i)))

def padR16 : List Inter :=
  [r16 (32 * c cs "gl") (c cs "kP" * c cs "j"), r16 (c cs "gh") (c cs "kP" * c cs "j"),
   -- `gl` itself: `r16 (32·gl)` alone admits gl ≈ P/32 (`gl_padding_counterexample`, R16Audit)
   r16 (c cs "gl") (c cs "kP" * c cs "j")]
end

namespace In
def cols : List String := streamCols
def c (s : String) : Expr := Cut.c cols s
def table : Table :=
  ⟨"CUTI", cols, streamConstraints cols pubCtxIn,
   [chSend (F cols 0) (F cols 1) (F cols 2) [F cols 3, F cols 4, F cols 5, F cols 6] (pv pubTIn) (c "act")] ++
   ifInters cols ++ padR16 cols⟩
end In

namespace Out
def cols : List String := streamCols ++
  ["space", "slot", "x2", "tp", "k0", "k2", "k4", "k5", "k6", "kL", "clo", "chi", "dep", "mm", "same",
   "dlo", "dhi", "rlo", "rhi"]
def c (s : String) : Expr := Cut.c cols s
def n (s : String) : Expr := Cut.n cols s
def F (k : Nat) : Expr := Cut.F cols k
def Fn (k : Nat) : Expr := Cut.Fn cols k
def constraints : List Expr :=
  let act := c "act"; let kL := c "kL"; let k4 := c "k4"
  streamConstraints cols pubCtxOut ++
  (["k0", "k2", "k4", "k5", "k6", "kL", "same"].map fun s => bool (c s)) ++
  [c "k0" + c "k2" + k4 + c "k5" + c "k6" + kL - act,
   (1 - kL) * (c "space" - 2 * c "k2" - 4 * k4 - 5 * c "k5" - 6 * c "k6"),
   kL * (c "space" - 16 - c "clo" - 65536 * c "chi"),
   (1 - kL) * (F 0 - c "space"),
   (1 - k4) * (F 1 - c "slot"),
   k4 * (F 1 - c "dep"),
   (1 - k4) * (F 5 - c "x2"),
   .first * (c "dep" - k4),
   .trans * (n "dep" - c "dep" - n "k4"),
   (1 - k4) * c "mm",
   act * n "act" * c "same" * (Fn 0 - F 0),
   act * n "act" * (c "same" * (Fn 1 - F 1 - 1) + (1 - c "same") * (Fn 0 - F 0 - 1) - c "dlo" - 65536 * c "dhi"),
   k4 * n "k4" * (n "slot" - c "slot" - 1 - c "rlo" - 65536 * c "rhi")]
def inters : List Inter :=
  let act := c "act"; let kL := c "kL"; let k4 := c "k4"
  [chRecv (c "space") (c "slot") (F 2) [F 3, F 4, c "x2", F 6] (c "tp") act,
   ⟨busCidm, false, kL, [c "space" - 16, F 0 - 16]⟩,
   ⟨busCidm, false, k4, [c "x2", F 5]⟩,
   ⟨busCidm, true, c "mm", [c "slot", F 1]⟩,
   r16 (c "clo") kL, r16 (8 * c "chi") kL,
   r16 (c "dlo") (act * n "act"), r16 (8 * c "dhi") (act * n "act"),
   r16 (c "rlo") (k4 * n "k4"), r16 (16 * c "rhi") (k4 * n "k4")] ++
  ((List.range 7).flatMap fun k => [r16 (c s!"lo{k}") act, r16 (4 * c s!"hi{k}") act]) ++
  ifInters cols ++ padR16 cols
def table : Table := ⟨"CUTO", cols, constraints, inters⟩
end Out
end Cut

/-! ## MEMB: touched memory blocks (one row per 128 bytes; the 9th row of a block is SHA padding) -/

namespace Memb
def cols : List String :=
  ["act"] ++ names "p" 9 ++ ["blk", "ro", "cidI", "cidO"] ++ names "bi" 128 ++ names "bo" 128 ++
  names "tq" 128 ++ names "si5_" 16 ++ names "si2_" 16 ++ names "so5_" 16 ++ names "so2_" 16 ++
  names "hiI" 24 ++ names "hoI" 24 ++ names "hiO" 24 ++ names "hoO" 24
def c (s : String) : Expr := v (ix cols s)
def n (s : String) : Expr := nv (ix cols s)
def p (i : Nat) : Expr := c s!"p{i}"
def kD : Expr := sumE ((List.range 8).map p)
def kP : Expr := p 8
def kk : Expr := sumE ((List.range 9).map fun i => Expr.c i * p i)
def addr (i : Nat) : Expr := 1024 * c "blk" + 128 * kk + Expr.c i

/-- The data limbs of word `w` (bytes `b(8w) … b(8w+7)`, big-endian) with split columns
`s5 = b(8w+5) >> 5`, `s2 = b(8w+2) >> 2`. -/
def dataW (b : Nat → Expr) (s5 s2 : Expr) (w : Nat) : W3 :=
  let B := fun i => b (8 * w + i)
  [B 7 + 256 * B 6 + 65536 * (B 5 - 32 * s5),
   s5 + 8 * B 4 + 2048 * B 3 + 524288 * (B 2 - 4 * s2),
   s2 + 64 * B 1 + 16384 * B 0]

/-- SHA-384 padding block of a 1024-byte message: word 0 = `0x80…`, word 15 = 8192 (bits). -/
def padW (w : Nat) : List Nat := if w = 0 then [0, 0, 2 ^ 21] else if w = 15 then [8192, 0, 0] else [0, 0, 0]

def blockW (pre : String) (s5 s2 : String) : List W3 :=
  (List.range 16).map fun w =>
    let d := dataW (fun i => c s!"{pre}{i}") (c s!"{s5}{w}") (c s!"{s2}{w}") w
    (List.range 3).map fun l => kD * d.getD l 0 + kP * Expr.c ((padW w).getD l 0)

def splitR16 (pre s5 s2 : String) (cnt : Expr) : List Inter :=
  (List.range 16).flatMap fun w =>
    [r16 (8192 * c s!"{s5}{w}") cnt, r16 (2048 * (c s!"{pre}{8 * w + 5}" - 32 * c s!"{s5}{w}")) cnt,
     r16 (1024 * c s!"{s2}{w}") cnt, r16 (16384 * (c s!"{pre}{8 * w + 2}" - 4 * c s!"{s2}{w}")) cnt,
     -- the split values themselves are bytes: without this a field element with 8192·s5 < 2^16
     -- mod P (P ≡ 1 mod 2^13) passes, and the limbs no longer encode the bytes
     byteQ 0 (c s!"{s5}{w}") (c s!"{s2}{w}") 0 cnt]

def constraints : List Expr :=
  let act := c "act"; let ro := c "ro"
  [bool act, bool ro, (1 - act) * ro] ++ ((List.range 9).map fun i => bool (p i)) ++
  [sumE ((List.range 9).map p) - act,
   .first * act * (1 - p 0),
   .trans * p 8 * n "act" * (1 - n "p0"),
   .trans * (1 - act) * n "act",
   .last * act * (1 - p 8),
   .trans * n "act" * (1 - n "p0") * (n "blk" - c "blk"),
   .trans * n "act" * (1 - n "p0") * (n "ro" - ro)] ++
  ((List.range 8).map fun i => .trans * p i * (1 - nv (ix cols s!"p{i + 1}"))) ++
  ((List.range 128).map fun i => ro * (c s!"bo{i}" - c s!"bi{i}")) ++
  ((List.range 24).map fun l => .trans * (1 - p 8) * act * (n s!"hiI{l}" - c s!"hoI{l}")) ++
  ((List.range 24).map fun l => p 0 * (c s!"hiI{l}" - Expr.c (ivLimbs.getD l 0))) ++
  ((List.range 24).map fun l => .trans * (1 - p 8) * act * (1 - ro) * (n s!"hiO{l}" - c s!"hoO{l}")) ++
  ((List.range 24).map fun l => p 0 * (1 - ro) * (c s!"hiO{l}" - Expr.c (ivLimbs.getD l 0))) ++
  ((List.range 18).map fun l => p 8 * ro * (c s!"hoO{l}" - c s!"hoI{l}"))

def inters : List Inter :=
  let act := c "act"; let ro := c "ro"
  ((List.range 128).flatMap fun i =>
    [chSend 3 (addr i) 0 [c s!"bi{i}", 0, 0, 0] (pv pubTIn) kD,
     chRecv 3 (addr i) 0 [c s!"bo{i}", 0, 0, 0] (c s!"tq{i}") kD]) ++
  ((List.range 64).map fun t => byteQ 0 (c s!"bi{2 * t}") (c s!"bi{2 * t + 1}") 0 kD) ++
  splitR16 "bi" "si5_" "si2_" kD ++ splitR16 "bo" "so5_" "so2_" (kD * (1 - ro)) ++
  comp (c "cidI") (wordsAt c "hiI" 8 ++ blockW "bi" "si5_" "si2_" ++ wordsAt c "hoI" 8) act ++
  comp (c "cidO") (wordsAt c "hiO" 8 ++ blockW "bo" "so5_" "so2_" ++ wordsAt c "hoO" 8) (act * (1 - ro)) ++
  [⟨busLeaf, true, p 8, [c "blk", ro] ++ (names "hoI" 18).map c ++ (names "hoO" 18).map c⟩,
   r16 (n "blk" - c "blk" - 1) (.trans * p 8 * n "p0"),
   r16 (c "blk") (p 8),
   r16 (pv pubNblk - 1 - c "blk") (p 8)]
def table : Table := ⟨"MEMB", cols, constraints, inters⟩
end Memb

/-! ## MPATH: one row per touched block and tree level (old and new path) -/

namespace Mpath
def cols : List String :=
  ["act", "bot", "top", "bit", "ro", "blk", "lvl", "acc", "pw", "kb", "cidO", "cidN"] ++
  names "co" 18 ++ names "cn" 18 ++ names "sb" 18 ++ names "po" 18 ++ names "pn" 18 ++
  names "xo" 6 ++ names "xn" 6 ++ names "ri" 18 ++ names "rt" 18
def c (s : String) : Expr := v (ix cols s)
def n (s : String) : Expr := nv (ix cols s)
def dig (pre : String) : List Expr := (names pre 18).map c
/-- The inner-node block `left48 ‖ right48` with its SHA-384 padding (96 bytes = 768 bits). -/
def nodeBlock (cur : String) : List W3 :=
  let b := c "bit"
  let side := fun (x y : String) => (List.range 6).map fun w =>
    (List.range 3).map fun l => b * c s!"{x}{3 * w + l}" + (1 - b) * c s!"{y}{3 * w + l}"
  side "sb" cur ++ side cur "sb" ++ [constW (2 ^ 63), zeroW, zeroW, constW 768]
def ivW : List W3 := IV384.map constW
def constraints : List Expr :=
  let act := c "act"; let top := c "top"; let bot := c "bot"
  let notTop : Expr := Expr.trans * act * (1 - top)
  [bool act, bool bot, bool top, bool (c "bit"), bool (c "ro"), (1 - act) * bot, (1 - act) * top,
   .first * act * (1 - bot), .first * act * c "kb",
   notTop * (n "lvl" - c "lvl" - 1), notTop * n "bot", notTop * (1 - n "act"),
   notTop * (n "blk" - c "blk"), notTop * (n "ro" - c "ro"), notTop * (n "kb" - c "kb"),
   notTop * (n "pw" - 2 * c "pw"), notTop * (n "acc" - c "acc" - 2 * c "pw" * n "bit"),
   .trans * top * n "act" * (1 - n "bot"), .trans * top * n "act" * (n "kb" - c "kb" - 1),
   .trans * (1 - act) * n "act", .last * act * (1 - top),
   bot * c "lvl", bot * (c "pw" - 1), bot * (c "acc" - c "bit"),
   top * (c "lvl" - pv pubDepth + 1), top * (c "acc" - c "blk")] ++
  ((List.range 18).flatMap fun l =>
    [notTop * (n s!"co{l}" - c s!"po{l}"), notTop * (n s!"cn{l}" - c s!"pn{l}"),
     notTop * (n s!"ri{l}" - c s!"ri{l}"), notTop * (n s!"rt{l}" - c s!"rt{l}"),
     top * (c s!"po{l}" - c s!"ri{l}"), top * (c s!"pn{l}" - c s!"rt{l}"),
     c "ro" * (c s!"pn{l}" - c s!"po{l}")])
def inters : List Inter :=
  let act := c "act"; let top := c "top"
  [⟨busLeaf, false, c "bot", [c "blk", c "ro"] ++ dig "co" ++ dig "cn"⟩,
   ⟨busRch, false, top, [c "kb"] ++ dig "ri"⟩,
   ⟨busRch, true, top, [c "kb" + 1] ++ dig "rt"⟩] ++
  comp (c "cidO") (ivW ++ nodeBlock "co" ++ wordsAt c "po" 6 ++ wordsAt c "xo" 2) act ++
  comp (c "cidN") (ivW ++ nodeBlock "cn" ++ wordsAt c "pn" 6 ++ wordsAt c "xn" 2) (act * (1 - c "ro"))
def table : Table := ⟨"MPATH", cols, constraints, inters⟩
end Mpath

end Seg
end Chips

open Chips in
/-- **The E2E M4 segment AIR.**  `wasmBaseM2Air`'s table list with BOUNDARY (0) → `SEGB`, RET (14)
→ `RET` + tombstone, DRAIN (18) → `DROP`, MEMINIT (19) → `MEMB`, DATA (20) → `MPATH`, HOST' (22)
→ `HOST` + gas register + call-key offer, HOSTB (25) / REG-C (27) → + call-key lookup (`busHKey`,
E2E M4c), and `CUTI` (30), `CUTO` (31) appended.  Every other table keeps its index
and definition. -/
def wasmBaseSegAir (_nloc _ngl : Nat) : Air where
  tables := [Seg.Segb.table, Add.table, Bit.table, Mul.table, Shift.table, Cmp.table,
    Const.table, Stack.table, Ctrl.table, Local.table, Div.table, Load.table, Store.table, Call.table,
    Seg.RetT.table, Range16.table, Byte.table, Code.table, Seg.Drop.table, Seg.Memb.table,
    Seg.Mpath.table, Func.table, Seg.HostG.table, HostO.table, HostTab.table, Seg.HostBK.table, IfC.table,
    Seg.RegCK.table, Conv.table, Unreach.table, Seg.Cut.In.table, Seg.Cut.Out.table]
  numPub := Seg.numPub

theorem seg_air_len (nloc ngl : Nat) : (wasmBaseSegAir nloc ngl).tables.length = 32 := by
  simp [wasmBaseSegAir]

/-- The instruction chips other than RET/HOST are `wasmBaseM2Air`'s, at the same indices. -/
theorem seg_air_same (nloc ngl t : Nat)
    (ht : t ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 21, 23, 24, 26, 28, 29]) :
    (wasmBaseSegAir nloc ngl).tables[t]? = (wasmBaseM2Air nloc ngl).tables[t]? := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wasmBaseSegAir, wasmBaseM2Air, wasmBaseAir]

end WasmBase
