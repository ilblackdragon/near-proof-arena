import WasmBase.Air
/-!
# WasmBase.Chips — the AIR set `wasm-base-v3` (families F1, linear memory)

Nineteen AIRs (≤ 32), max degree 8; CODE and DATA are cached traces.  Buses:

| bus | name | message | role |
|---|---|---|---|
| 0 | STATE | `[pc, ts, S, halted, sb, cid]` | execution-state chain: each instruction row receives once, sends once |
| 1 | FETCH | `[pc, op, h, fee, x0, x1, x2, x3]` | code records; queried by instruction rows, answered by the cached CODE table |
| 2 | CH | `[space, slot, tag, v0, v1, v2, v3, tp]` | value channel: operand stack (space 0, absolute slot `sb + h − k`) and the locals of activation `cid` (space `16 + cid`); producer → consumer (P-PERF-5) |
| 3 | R16 | `[v]` | 16-bit range lookups into RANGE16 |
| 4 | BYTE | `[kind, x, y, z]` | byte-pair range (kind 0) / and (1) / or (2) / xor (3) into BYTE |
| 5 | DATA | `[addr, byte]` | initial-memory bytes of the data image; queried by MEMINIT, answered by the cached DATA table |

Linear memory is channel space 3: one message `[3, addr, 0, byte, 0, 0, 0, tp]` per touched byte,
produced initially by a MEMINIT row (time 0) and consumed / re-produced by every LOAD / STORE that
touches it (offline memory checking through the channel); leftover messages are drained at the end.

Values are 4 limbs of 16 bits (i32: limbs 2, 3 are 0); `tag` = 1 for i64.  `S` is the number of
gas units (`regular_op_cost`) charged so far; `h` is the static operand-stack height at `pc` (from
the code record); `sb` is the current frame's stack base and `cid` its activation id (0 = entry
frame; every chip appends the two columns `sb, cid` and passes them through unchanged); `ts` is the
row clock.  A consumer of a stack value receives `(slot, tag, v, tp)`
and range-checks `ts - tp - 1 = lo + 2^16 hi` with `lo, 4·hi < 2^16`.
-/
namespace WasmBase
namespace Chips
open Expr

def v (i : Nat) : Expr := .col i
def nv (i : Nat) : Expr := .nxt i
def pv (i : Nat) : Expr := .pub i

def busState : Nat := 0
def busFetch : Nat := 1
def busStk : Nat := 2
def busR16 : Nat := 3
def busByte : Nat := 4
def busData : Nat := 5
def busFunc : Nat := 6

def B16 : Expr := 65536
def bool (x : Expr) : Expr := x * (x - 1)

def stateIn (pc ts s sb cid : Expr) (cnt : Expr) : Inter := ⟨busState, false, cnt, [pc, ts, s, 0, sb, cid]⟩
def stateOut (pc ts s halted sb cid : Expr) (cnt : Expr) : Inter :=
  ⟨busState, true, cnt, [pc, ts, s, halted, sb, cid]⟩
def fetch (pc op h fee : Expr) (xs : List Expr) (cnt : Expr) : Inter :=
  ⟨busFetch, true, cnt, [pc, op, h, fee] ++ xs⟩
/-- Space 0 = operand stack, space `16 + cid` = locals of activation `cid`. -/
def chRecv (space slot tag : Expr) (val : List Expr) (tp cnt : Expr) : Inter :=
  ⟨busStk, false, cnt, [space, slot, tag] ++ val ++ [tp]⟩
def chSend (space slot tag : Expr) (val : List Expr) (ts cnt : Expr) : Inter :=
  ⟨busStk, true, cnt, [space, slot, tag] ++ val ++ [ts]⟩
def stkRecv (slot tag : Expr) (val : List Expr) (tp cnt : Expr) : Inter := chRecv 0 slot tag val tp cnt
def stkSend (slot tag : Expr) (val : List Expr) (ts cnt : Expr) : Inter := chSend 0 slot tag val ts cnt
def r16 (e cnt : Expr) : Inter := ⟨busR16, true, cnt, [e]⟩
def byteQ (kind x y z cnt : Expr) : Inter := ⟨busByte, true, cnt, [kind, x, y, z]⟩
/-- `tp < ts`: `ts - tp - 1 = lo + 2^16·hi`, `lo < 2^16`, `4·hi < 2^16`. -/
def timeChk (ts tp hi cnt : Expr) : List Inter :=
  [r16 (ts - tp - 1 - B16 * hi) cnt, r16 (4 * hi) cnt]

/-- Header columns shared by every instruction chip. -/
def cPc : Nat := 0
def cTs : Nat := 1
def cS : Nat := 2
def cH : Nat := 3
def cFee : Nat := 4
def headerCols : List String := ["pc", "ts", "S", "h", "fee"]
/-- Frame columns `sb, cid`, appended last by every instruction chip (indices `kSb`, `kCid`). -/
def frameCols : List String := ["fr_sb", "fr_cid"]

/-- Standard state transition `pc → pc+1` plus fetch; the frame columns pass through. -/
def stdState (sb cid : Nat) (op : Expr) (xs : List Expr) (act : Expr) : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v sb) (v cid) act,
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) 0 (v sb) (v cid) act,
   fetch (v cPc) op (v cH) (v cFee) xs act]

def zeros4 : List Expr := [0, 0, 0, 0]
def limbsOf (base : Nat) : List Expr := (List.range 4).map fun i => v (base + i)
/-- 16-bit limb `i` from byte columns `base..base+7`. -/
def limbB (base i : Nat) : Expr := v (base + 2 * i) + 256 * v (base + 2 * i + 1)
def limbsB (base : Nat) : List Expr := (List.range 4).map (limbB base)

/-! ## ADD: i32/i64 add, sub -/
namespace Add
def kSb : Nat := 28
def kCid : Nat := 29
def fAdd : Nat := 5
def fSub : Nat := 6
def is64 : Nat := 7
def a : Nat := 8     -- a[4] 8..11
def ta : Nat := 12
def ha : Nat := 13
def b : Nat := 14    -- b[4] 14..17
def tb : Nat := 18
def hb : Nat := 19
def r : Nat := 20    -- r[4] 20..23
def cy : Nat := 24   -- carries 24..27
def cols : List String := headerCols ++ ["f_add", "f_sub", "is64", "a0", "a1", "a2", "a3", "ta", "ha",
  "b0", "b1", "b2", "b3", "tb", "hb", "r0", "r1", "r2", "r3", "c0", "c1", "c2", "c3"] ++ frameCols
def act : Expr := v fAdd + v fSub
def op : Expr := 0x6A + 18 * v is64 + v fSub
/-- add: `a + b = r (+ carry)`, sub: `r + b = a (+ borrow)`; `X + b + c_in = Z + 2^16 c_out`. -/
def X (i : Nat) : Expr := v fAdd * v (a + i) + v fSub * v (r + i)
def Z (i : Nat) : Expr := v fAdd * v (r + i) + v fSub * v (a + i)
def constraints : List Expr :=
  [bool (v fAdd), bool (v fSub), bool (v is64), v fAdd * v fSub,
   (1 - v is64) * v (a + 2), (1 - v is64) * v (a + 3),
   (1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3),
   (1 - v is64) * v (r + 2), (1 - v is64) * v (r + 3),
   bool (v cy), bool (v (cy + 1)), bool (v (cy + 2)), bool (v (cy + 3)),
   (1 - v is64) * v (cy + 2), (1 - v is64) * v (cy + 3),
   X 0 + v (b + 0) - Z 0 - B16 * v cy,
   X 1 + v (b + 1) + v cy - Z 1 - B16 * v (cy + 1),
   v is64 * (X 2 + v (b + 2) + v (cy + 1) - Z 2 - B16 * v (cy + 2)),
   v is64 * (X 3 + v (b + 3) + v (cy + 2) - Z 3 - B16 * v (cy + 3))]
def inters : List Inter :=
  stdState kSb kCid op zeros4 act ++
  [stkRecv (v kSb + v cH - 2) (v is64) (limbsOf a) (v ta) act,
   stkRecv (v kSb + v cH - 1) (v is64) (limbsOf b) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v kSb + v cH - 2) (v is64) (limbsOf r) (v cTs) act] ++
  (List.range 4).map (fun i => r16 (v (r + i)) act)
def table : Table := ⟨"ADD", cols, constraints, inters⟩
end Add

/-! ## BIT: i32/i64 and, or, xor (byte lookups) -/
namespace Bit
def kSb : Nat := 37
def kCid : Nat := 38
def fAnd : Nat := 5
def fOr : Nat := 6
def fXor : Nat := 7
def is64 : Nat := 8
def ab : Nat := 9    -- 9..16
def ta : Nat := 17
def ha : Nat := 18
def bb : Nat := 19   -- 19..26
def tb : Nat := 27
def hb : Nat := 28
def rb : Nat := 29   -- 29..36
def byteNames (p : String) : List String := (List.range 8).map fun i => p ++ toString i
def cols : List String := headerCols ++ ["f_and", "f_or", "f_xor", "is64"] ++ byteNames "ab" ++
  ["ta", "ha"] ++ byteNames "bb" ++ ["tb", "hb"] ++ byteNames "rb" ++ frameCols
def act : Expr := v fAnd + v fOr + v fXor
def op : Expr := 0x71 + 18 * v is64 + v fOr + 2 * v fXor
def kind : Expr := v fAnd + 2 * v fOr + 3 * v fXor
def constraints : List Expr :=
  [bool (v fAnd), bool (v fOr), bool (v fXor), bool (v is64),
   v fAnd * v fOr, v fAnd * v fXor, v fOr * v fXor] ++
  ((List.range 4).flatMap fun k =>
    [(1 - v is64) * v (ab + 4 + k), (1 - v is64) * v (bb + 4 + k), (1 - v is64) * v (rb + 4 + k)])
def inters : List Inter :=
  stdState kSb kCid op zeros4 act ++
  [stkRecv (v kSb + v cH - 2) (v is64) (limbsB ab) (v ta) act,
   stkRecv (v kSb + v cH - 1) (v is64) (limbsB bb) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v kSb + v cH - 2) (v is64) (limbsB rb) (v cTs) act] ++
  (List.range 8).map (fun k => byteQ kind (v (ab + k)) (v (bb + k)) (v (rb + k)) act)
def table : Table := ⟨"BIT", cols, constraints, inters⟩
end Bit

/-! ## MUL: i32/i64 mul (byte limbs, carries range-checked) -/
namespace Mul
def kSb : Nat := 43
def kCid : Nat := 44
def act : Nat := 5
def is64 : Nat := 6
def ab : Nat := 7    -- 7..14
def ta : Nat := 15
def ha : Nat := 16
def bb : Nat := 17   -- 17..24
def tb : Nat := 25
def hb : Nat := 26
def rb : Nat := 27   -- 27..34
def cy : Nat := 35   -- 35..42
def cols : List String := headerCols ++ ["act", "is64"] ++ Bit.byteNames "ab" ++ ["ta", "ha"] ++
  Bit.byteNames "bb" ++ ["tb", "hb"] ++ Bit.byteNames "rb" ++ Bit.byteNames "cy" ++ frameCols
def op : Expr := 0x6C + 18 * v is64
/-- Column convolution `Σ_{i+j=k} a_i b_j`. -/
def conv (k : Nat) : Expr :=
  ((List.range (k + 1)).map fun i => v (ab + i) * v (bb + (k - i))).foldl (· + ·) 0
def carryIn (k : Nat) : Expr := if k = 0 then 0 else v (cy + k - 1)
def limbEq (k : Nat) : Expr := conv k + carryIn k - v (rb + k) - 256 * v (cy + k)
def constraints : List Expr :=
  [bool (v act), bool (v is64)] ++
  ((List.range 4).flatMap fun k =>
    [(1 - v is64) * v (ab + 4 + k), (1 - v is64) * v (bb + 4 + k), (1 - v is64) * v (rb + 4 + k),
     (1 - v is64) * v (cy + 4 + k)]) ++
  (List.range 4).map limbEq ++
  (List.range 4).map (fun k => v is64 * limbEq (k + 4))
def inters : List Inter :=
  stdState kSb kCid op zeros4 (v act) ++
  [stkRecv (v kSb + v cH - 2) (v is64) (limbsB ab) (v ta) (v act),
   stkRecv (v kSb + v cH - 1) (v is64) (limbsB bb) (v tb) (v act)] ++
  timeChk (v cTs) (v ta) (v ha) (v act) ++ timeChk (v cTs) (v tb) (v hb) (v act) ++
  [stkSend (v kSb + v cH - 2) (v is64) (limbsB rb) (v cTs) (v act)] ++
  (List.range 4).map (fun i => byteQ 0 (v (ab + 2 * i)) (v (ab + 2 * i + 1)) 0 (v act)) ++
  (List.range 4).map (fun i => byteQ 0 (v (bb + 2 * i)) (v (bb + 2 * i + 1)) 0 (v act)) ++
  (List.range 4).map (fun i => byteQ 0 (v (rb + 2 * i)) (v (rb + 2 * i + 1)) 0 (v act)) ++
  (List.range 8).map (fun k => r16 (v (cy + k)) (v act))
def table : Table := ⟨"MUL", cols, constraints, inters⟩
end Mul

/-! ## SHIFT: i32/i64 shl, shr_s, shr_u, rotl, rotr

`k = b mod w` (bits `kb`, `b0 = k + w·q`); `e = k` (shl, rotl) or `w - k` (shr, rotr), `e = 8·t + eb`
with `t` one-hot (`el`) and `pow = 2^eb`.  `A` = `a` extended to `2w` bits (sign-filled for shr_s),
`P = A·2^e mod 2^(2w)` byte by byte with carries; the result is the low half (shl), the high half
(shr_s, shr_u) or their sum (rotl, rotr). -/
namespace Shift
def kSb : Nat := 80
def kCid : Nat := 81
def fShl : Nat := 5
def fShrS : Nat := 6
def fShrU : Nat := 7
def fRotl : Nat := 8
def fRotr : Nat := 9
def is64 : Nat := 10
def ab : Nat := 11   -- 11..18
def ta : Nat := 19
def ha : Nat := 20
def b : Nat := 21    -- 21..24 (16-bit limbs of the count)
def tb : Nat := 25
def hb : Nat := 26
def kb : Nat := 27   -- 27..32
def q : Nat := 33
def eb : Nat := 34   -- 34..36
def el : Nat := 37   -- 37..45
def sgn : Nat := 46
def rest : Nat := 47
def P : Nat := 48    -- 48..63
def cy : Nat := 64   -- 64..79
def cols : List String := headerCols ++ ["f_shl", "f_shrs", "f_shru", "f_rotl", "f_rotr", "is64"] ++
  Bit.byteNames "ab" ++ ["ta", "ha", "b0", "b1", "b2", "b3", "tb", "hb"] ++
  ((List.range 6).map fun i => s!"kb{i}") ++ ["q"] ++ ((List.range 3).map fun i => s!"eb{i}") ++
  ((List.range 9).map fun i => s!"el{i}") ++ ["sgn", "rest"] ++
  ((List.range 16).map fun i => s!"P{i}") ++ ((List.range 16).map fun i => s!"cy{i}") ++ frameCols
def left : Expr := v fShl + v fRotl
def right : Expr := v fShrS + v fShrU + v fRotr
def act : Expr := left + right
def op : Expr := 0x74 + 18 * v is64 + v fShrS + 2 * v fShrU + 3 * v fRotl + 4 * v fRotr
def w : Expr := 32 + 32 * v is64
def kval : Expr := ((List.range 6).map fun j => Expr.c (2 ^ j) * v (kb + j)).foldl (· + ·) 0
def eval' : Expr := left * kval + right * (w - kval)
def tval : Expr := ((List.range 9).map fun t => Expr.c t * v (el + t)).foldl (· + ·) 0
def ebval : Expr := v eb + 2 * v (eb + 1) + 4 * v (eb + 2)
def pow : Expr := (1 + v eb) * (1 + 3 * v (eb + 1)) * (1 + 15 * v (eb + 2))
def topByte : Expr := v is64 * v (ab + 7) + (1 - v is64) * v (ab + 3)
def fill : Expr := 255 * v sgn * v fShrS
/-- byte `i` of the `2w`-bit extension of `a`. -/
def A (i : Nat) : Expr :=
  if i < 4 then v (ab + i)
  else if i < 8 then v is64 * v (ab + i) + (1 - v is64) * fill
  else if i < 16 then v is64 * fill
  else 0
/-- `A_{j - t}` selected by the one-hot `el`. -/
def M (j : Nat) : Expr :=
  ((List.range 9).filterMap fun t => if t ≤ j then some (v (el + t) * A (j - t)) else none).foldl (· + ·) 0
def carryIn (j : Nat) : Expr := if j = 0 then 0 else v (cy + j - 1)
def limbEq (j : Nat) : Expr := pow * M j + carryIn j - v (P + j) - 256 * v (cy + j)
def flo : Expr := v fShl + v fRotl + v fRotr
def fhi : Expr := v fShrS + v fShrU + v fRotl + v fRotr
/-- result byte `j` (0..7). -/
def rbyte (j : Nat) : Expr :=
  if j < 4 then flo * v (P + j) + fhi * (v is64 * v (P + j + 8) + (1 - v is64) * v (P + j + 4))
  else v is64 * (flo * v (P + j) + fhi * v (P + j + 8))
def rlimb (i : Nat) : Expr := rbyte (2 * i) + 256 * rbyte (2 * i + 1)
def constraints : List Expr :=
  [bool (v fShl), bool (v fShrS), bool (v fShrU), bool (v fRotl), bool (v fRotr), bool (v is64),
   bool act] ++
  ((List.range 6).map fun j => bool (v (kb + j))) ++
  [(1 - v is64) * v (kb + 5),
   v b - kval - w * v q] ++
  ((List.range 3).map fun j => bool (v (eb + j))) ++
  ((List.range 9).map fun t => bool (v (el + t))) ++
  [((List.range 9).map fun t => v (el + t)).foldl (· + ·) 0 - act,
   eval' - ebval - 8 * tval,
   bool (v sgn),
   topByte - 128 * v sgn - v rest] ++
  ((List.range 4).map fun k => (1 - v is64) * v (ab + 4 + k)) ++
  [(1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3)] ++
  ((List.range 8).flatMap fun k => [(1 - v is64) * v (P + 8 + k), (1 - v is64) * v (cy + 8 + k)]) ++
  (List.range 8).map limbEq ++
  (List.range 8).map (fun j => v is64 * limbEq (j + 8))
def inters : List Inter :=
  stdState kSb kCid op zeros4 act ++
  [stkRecv (v kSb + v cH - 2) (v is64) (limbsB ab) (v ta) act,
   stkRecv (v kSb + v cH - 1) (v is64) (limbsOf b) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v kSb + v cH - 2) (v is64) ((List.range 4).map rlimb) (v cTs) act,
   -- `q < 2^16` itself (v1 range-checked `w·q`, which is unsound: `q` is free, so `w·q` can be any
   -- small residue and the shift count `k` was unconstrained; found by the Lean proof)
   r16 (v q) act,
   byteQ 0 (2 * v rest) 0 0 act] ++
  (List.range 4).map (fun i => byteQ 0 (v (ab + 2 * i)) (v (ab + 2 * i + 1)) 0 act) ++
  (List.range 8).map (fun i => byteQ 0 (v (P + 2 * i)) (v (P + 2 * i + 1)) 0 act) ++
  (List.range 8).map (fun i => byteQ 0 (v (cy + 2 * i)) (v (cy + 2 * i + 1)) 0 act)
def table : Table := ⟨"SHIFT", cols, constraints, inters⟩
end Shift


/-! ## CMP: i32/i64 eqz, eq, ne, lt/gt/le/ge _s/_u -/
namespace Cmp
def kSb : Nat := 42
def kCid : Nat := 43
def fEqz : Nat := 5
def fEq : Nat := 6
def fNe : Nat := 7
def fLtS : Nat := 8
def fLtU : Nat := 9
def fGtS : Nat := 10
def fGtU : Nat := 11
def fLeS : Nat := 12
def fLeU : Nat := 13
def fGeS : Nat := 14
def fGeU : Nat := 15
def is64 : Nat := 16
def a : Nat := 17    -- 17..20
def ta : Nat := 21
def ha : Nat := 22
def b : Nat := 23    -- 23..26
def tb : Nat := 27
def hb : Nat := 28
def sa : Nat := 29
def ra : Nat := 30
def sb : Nat := 31
def rb : Nat := 32
def d : Nat := 33    -- 33..36
def br : Nat := 37   -- 37..40
def inv : Nat := 41
def cols : List String := headerCols ++ ["f_eqz", "f_eq", "f_ne", "f_lts", "f_ltu", "f_gts", "f_gtu",
  "f_les", "f_leu", "f_ges", "f_geu", "is64", "a0", "a1", "a2", "a3", "ta", "ha",
  "b0", "b1", "b2", "b3", "tb", "hb", "sa", "ra", "sb", "rb", "d0", "d1", "d2", "d3",
  "br0", "br1", "br2", "br3", "inv"] ++ frameCols
def flags : List Nat := [fEqz, fEq, fNe, fLtS, fLtU, fGtS, fGtU, fLeS, fLeU, fGeS, fGeU]
def act : Expr := (flags.map v).foldl (· + ·) 0
def op : Expr := 0x45 + 11 * v is64 +
  ((flags.zipIdx).map fun (f, i) => Expr.c i * v f).foldl (· + ·) 0
def swap : Expr := v fGtS + v fGtU + v fLeS + v fLeU
def signed : Expr := v fLtS + v fGtS + v fLeS + v fGeS
def X (i : Nat) : Expr := v (a + i) + swap * (v (b + i) - v (a + i))
def Y (i : Nat) : Expr := v (b + i) + swap * (v (a + i) - v (b + i))
def sX : Expr := v sa + swap * (v sb - v sa)
def sY : Expr := v sb + swap * (v sa - v sb)
def topInd (i : Nat) : Expr := if i = 1 then 1 - v is64 else if i = 3 then v is64 else 0
def flipX (i : Nat) : Expr := signed * (32768 - B16 * sX) * topInd i
def flipY (i : Nat) : Expr := signed * (32768 - B16 * sY) * topInd i
def brIn (i : Nat) : Expr := if i = 0 then 0 else v (br + i - 1)
def limbEq (i : Nat) : Expr :=
  X i + flipX i - (Y i + flipY i) - brIn i - v (d + i) + B16 * v (br + i)
def lt : Expr := (1 - v is64) * v (br + 1) + v is64 * v (br + 3)
def zsum : Expr := v d + v (d + 1) + v (d + 2) + v (d + 3)
def eqf : Expr := 1 - zsum * v inv
def res : Expr := (v fEqz + v fEq) * eqf + v fNe * (1 - eqf) +
  (v fLtS + v fLtU + v fGtS + v fGtU) * lt + (v fLeS + v fLeU + v fGeS + v fGeU) * (1 - lt)
def topA : Expr := v is64 * v (a + 3) + (1 - v is64) * v (a + 1)
def topB : Expr := v is64 * v (b + 3) + (1 - v is64) * v (b + 1)
def slotA : Expr := v kSb + v cH - 2 + v fEqz
def constraints : List Expr :=
  (flags.map fun f => bool (v f)) ++ [bool act, bool (v is64)] ++
  ((List.range 4).map fun i => v fEqz * v (b + i)) ++
  [(1 - v is64) * v (a + 2), (1 - v is64) * v (a + 3),
   (1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3),
   bool (v sa), bool (v sb), topA - 32768 * v sa - v ra, topB - 32768 * v sb - v rb] ++
  ((List.range 4).map fun i => bool (v (br + i))) ++
  [(1 - v is64) * v (d + 2), (1 - v is64) * v (d + 3),
   (1 - v is64) * v (br + 2), (1 - v is64) * v (br + 3),
   limbEq 0, limbEq 1, v is64 * limbEq 2, v is64 * limbEq 3,
   zsum * eqf]
def inters : List Inter :=
  stdState kSb kCid op zeros4 act ++
  [stkRecv slotA (v is64) (limbsOf a) (v ta) act,
   stkRecv (v kSb + v cH - 1) (v is64) (limbsOf b) (v tb) (act - v fEqz)] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) (act - v fEqz) ++
  [stkSend slotA 0 [res, 0, 0, 0] (v cTs) act] ++
  ((List.range 4).map fun i => r16 (v (d + i)) act) ++
  [r16 (2 * v ra) act, r16 (2 * v rb) act]
def table : Table := ⟨"CMP", cols, constraints, inters⟩
end Cmp

/-! ## CONST: i32.const, i64.const (immediate from the code record) -/
namespace Const
def kSb : Nat := 11
def kCid : Nat := 12
def act : Nat := 5
def is64 : Nat := 6
def imm : Nat := 7   -- 7..10
def cols : List String := headerCols ++ ["act", "is64", "imm0", "imm1", "imm2", "imm3"] ++ frameCols
def op : Expr := 0x41 + v is64
def constraints : List Expr :=
  [bool (v act), bool (v is64), (1 - v is64) * v (imm + 2), (1 - v is64) * v (imm + 3)]
def inters : List Inter :=
  stdState kSb kCid op (limbsOf imm) (v act) ++ [stkSend (v kSb + v cH) (v is64) (limbsOf imm) (v cTs) (v act)]
def table : Table := ⟨"CONST", cols, constraints, inters⟩
end Const

/-! ## STACK: drop, select -/
namespace Stack
def kSb : Nat := 28
def kCid : Nat := 29
def fDrop : Nat := 5
def fSel : Nat := 6
def tagA : Nat := 7
def A : Nat := 8     -- 8..11 (dropped value, or the select condition)
def tA : Nat := 12
def hA : Nat := 13
def tagV : Nat := 14
def V2 : Nat := 15   -- 15..18
def t2 : Nat := 19
def h2 : Nat := 20
def V1 : Nat := 21   -- 21..24
def t1 : Nat := 25
def h1 : Nat := 26
def inv : Nat := 27
def cols : List String := headerCols ++ ["f_drop", "f_sel", "tagA", "A0", "A1", "A2", "A3", "tA", "hA",
  "tagV", "V2_0", "V2_1", "V2_2", "V2_3", "t2", "h2", "V1_0", "V1_1", "V1_2", "V1_3", "t1", "h1", "inv"] ++ frameCols
def act : Expr := v fDrop + v fSel
def op : Expr := 0x1A * v fDrop + 0x1B * v fSel
def cz : Expr := v A + v (A + 1)
def nz : Expr := cz * v inv
def out (i : Nat) : Expr := nz * v (V1 + i) + (1 - nz) * v (V2 + i)
def constraints : List Expr :=
  [bool (v fDrop), bool (v fSel), v fDrop * v fSel, bool (v tagA), bool (v tagV),
   v fSel * v tagA,
   (1 - v tagA) * v (A + 2), (1 - v tagA) * v (A + 3),
   (1 - v tagV) * v (V2 + 2), (1 - v tagV) * v (V2 + 3),
   (1 - v tagV) * v (V1 + 2), (1 - v tagV) * v (V1 + 3),
   cz * (1 - nz)]
def inters : List Inter :=
  stdState kSb kCid op zeros4 act ++
  [stkRecv (v kSb + v cH - 1) (v tagA) (limbsOf A) (v tA) act] ++ timeChk (v cTs) (v tA) (v hA) act ++
  [stkRecv (v kSb + v cH - 2) (v tagV) (limbsOf V2) (v t2) (v fSel),
   stkRecv (v kSb + v cH - 3) (v tagV) (limbsOf V1) (v t1) (v fSel)] ++
  timeChk (v cTs) (v t2) (v h2) (v fSel) ++ timeChk (v cTs) (v t1) (v h1) (v fSel) ++
  [stkSend (v kSb + v cH - 3) (v tagV) ((List.range 4).map out) (v cTs) (v fSel)]
def table : Table := ⟨"STACK", cols, constraints, inters⟩
end Stack

/-! ## CTRL: block / loop / nested end (NEXT), br (JUMP), br_if (JUMPIF), end-of-function /
return / br to the function label (HALT), br_if to the function label (HALTIF).  Labels and target
pcs are static (code record field `x0`); under the no-discard domain condition branches do not
touch the operand stack. -/
namespace Ctrl
def kSb : Nat := 16
def kCid : Nat := 17
def fNext : Nat := 5
def fJump : Nat := 6
def fJif : Nat := 7
def fHalt : Nat := 8
def fHif : Nat := 9
def tgt : Nat := 10
def c : Nat := 11    -- 11, 12
def tc : Nat := 13
def hc : Nat := 14
def inv : Nat := 15
def cols : List String := headerCols ++ ["f_next", "f_jump", "f_jif", "f_halt", "f_hif", "tgt",
  "c0", "c1", "tc", "hc", "inv"] ++ frameCols
def opNext : Nat := 0x101
def opJump : Nat := 0x102
def opJif : Nat := 0x103
def opHalt : Nat := 0x104
def opHif : Nat := 0x105
def act : Expr := v fNext + v fJump + v fJif + v fHalt + v fHif
def cnd : Expr := v fJif + v fHif
def op : Expr := Expr.c opNext * v fNext + Expr.c opJump * v fJump + Expr.c opJif * v fJif +
  Expr.c opHalt * v fHalt + Expr.c opHif * v fHif
def nz : Expr := (v c + v (c + 1)) * v inv
def pc1 : Expr := v cPc + 1
def pcNext : Expr := v fNext * pc1 + v fJump * v tgt + v fJif * (nz * v tgt + (1 - nz) * pc1) +
  v fHalt * v cPc + v fHif * (nz * v cPc + (1 - nz) * pc1)
def halted : Expr := v fHalt + v fHif * nz
def constraints : List Expr :=
  [bool (v fNext), bool (v fJump), bool (v fJif), bool (v fHalt), bool (v fHif), bool act,
   (v c + v (c + 1)) * (1 - nz),
   -- HALT / HALTIF (end of the function) only in the entry frame (calls: family 4)
   (v fHalt + v fHif) * v kCid]
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) act,
   stateOut pcNext (v cTs + 1) (v cS + v cFee) halted (v kSb) (v kCid) act,
   fetch (v cPc) op (v cH) (v cFee) [v tgt, 0, 0, 0] act,
   stkRecv (v kSb + v cH - 1) 0 [v c, v (c + 1), 0, 0] (v tc) cnd] ++
  timeChk (v cTs) (v tc) (v hc) cnd
def table : Table := ⟨"CTRL", cols, constraints, inters⟩
end Ctrl

/-! ## LOCAL: local.get/set/tee and global.get/set (locals are channel space `16 + cid`, globals
space 2: every access consumes the current record and produces a fresh one) -/
namespace Local
def kSb : Nat := 23
def kCid : Nat := 24
def fGet : Nat := 5
def fSet : Nat := 6
def fTee : Nat := 7
def idx : Nat := 8
def tagL : Nat := 9
def L : Nat := 10    -- 10..13 (old local / global value)
def tL : Nat := 14
def hL : Nat := 15
def tagV : Nat := 16
def V : Nat := 17    -- 17..20 (stack value, set/tee)
def tV : Nat := 21
def hV : Nat := 22
/-- inverse of the channel space of the accessed variable (non-zero, so the produced variable and
stack messages differ) -/
def invSp : Nat := 25
def fGGet : Nat := 26
def fGSet : Nat := 27
def cols : List String := headerCols ++ ["f_get", "f_set", "f_tee", "idx", "tagL", "L0", "L1", "L2", "L3",
  "tL", "hL", "tagV", "V0", "V1", "V2", "V3", "tV", "hV"] ++ frameCols ++ ["inv_sp", "f_gget", "f_gset"]
def act : Expr := v fGet + v fSet + v fTee + v fGGet + v fGSet
/-- reads the old value (local.get, global.get) -/
def rd : Expr := v fGet + v fGGet
/-- writes a stack value (local.set, local.tee, global.set) -/
def wr : Expr := v fSet + v fTee + v fGSet
def isG : Expr := v fGGet + v fGSet
def op : Expr := 0x20 + v fSet + 2 * v fTee + 3 * v fGGet + 4 * v fGSet
/-- channel space: `16 + cid` (locals of the current activation) or 2 (globals) -/
def space : Expr := (1 - isG) * (16 + v kCid) + 2 * isG
def newTag : Expr := rd * v tagL + wr * v tagV
def newVal (i : Nat) : Expr := rd * v (L + i) + wr * v (V + i)
def constraints : List Expr :=
  [bool (v fGet), bool (v fSet), bool (v fTee), bool act, bool (v tagL), bool (v tagV),
   (1 - v tagL) * v (L + 2), (1 - v tagL) * v (L + 3),
   (1 - v tagV) * v (V + 2), (1 - v tagV) * v (V + 3),
   act * (space * v invSp - 1), bool (v fGGet), bool (v fGSet)]
def inters : List Inter :=
  stdState kSb kCid op [v idx, 0, 0, 0] act ++
  [chRecv space (v idx) (v tagL) (limbsOf L) (v tL) act] ++ timeChk (v cTs) (v tL) (v hL) act ++
  [chSend space (v idx) newTag ((List.range 4).map newVal) (v cTs) act,
   stkRecv (v kSb + v cH - 1) (v tagV) (limbsOf V) (v tV) wr] ++ timeChk (v cTs) (v tV) (v hV) wr ++
  [stkSend (v kSb + v cH - 1 + rd) newTag ((List.range 4).map newVal) (v cTs) (v fGet + v fTee + v fGGet)]
def table : Table := ⟨"LOCAL", cols, constraints, inters⟩
end Local

/-! ## BOUNDARY (height 4): initial / final state, final stack value, initial / final locals of the
entry frame (space 16). -/
namespace Boundary
def pcf : Nat := 0
def tpr : Nat := 1
/-- the final STATE message's frame fields (free: a trap may happen in any frame) -/
def sbf : Nat := 2
def cidf : Nat := 3
/-- per local `j`: final tag, value limbs, producer time (6 columns from `4 + 6 j`) -/
def fin (j : Nat) : Nat := 4 + 6 * j
/-- Public values: `[N, S_final, nres, rtag, r0, r1, r2, r3, status, mem, dataEnd]`, then one tag per local,
then per global `[tag, v0, v1, v2, v3]` (its initial value; globals are channel space 2), then the
initial stack budget `stackRem` as two 16-bit limbs (channel space 5)
(`status` = 1: the function returned; 2: it trapped).  The code is not public: it is the cached CODE
table, whose commitment is a statement component (`code_root`).  The first instruction row has
`ts = 1`; initial locals are produced at time 0. -/
def pubN : Nat := 0
def pubS : Nat := 1
def pubNres : Nat := 2
def pubTag : Nat := 3
def pubR : Nat := 4
def pubStatus : Nat := 8
/-- memory size in bytes (`pages · 65536`, constant: no `memory.grow`) -/
def pubMem : Nat := 9
/-- end of the data image: bytes at addresses `≥ pubDataEnd` are initially 0 -/
def pubDataEnd : Nat := 10
def pubLoc : Nat := 11
def recWidth : Nat := 8
def cols (nloc : Nat) : List String := ["pcf", "tpr", "sbf", "cidf"] ++
  ((List.range nloc).flatMap fun j => [s!"ftag{j}", s!"fv{j}_0", s!"fv{j}_1", s!"fv{j}_2", s!"fv{j}_3", s!"ftp{j}"])
def inters (nloc ngl : Nat) : List Inter :=
  [stateOut 0 1 0 0 0 0 .first,
   ⟨busState, false, .first, [v pcf, pv pubN, pv pubS, pv pubStatus, v sbf, v cidf]⟩,
   -- the result is returned only if the function did not trap
   stkRecv 0 (pv pubTag) ((List.range 4).map fun i => pv (pubR + i)) (v tpr)
     (.first * pv pubNres * (2 - pv pubStatus))] ++
  ((List.range nloc).flatMap fun j =>
    [chSend 16 (Expr.c j) (pv (pubLoc + j)) zeros4 0 .first,
     chRecv 16 (Expr.c j) (v (fin j)) ((List.range 4).map fun i => v (fin j + 1 + i)) (v (fin j + 5)) .first]) ++
  ((List.range ngl).map fun g =>
    chSend 2 (Expr.c g) (pv (pubLoc + nloc + 5 * g)) ((List.range 4).map fun i => pv (pubLoc + nloc + 5 * g + 1 + i))
      0 .first) ++
  -- the initial stack-budget register (space 5): `stackRem` as two limbs from the public values
  [chSend 5 0 0 [pv (pubLoc + nloc + 5 * ngl), pv (pubLoc + nloc + 5 * ngl + 1), 0, 0] 0 .first]
def table (nloc ngl : Nat) : Table := ⟨"BOUNDARY", cols nloc, [], inters nloc ngl⟩
end Boundary

/-! ## CODE: the code records `[pc, op, h, fee, x0..x3]` as a **cached** trace (columns 0..7; the
multiplicity column 8 is in the common main).  Its commitment `code_root` is exposed by L1 and
checked by V_d against the contract's code (`code_hash`): the canonical CODE matrix is a
deterministic function of the code (records in pc order, padded by repeating the last record). -/
namespace Code
def mult : Nat := 8
def cachedWidth : Nat := 8
def cols : List String := ["pc", "op", "h", "fee", "x0", "x1", "x2", "x3", "mult"]
def table : Table :=
  ⟨"CODE", cols, [], [⟨busFetch, false, v mult, (List.range 8).map v⟩]⟩
end Code

/-! ## RANGE16: the committed, derived table `v = row index`, height exactly `2^16`. -/
namespace Range16
def val : Nat := 0
def m : Nat := 1
def constraints : List Expr :=
  [.first * v val, .trans * (nv val - v val - 1), .last * (v val - 65535)]
def table : Table := ⟨"RANGE16", ["v", "m"], constraints, [⟨busR16, false, v m, [v val]⟩]⟩
end Range16

/-! ## BYTE: committed, derived table over all byte pairs `(x, y)` (bits), height exactly `2^16`,
answering pair-range (kind 0), and (1), or (2), xor (3). -/
namespace Byte
def xb : Nat := 0    -- 0..7
def yb : Nat := 8    -- 8..15
def m : Nat := 16    -- 16..19
def cols : List String := ((List.range 8).map fun i => s!"x{i}") ++ ((List.range 8).map fun i => s!"y{i}") ++
  ["m0", "m1", "m2", "m3"]
def bitsum (col : Nat → Expr) (base : Nat) (f : Expr → Expr → Expr) : Expr :=
  ((List.range 8).map fun i => Expr.c (2 ^ i) * f (col (base + i)) (col (base + 8 + i))).foldl (· + ·) 0
def X : Expr := ((List.range 8).map fun i => Expr.c (2 ^ i) * v (xb + i)).foldl (· + ·) 0
def Y : Expr := ((List.range 8).map fun i => Expr.c (2 ^ i) * v (yb + i)).foldl (· + ·) 0
def key : Expr := X + 256 * Y
def nkey : Expr := ((List.range 8).map fun i => Expr.c (2 ^ i) * nv (xb + i)).foldl (· + ·) 0 +
  256 * ((List.range 8).map fun i => Expr.c (2 ^ i) * nv (yb + i)).foldl (· + ·) 0
def andE : Expr := bitsum v 0 fun x y => x * y
def orE : Expr := bitsum v 0 fun x y => x + y - x * y
def xorE : Expr := bitsum v 0 fun x y => x + y - 2 * x * y
def constraints : List Expr :=
  ((List.range 16).map fun i => bool (v i)) ++
  [.first * key, .trans * (nkey - key - 1), .last * (key - 65535)]
def inters : List Inter :=
  [⟨busByte, false, v m, [0, X, Y, 0]⟩,
   ⟨busByte, false, v (m + 1), [1, X, Y, andE]⟩,
   ⟨busByte, false, v (m + 2), [2, X, Y, orE]⟩,
   ⟨busByte, false, v (m + 3), [3, X, Y, xorE]⟩]
def table : Table := ⟨"BYTE", cols, constraints, inters⟩
end Byte

/-! ## DIV: i32/i64 div_s, div_u, rem_s, rem_u, with traps

Magnitudes: `A = |a|`, `B = |b|` (signed ops; `= a, b` for unsigned) via negation chains
`A + a ∈ {0, 2^w}`; the byte product `Q·B + R = A` (no overflow: high convolution sums and the top
carry vanish) and `R < B` (borrow chain, `D = B − R − 1 ≥ 0`); the result is `±Q` or `±R`
(negation chain with the result sign).  Traps: `tz = [B = 0]` (inverse test; the division is only
enforced when `tz = 0`) and `tov = div_s · sign(a) · sign(b) · topbit(Q)` (for div_s, `Q ≤ 2^(w−1)`
with equality exactly when `a = MIN`, `b = ±1`).  A trapping row consumes its operands, produces
nothing and ends the execution (`halted = 2`). -/
namespace Div
def kSb : Nat := 95
def kCid : Nat := 96
def fDivS : Nat := 5
def fDivU : Nat := 6
def fRemS : Nat := 7
def fRemU : Nat := 8
def is64 : Nat := 9
def a : Nat := 10    -- 10..13
def ta : Nat := 14
def ha : Nat := 15
def b : Nat := 16    -- 16..19
def tb : Nat := 20
def hb : Nat := 21
def hbA : Nat := 22  -- top bit of a
def ra : Nat := 23
def hbB : Nat := 24
def rb : Nat := 25
def AB : Nat := 26   -- A bytes 26..33
def BB : Nat := 34   -- B bytes 34..41
def QB : Nat := 42   -- Q bytes 42..49
def RB : Nat := 50   -- R bytes 50..57
def ca : Nat := 58   -- 58..61
def cb : Nat := 62   -- 62..65
def cy : Nat := 66   -- 66..73
def dd : Nat := 74   -- D limbs 74..77
def bw : Nat := 78   -- borrows 78..81
def tz : Nat := 82
def invB : Nat := 83
def hbQ : Nat := 84  -- top bit of Q
def rq : Nat := 85
def tov : Nat := 86
def res : Nat := 87  -- 87..90
def cr : Nat := 91   -- 91..94
def names (p : String) (n : Nat) : List String := (List.range n).map fun i => p ++ toString i
def cols : List String := headerCols ++ ["f_divs", "f_divu", "f_rems", "f_remu", "is64"] ++ names "a" 4 ++
  ["ta", "ha"] ++ names "b" 4 ++ ["tb", "hb", "hbA", "ra", "hbB", "rb"] ++ names "A" 8 ++ names "B" 8 ++
  names "Q" 8 ++ names "R" 8 ++ names "ca" 4 ++ names "cb" 4 ++ names "cy" 8 ++ names "d" 4 ++ names "bw" 4 ++
  ["tz", "invB", "hbQ", "rq", "tov"] ++ names "res" 4 ++ names "cr" 4 ++ frameCols
def act : Expr := v fDivS + v fDivU + v fRemS + v fRemU
def signed : Expr := v fDivS + v fRemS
def trap : Expr := v tz + v tov
/-- the division is enforced on active rows unless `B = 0` (`tz ≤ act`) -/
def nt : Expr := act - v tz
def op : Expr := 0x6D + 18 * v is64 + v fDivU + 2 * v fRemS + 3 * v fRemU
def sa : Expr := signed * v hbA
def sb : Expr := signed * v hbB
/-- 16-bit limb `i` of a byte vector. -/
def L (base i : Nat) : Expr := v (base + 2 * i) + 256 * v (base + 2 * i + 1)
def topA : Expr := v is64 * v (a + 3) + (1 - v is64) * v (a + 1)
def topB : Expr := v is64 * v (b + 3) + (1 - v is64) * v (b + 1)
def cIn (c i : Nat) : Expr := if i = 0 then 0 else v (c + i - 1)
/-- `s = 0 → X_i = x_i`; `s = 1 → X_i + x_i + c_{i-1} = 2^16 c_i` (limbs 2, 3 only for i64). -/
def negChain (s : Expr) (X : Nat → Expr) (x : Nat → Expr) (c : Nat) : List Expr :=
  (List.range 4).flatMap fun i =>
    let g : Expr := if i < 2 then 1 else v is64
    [g * ((1 - s) * (X i - x i)), g * (s * (X i + x i + cIn c i - B16 * v (c + i)))]
def conv (k : Nat) : Expr :=
  ((List.range 8).filterMap fun i => if i ≤ k ∧ k - i < 8 then some (v (QB + i) * v (BB + (k - i))) else none).foldl
    (· + ·) 0
def prodEq (k : Nat) : Expr := conv k + v (RB + k) + cIn cy k - v (AB + k) - 256 * v (cy + k)
def ltEq (i : Nat) : Expr :=
  L BB i - L RB i - (if i = 0 then 1 else 0) - cIn bw i + B16 * v (bw + i) - v (dd + i)
def bsum : Expr := ((List.range 8).map fun i => v (BB + i)).foldl (· + ·) 0
def topQ : Expr := v is64 * L QB 3 + (1 - v is64) * L QB 1
def isDiv : Expr := v fDivS + v fDivU
def isRem : Expr := v fRemS + v fRemU
/-- result sign: div_s: `sa xor sb`; rem_s: `sa`. -/
def sres : Expr := v fDivS * (v hbA + v hbB - 2 * v hbA * v hbB) + v fRemS * v hbA
def X (i : Nat) : Expr := isDiv * L QB i + isRem * L RB i
def constraints : List Expr :=
  [bool (v fDivS), bool (v fDivU), bool (v fRemS), bool (v fRemU), bool act, bool (v is64),
   bool (v hbA), bool (v hbB), topA - 32768 * v hbA - v ra, topB - 32768 * v hbB - v rb,
   (1 - v is64) * v (a + 2), (1 - v is64) * v (a + 3), (1 - v is64) * v (b + 2), (1 - v is64) * v (b + 3),
   (1 - v is64) * v (res + 2), (1 - v is64) * v (res + 3),
   bool (v hbQ), topQ - 32768 * v hbQ - v rq] ++
  ((List.range 4).flatMap fun i =>
    [(1 - v is64) * v (AB + 4 + i), (1 - v is64) * v (BB + 4 + i), (1 - v is64) * v (QB + 4 + i),
     (1 - v is64) * v (RB + 4 + i), (1 - v is64) * v (cy + 4 + i)]) ++
  ((List.range 4).map fun i => bool (v (ca + i))) ++ ((List.range 4).map fun i => bool (v (cb + i))) ++
  ((List.range 4).map fun i => bool (v (cr + i))) ++ ((List.range 4).map fun i => bool (v (bw + i))) ++
  negChain sa (L AB) (fun i => v (a + i)) ca ++ negChain sb (L BB) (fun i => v (b + i)) cb ++
  -- zero test of B and the overflow test
  [v tz - act * (1 - bsum * v invB), bsum * v tz,
   v tov - nt * v fDivS * v hbA * v hbB * v hbQ] ++
  -- the division (non-trap rows)
  ((List.range 8).map fun k => nt * prodEq k) ++
  [nt * (1 - v is64) * v (cy + 3), nt * v is64 * v (cy + 7)] ++
  ((List.range 3).map fun j => nt * (1 - v is64) * conv (4 + j)) ++
  ((List.range 7).map fun j => nt * v is64 * conv (8 + j)) ++
  ((List.range 4).map fun i => nt * ltEq i) ++ [nt * v (bw + 3)] ++
  -- the result
  negChain sres (fun i => v (res + i)) X cr
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) act,
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) (2 * trap) (v kSb) (v kCid) act,
   fetch (v cPc) op (v cH) (v cFee) zeros4 act,
   stkRecv (v kSb + v cH - 2) (v is64) (limbsOf a) (v ta) act,
   stkRecv (v kSb + v cH - 1) (v is64) (limbsOf b) (v tb) act] ++
  timeChk (v cTs) (v ta) (v ha) act ++ timeChk (v cTs) (v tb) (v hb) act ++
  [stkSend (v kSb + v cH - 2) (v is64) (limbsOf res) (v cTs) (act * (1 - trap)),
   r16 (2 * v ra) act, r16 (2 * v rb) act, r16 (2 * v rq) act] ++
  (List.range 4).map (fun i => byteQ 0 (v (AB + 2 * i)) (v (AB + 2 * i + 1)) 0 act) ++
  (List.range 4).map (fun i => byteQ 0 (v (BB + 2 * i)) (v (BB + 2 * i + 1)) 0 act) ++
  (List.range 4).map (fun i => byteQ 0 (v (QB + 2 * i)) (v (QB + 2 * i + 1)) 0 act) ++
  (List.range 4).map (fun i => byteQ 0 (v (RB + 2 * i)) (v (RB + 2 * i + 1)) 0 act) ++
  (List.range 4).map (fun i => r16 (v (dd + i)) act) ++
  (List.range 4).map (fun i => r16 (v (res + i)) act) ++
  -- product carries (≤ ~2^11): without this the product chain only holds mod p
  (List.range 8).map (fun k => r16 (v (cy + k)) act)
def table : Table := ⟨"DIV", cols, constraints, inters⟩
end Div


/-! ## DRAIN: at the end, each DRAIN row consumes one leftover channel message: memory bytes (space
≠ 0) always, operand-stack messages (space 0) only after a trap (`status = 2`):
`act · (1 − space·inv) · (status − 2) = 0`. -/
namespace Drain
def act : Nat := 0
def space : Nat := 1
def slot : Nat := 2
def tag : Nat := 3
def val : Nat := 4   -- 4..7
def tp : Nat := 8
def inv : Nat := 9
def cols : List String := ["act", "space", "slot", "tag", "v0", "v1", "v2", "v3", "tp", "inv"]
def table : Table :=
  ⟨"DRAIN", cols,
   [bool (v act), v act * (1 - v space * v inv) * (pv Boundary.pubStatus - 2)],
   [chRecv (v space) (v slot) (v tag) (limbsOf val) (v tp) (v act)]⟩
end Drain

/-! ## LOAD: `i32/i64.load*` (12 integer loads, one-hot flags)

The address `a` (2 limbs, from the stack) plus the static offset is the effective address
`ea = e0 + 2^16·e1` (exact: `a0 + off0 = e0 + 2^16·c`, `e1 = a1 + off1 + c`, `e0 < 2^16`,
`e1 < 2^11`).  The `w` bytes at `ea + i` are consumed and produced again (memory channel, space 3);
the result limbs are the little-endian bytes, sign-extended from the top byte's bit `sbit` for the
signed loads. -/
namespace Load
/-- `(opcode, width, signed, is64)` in flag order (`loadSpec`). -/
def ops : List (Nat × Nat × Bool × Bool) :=
  [(0x28, 4, false, false), (0x29, 8, false, true), (0x2C, 1, true, false), (0x2D, 1, false, false),
   (0x2E, 2, true, false), (0x2F, 2, false, false), (0x30, 1, true, true), (0x31, 1, false, true),
   (0x32, 2, true, true), (0x33, 2, false, true), (0x34, 4, true, true), (0x35, 4, false, true)]
def fl (k : Nat) : Nat := 5 + k   -- 5..16
def a : Nat := 17    -- 17, 18
def ta : Nat := 19
def ha : Nat := 20
def off : Nat := 21  -- 21, 22
def e : Nat := 23    -- 23, 24
def cyE : Nat := 25
def b : Nat := 26    -- 26..33
def tb : Nat := 34   -- 34..41
def hb : Nat := 42   -- 42..49
def sbit : Nat := 50
def low7 : Nat := 51
def r : Nat := 52    -- 52..55
def kSb : Nat := 56
def kCid : Nat := 57
def names (p : String) (n : Nat) : List String := (List.range n).map fun i => p ++ toString i
def cols : List String := headerCols ++ names "f" 12 ++ ["a0", "a1", "ta", "ha", "off0", "off1", "e0", "e1", "cyE"] ++
  names "b" 8 ++ names "tb" 8 ++ names "hb" 8 ++ ["sbit", "low7"] ++ names "r" 4 ++ frameCols
/-- Sum of the flags of the ops satisfying `p`. -/
def sumF (p : Nat × Nat × Bool × Bool → Bool) : Expr :=
  ((List.range 12).filter fun k => p (ops.getD k default)).foldl (fun acc k => acc + v (fl k)) 0
def act : Expr := sumF fun _ => true
def is64 : Expr := sumF fun o => o.2.2.2
def sgn : Expr := sumF fun o => o.2.2.1
/-- byte `i` is accessed (`i < w`) -/
def cnt (i : Nat) : Expr := sumF fun o => decide (i < o.2.1)
/-- byte `i` is the top byte (`i = w − 1`) -/
def lastE (i : Nat) : Expr := sumF fun o => decide (o.2.1 = i + 1)
def op : Expr := (List.range 12).foldl (fun acc k => acc + Expr.c (ops.getD k default).1 * v (fl k)) 0
def eaE : Expr := v e + 65536 * v (e + 1)
def ext (i : Nat) : Expr := sgn * v sbit * 255 * (if i < 4 then 1 else is64)
def B (i : Nat) : Expr := cnt i * v (b + i) + (1 - cnt i) * ext i
def topB : Expr := (List.range 8).foldl (fun acc i => acc + lastE i * v (b + i)) 0
def constraints : List Expr :=
  (List.range 12).map (fun k => bool (v (fl k))) ++
  [bool act, bool (v cyE), bool (v sbit),
   v a + v off - v e - 65536 * v cyE,
   v (e + 1) - v (a + 1) - v (off + 1) - v cyE,
   topB - 128 * v sbit - v low7] ++
  (List.range 4).map fun j => v (r + j) - (B (2 * j) + 256 * B (2 * j + 1))
def inters : List Inter :=
  stdState kSb kCid op [v off, v (off + 1), 0, 0] act ++
  [stkRecv (v kSb + v cH - 1) 0 [v a, v (a + 1), 0, 0] (v ta) act] ++ timeChk (v cTs) (v ta) (v ha) act ++
  [r16 (v e) act, r16 (32 * v (e + 1)) act, r16 (512 * v low7) act] ++
  (List.range 8).flatMap (fun i =>
    [chRecv 3 (eaE + Expr.c i) 0 [v (b + i), 0, 0, 0] (v (tb + i)) (cnt i)] ++
    timeChk (v cTs) (v (tb + i)) (v (hb + i)) (cnt i) ++
    [chSend 3 (eaE + Expr.c i) 0 [v (b + i), 0, 0, 0] (v cTs) (cnt i)]) ++
  [stkSend (v kSb + v cH - 1) is64 (limbsOf r) (v cTs) act]
def table : Table := ⟨"LOAD", cols, constraints, inters⟩
end Load

/-! ## STORE: `i32/i64.store*` (7 integer stores, one-hot flags)

The value (top of the stack, tag `is64`) is split into bytes `vb` (byte-pair range lookups); the
address and `ea` as in LOAD; the `w` old bytes at `ea + i` are consumed and the new ones
(`vb_i`) produced. -/
namespace Store
/-- `(opcode, width, is64)` in flag order (`storeWidth`). -/
def ops : List (Nat × Nat × Bool) :=
  [(0x36, 4, false), (0x37, 8, true), (0x3A, 1, false), (0x3B, 2, false), (0x3C, 1, true), (0x3D, 2, true),
   (0x3E, 4, true)]
def fl (k : Nat) : Nat := 5 + k   -- 5..11
def vl : Nat := 12   -- 12..15
def tv : Nat := 16
def hv : Nat := 17
def vb : Nat := 18   -- 18..25
def a : Nat := 26    -- 26, 27
def ta : Nat := 28
def ha : Nat := 29
def off : Nat := 30  -- 30, 31
def e : Nat := 32    -- 32, 33
def cyE : Nat := 34
def ob : Nat := 35   -- 35..42
def tob : Nat := 43  -- 43..50
def hob : Nat := 51  -- 51..58
def kSb : Nat := 59
def kCid : Nat := 60
def cols : List String := headerCols ++ Load.names "f" 7 ++ Load.names "v" 4 ++ ["tv", "hv"] ++ Load.names "vb" 8 ++
  ["a0", "a1", "ta", "ha", "off0", "off1", "e0", "e1", "cyE"] ++ Load.names "ob" 8 ++ Load.names "tob" 8 ++
  Load.names "hob" 8 ++ frameCols
def sumF (p : Nat × Nat × Bool → Bool) : Expr :=
  ((List.range 7).filter fun k => p (ops.getD k default)).foldl (fun acc k => acc + v (fl k)) 0
def act : Expr := sumF fun _ => true
def is64 : Expr := sumF fun o => o.2.2
def cnt (i : Nat) : Expr := sumF fun o => decide (i < o.2.1)
def op : Expr := (List.range 7).foldl (fun acc k => acc + Expr.c (ops.getD k default).1 * v (fl k)) 0
def eaE : Expr := v e + 65536 * v (e + 1)
def constraints : List Expr :=
  (List.range 7).map (fun k => bool (v (fl k))) ++
  [bool act, bool (v cyE),
   v a + v off - v e - 65536 * v cyE,
   v (e + 1) - v (a + 1) - v (off + 1) - v cyE] ++
  (List.range 4).map fun j => v (vl + j) - v (vb + 2 * j) - 256 * v (vb + 2 * j + 1)
def inters : List Inter :=
  stdState kSb kCid op [v off, v (off + 1), 0, 0] act ++
  [stkRecv (v kSb + v cH - 1) is64 (limbsOf vl) (v tv) act] ++ timeChk (v cTs) (v tv) (v hv) act ++
  [stkRecv (v kSb + v cH - 2) 0 [v a, v (a + 1), 0, 0] (v ta) act] ++ timeChk (v cTs) (v ta) (v ha) act ++
  [r16 (v e) act, r16 (32 * v (e + 1)) act] ++
  (List.range 4).map (fun j => byteQ 0 (v (vb + 2 * j)) (v (vb + 2 * j + 1)) 0 act) ++
  (List.range 8).flatMap (fun i =>
    [chRecv 3 (eaE + Expr.c i) 0 [v (ob + i), 0, 0, 0] (v (tob + i)) (cnt i)] ++
    timeChk (v cTs) (v (tob + i)) (v (hob + i)) (cnt i) ++
    [chSend 3 (eaE + Expr.c i) 0 [v (vb + i), 0, 0, 0] (v cTs) (cnt i)])
def table : Table := ⟨"STORE", cols, constraints, inters⟩
end Store

/-! ## MEMINIT: one row per touched byte, producing its initial memory message (time 0).

Active rows first; addresses strictly increasing (`ad' − ad − 1 = glo + 2^16·ghi`, `ghi < 2^11`),
`ad < 2^27` and `ad < mem`; a byte in the data image (`zd = 0`) is looked up in DATA, a byte
beyond it (`zd = 1`, `ad ≥ dataEnd`) is 0. -/
namespace MemInit
def act : Nat := 0
def ad : Nat := 1
def bv : Nat := 2
def zd : Nat := 3
def glo : Nat := 4
def ghi : Nat := 5
def alo : Nat := 6
def ahi : Nat := 7
def mlo : Nat := 8
def mhi : Nat := 9
def dlo : Nat := 10
def dhi : Nat := 11
def cols : List String := ["act", "ad", "bv", "zd", "glo", "ghi", "alo", "ahi", "mlo", "mhi", "dlo", "dhi"]
def constraints : List Expr :=
  [bool (v act), bool (v zd), v zd * v bv,
   .trans * ((1 - v act) * nv act),
   .trans * (nv act * (nv ad - v ad - 1 - nv glo - 65536 * nv ghi)),
   v ad - v alo - 65536 * v ahi,
   v act * (pv Boundary.pubMem - 1 - v ad - v mlo - 65536 * v mhi),
   v act * v zd * (v ad - pv Boundary.pubDataEnd - v dlo - 65536 * v dhi)]
def inters : List Inter :=
  [chSend 3 (v ad) 0 [v bv, 0, 0, 0] 0 (v act),
   r16 (v glo) (v act), r16 (32 * v ghi) (v act),
   r16 (v alo) (v act), r16 (32 * v ahi) (v act),
   r16 (v mlo) (v act), r16 (32 * v mhi) (v act),
   r16 (v dlo) (v act * v zd), r16 (32 * v dhi) (v act * v zd),
   ⟨busData, true, v act * (1 - v zd), [v ad, v bv]⟩]
def table : Table := ⟨"MEMINIT", cols, constraints, inters⟩
end MemInit

/-! ## DATA: the data image `[addr, byte]` as a **cached** trace (columns 0, 1; multiplicity column
2 in the common main), bound through the statement like CODE: records `(a, img[a])` for
`a < dataEnd` in address order, padded by repeating the last record (`(0, 0)` if the image is
empty). -/
namespace Data
def mult : Nat := 2
def cachedWidth : Nat := 2
def table : Table := ⟨"DATA", ["addr", "byte", "mult"], [], [⟨busData, false, v mult, [v 0, v 1]⟩]⟩
end Data

/-! ## CALL: `call` of a checked function.  Fetches the call record `[pc, 0x10, h, fee, entry, 0, 0,
0]` and the callee's function-table row `[entry, np + 128 nl, charge, prologue, m0..m3]` (bus FUNC);
moves the `np ≤ 8` params from the operand stack into the callee's locals (space `16 + ts`),
produces the declared locals (zero, typed by the mask bits), the call record (space 4, slot `ts`)
and the decremented stack budget (space 5).  New state: `(entry, ts + 1, S + fee + prologue, 0,
sb + h − np, ts)`; `sb + h − np` and `ts` are range-checked below `2^28`. -/
namespace Call
def opCall : Nat := 0x10
def act : Nat := 5
def entry : Nat := 6
def shape : Nat := 7
def charge : Nat := 8
def pro : Nat := 9
def m (q : Nat) : Nat := 10 + q        -- 10..13
def pf (j : Nat) : Nat := 14 + j       -- 14..21: param j present (j < np)
def af (j : Nat) : Nat := 22 + j       -- 22..85: local j present (j < nl)
def tg (j : Nat) : Nat := 86 + j       -- 86..149: local j is i64 (mask bit)
def tagP (j : Nat) : Nat := 150 + 7 * j
def P (j : Nat) : Nat := 151 + 7 * j   -- 4 limbs
def tP (j : Nat) : Nat := 155 + 7 * j
def hP (j : Nat) : Nat := 156 + 7 * j
def r0 : Nat := 206
def r1 : Nat := 207
def tpb : Nat := 208
def hb : Nat := 209
def n0 : Nat := 210
def n1 : Nat := 211
def sbn0 : Nat := 212
def sbn1 : Nat := 213
def ts0 : Nat := 214
def ts1 : Nat := 215
def kSb : Nat := 216
def kCid : Nat := 217
def cols : List String := headerCols ++ ["act", "entry", "shape", "charge", "pro", "m0", "m1", "m2", "m3"] ++
  (List.range 8).map (fun j => s!"pf{j}") ++ (List.range 64).map (fun j => s!"af{j}") ++
  (List.range 64).map (fun j => s!"tg{j}") ++
  ((List.range 8).flatMap fun j => [s!"tagP{j}", s!"P{j}_0", s!"P{j}_1", s!"P{j}_2", s!"P{j}_3", s!"tP{j}", s!"hP{j}"]) ++
  ["r0", "r1", "tpb", "hb", "n0", "n1", "sbn0", "sbn1", "ts0", "ts1"] ++ frameCols
/-- number of params / locals -/
def np : Expr := ((List.range 8).map fun j => v (pf j)).foldl (· + ·) 0
def nl : Expr := ((List.range 64).map fun j => v (af j)).foldl (· + ·) 0
/-- the new stack base `sb + h − np` -/
def sbNew : Expr := v kSb + v cH - np
def maskOf (q : Nat) : Expr := ((List.range 16).map fun i => Expr.c (2 ^ i) * v (tg (16 * q + i))).foldl (· + ·) 0
/-- count of the zero-initialised declared local `j` -/
def lcnt (j : Nat) : Expr := if j < 8 then v (af j) - v (pf j) else v (af j)
def constraints : List Expr :=
  [bool (v act), v (af 0) * (1 - v act)] ++
  (List.range 8).flatMap (fun j => [bool (v (pf j)), v (pf j) * (1 - v (af j))]) ++
  (List.range 7).map (fun j => v (pf (j + 1)) * (1 - v (pf j))) ++
  (List.range 64).map (fun j => bool (v (af j))) ++
  (List.range 63).map (fun j => v (af (j + 1)) * (1 - v (af j))) ++
  (List.range 64).map (fun j => bool (v (tg j))) ++
  [v shape - np - 128 * nl] ++
  (List.range 4).map (fun q => v (m q) - maskOf q) ++
  [v n0 + B16 * v n1 + v charge - v r0 - B16 * v r1,
   sbNew - v sbn0 - B16 * v sbn1,
   v cTs - v ts0 - B16 * v ts1]
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) (v act),
   stateOut (v entry) (v cTs + 1) (v cS + v cFee + v pro) 0 sbNew (v cTs) (v act),
   fetch (v cPc) (Expr.c opCall) (v cH) (v cFee) [v entry, 0, 0, 0] (v act),
   ⟨busFunc, true, v act, [v entry, v shape, v charge, v pro, v (m 0), v (m 1), v (m 2), v (m 3)]⟩,
   chRecv 5 0 0 [v r0, v r1, 0, 0] (v tpb) (v act)] ++ timeChk (v cTs) (v tpb) (v hb) (v act) ++
  [chSend 5 0 0 [v n0, v n1, 0, 0] (v cTs) (v act), r16 (v n0) (v act), r16 (v n1) (v act),
   r16 (4 * v n1) (v act),
   chSend 4 (v cTs) 0 [v cPc + 1, v kSb, v kCid, v charge] (v cTs) (v act),
   r16 (v sbn0) (v act), r16 (v sbn1) (v act), r16 (16 * v sbn1) (v act),
   r16 (v ts0) (v act), r16 (v ts1) (v act), r16 (16 * v ts1) (v act)] ++
  ((List.range 8).flatMap fun j =>
    [stkRecv (sbNew + Expr.c j) (v (tagP j)) (limbsOf (P j)) (v (tP j)) (v (pf j))] ++
    timeChk (v cTs) (v (tP j)) (v (hP j)) (v (pf j)) ++
    [chSend (16 + v cTs) (Expr.c j) (v (tagP j)) (limbsOf (P j)) (v cTs) (v (pf j))]) ++
  (List.range 64).map (fun j => chSend (16 + v cTs) (Expr.c j) (v (tg j)) zeros4 (v cTs) (lcnt j))
def table : Table := ⟨"CALL", cols, constraints, inters⟩
end Call

/-! ## RET: `end` of the body / `return` / `br` (HALT records) and `br_if` (HALTIF records) to the
function label in a callee (`cid ≠ 0`; CTRL handles `cid = 0`).  A taken return consumes the call
record `[4, cid, 0, retpc, sb_c, cid_c, charge, tp]` and the budget register, produces the budget
plus `charge`, and continues at `(retpc, ts + 1, S + fee, 0, sb_c, cid_c)`; under D3 the operand
stack is untouched (the results already sit at the callee's base). -/
namespace Ret
def fRet : Nat := 5
def fRif : Nat := 6
def c : Nat := 7     -- 7, 8
def tc : Nat := 9
def hc : Nat := 10
def inv : Nat := 11
def retpc : Nat := 12
def sbc : Nat := 13
def cidc : Nat := 14
def charge : Nat := 15
def tpr : Nat := 16
def hr : Nat := 17
def r0 : Nat := 18
def r1 : Nat := 19
def tpb : Nat := 20
def hb : Nat := 21
def n0 : Nat := 22
def n1 : Nat := 23
def invc : Nat := 24
def kSb : Nat := 25
def kCid : Nat := 26
def cols : List String := headerCols ++ ["f_ret", "f_rif", "c0", "c1", "tc", "hc", "inv", "retpc", "sbc", "cidc",
  "charge", "tpr", "hr", "r0", "r1", "tpb", "hb", "n0", "n1", "invc"] ++ frameCols
def act : Expr := v fRet + v fRif
def nz : Expr := (v c + v (c + 1)) * v inv
/-- the return is taken -/
def tk : Expr := v fRet + v fRif * nz
def op : Expr := Expr.c Ctrl.opHalt * v fRet + Expr.c Ctrl.opHif * v fRif
def constraints : List Expr :=
  [bool (v fRet), bool (v fRif), bool act, (v c + v (c + 1)) * (1 - nz),
   act * (v kCid * v invc - 1),
   tk * (v n0 + B16 * v n1 - v r0 - B16 * v r1 - v charge)]
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) act,
   stateOut (tk * v retpc + (1 - tk) * (v cPc + 1)) (v cTs + 1) (v cS + v cFee) 0
     (tk * v sbc + (1 - tk) * v kSb) (tk * v cidc + (1 - tk) * v kCid) act,
   fetch (v cPc) op (v cH) (v cFee) zeros4 act,
   stkRecv (v kSb + v cH - 1) 0 [v c, v (c + 1), 0, 0] (v tc) (v fRif)] ++
  timeChk (v cTs) (v tc) (v hc) (v fRif) ++
  [chRecv 4 (v kCid) 0 [v retpc, v sbc, v cidc, v charge] (v tpr) tk] ++ timeChk (v cTs) (v tpr) (v hr) tk ++
  [chRecv 5 0 0 [v r0, v r1, 0, 0] (v tpb) tk] ++ timeChk (v cTs) (v tpb) (v hb) tk ++
  [chSend 5 0 0 [v n0, v n1, 0, 0] (v cTs) tk, r16 (v n0) tk, r16 (v n1) tk, r16 (4 * v n1) tk]
def table : Table := ⟨"RET", cols, constraints, inters⟩
end Ret

/-! ## FUNC: the module's function table as a **cached** trace (columns 0..7; multiplicity column 8),
bound through the statement like CODE: per checked function `[entry, np + 128 nl, charge,
prologue, m0, m1, m2, m3]`. -/
namespace Func
def mult : Nat := 8
def cachedWidth : Nat := 8
def table : Table := ⟨"FUNC", ["entry", "shape", "charge", "pro", "m0", "m1", "m2", "m3", "mult"], [],
  [⟨busFunc, false, v mult, (List.range 8).map v⟩]⟩
end Func

/-! ## IF: `if` (the condition pop and the two-way successor)

`if` **falls through on non-zero** (`pc + 1`) and jumps on zero (`tgt = elseOf + 1`, or
`endOf + 1` when there is no `else`).  That is the opposite polarity to `Ctrl.fJif` (`br_if`,
which *jumps* on non-zero), so the row cannot reuse `fJif`; it is a separate table for the same
reason `ChiAir`/`ShaAir` are separate.  `CTRL` stays byte-identical.

The row is the `if` only.  The `else` body's unconditional jump to `end + 1` is the existing
`Ctrl.fJump` (`step_else`), so no new selector is needed for it.

Columns: the header, the selector, the false target, the popped condition's two limbs, its
producer time and the two time witnesses, and the frame columns.

`s.tgt` is `elseOf[pc] + 1` in **both** shapes: `matchBlocks` sets `elseOf[i] = endOf[i]` when the
`if` has no `else`, so "no else" is exactly `elseOf = endOf`.  The AIR therefore does not need to
distinguish the two shapes; only the checker's label bookkeeping does. -/
namespace IfC
def kSb : Nat := 12
def kCid : Nat := 13
def fIf : Nat := 5
def tgt : Nat := 6
def c : Nat := 7      -- 7, 8 (the popped condition, 4 x 16-bit limbs with 2 used)
def tc : Nat := 9
def hc : Nat := 10
def inv : Nat := 11
def cols : List String := headerCols ++ ["f_if", "tgt", "c0", "c1", "tc", "hc", "inv"] ++ frameCols
/-- The `if` opcode, after the CTRL block `0x101..0x105`. -/
def opIf : Nat := 0x106
def act : Expr := v fIf
/-- Non-zero test: `z · inv` with `z · (1 − nz) = 0`, exactly `Ctrl.nz`. -/
def nz : Expr := (v c + v (c + 1)) * v inv
def pc1 : Expr := v cPc + 1
/-- **The polarity.**  `if` continues at `pc + 1` when the condition is non-zero and jumps to
`tgt` when it is zero. -/
def pcNext : Expr := nz * pc1 + (1 - nz) * v tgt
def constraints : List Expr :=
  [bool (v fIf),
   (v c + v (c + 1)) * (1 - nz)]
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) act,
   stateOut pcNext (v cTs + 1) (v cS + v cFee) 0 (v kSb) (v kCid) act,
   fetch (v cPc) (Expr.c opIf) (v cH) (v cFee) [v tgt, 0, 0, 0] act,
   stkRecv (v kSb + v cH - 1) 0 [v c, v (c + 1), 0, 0] (v tc) act] ++
  timeChk (v cTs) (v tc) (v hc) act
def table : Table := ⟨"IF", cols, constraints, inters⟩
end IfC

end Chips

open Chips in
/-- The AIR set `wasm-base-v3` for a function with `nloc` locals in a module with `ngl` globals (the
code size only sets the CODE height). -/
def wasmBaseAir (nloc ngl : Nat) : Air where
  tables := [Boundary.table nloc ngl, Add.table, Bit.table, Mul.table, Shift.table, Cmp.table,
    Const.table, Stack.table, Ctrl.table, Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table,
    Range16.table, Byte.table, Code.table, Drain.table, MemInit.table, Data.table, Func.table]
  numPub := Boundary.pubLoc + nloc + 5 * ngl + 2

end WasmBase
