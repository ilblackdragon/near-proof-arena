import M5T1.Ids

/-!
# M5T1.Schema — the Borsh layouts the byte engine `MSG` parses and emits

A message type is a list of segments. A segment is one constant byte (`K_C`), a field defined by
the message's bytes (`K_D`, parse) or copied from `FB` (`K_U`, `K_UV`), a u32 length prefix parsed
(`K_LP`) or emitted (`K_LE`), or the receipt count (`K_CNT`). The schema is a constant of the AIR:
every `MSG` row receives its entry on the `SCH` bus from the constant table `SCHT`.

The layouts are the spec's encoders, field by field:

* `RL`: `encodeRcpts` (`D2/Types.lean`) of action receipts with one `FunctionCall` action, no
  output data receivers, no input data ids, signed by an ED25519 key (`Rcpt.encode`,
  `ActionR.encode` with `v2 = false`, `Act.raw` of `fcall`: `2 ‖ borsh method ‖ borsh args ‖ u64 gas
  ‖ u128 deposit`);
* `KEYR`/`KEYW`: `kAccount recv = [0] ++ recv`;
* `APRE`/`APOST`: `Acct.encode` of a V1 account with a local contract (`amount ‖ locked ‖ code
  hash ‖ usage`);
* `AH`: `actionHash rid h 0 = sha256 (rid ‖ u64 h ‖ u64 (2^64 − 1))`; `SEED`: `sha256 (ah ‖
  randomValue)`; `RID`: `receiptIdFrom rid h 0 = sha256 (rid ‖ u64 h ‖ u64 0)`;
* `RREF`: `Rcpt.encode` of the gas-refund receipt of `D2.refunds` (`pred = system`, `recv =
  signer`, an action receipt with one `Transfer`);
* `LOGi`: the log bytes; `PART`: `OutD1.partialEncode` with one receipt id and a
  `SuccessValue` status; `LEAFn`: the preimage of `OutD1.leaf` with `n` logs.
-/

namespace M5T1

structure Seg where
  mt : Nat
  s : Nat
  kind : Nat
  var : Bool := false
  fid : Nat := 0
  fixL : Nat := 1
  cv : Nat := 0
  nextS : Nat := 0
  skipS : Nat := 0
  endOK : Bool := false
  cont : Bool := true
  newR : Bool := false
  /-- an empty variable field after this length prefix ends the message -/
  skipEnd : Bool := false
  deriving Repr, DecidableEq

/-- Message-level flags: hashed (`SHA_BYTES`), sent on `HB`, received on `HBR`. -/
def mflags (mt : Nat) : Bool × Bool × Bool :=
  if mt == MT_KEYR || mt == MT_KEYW || mt == MT_APOST then (false, true, false)
  else if mt == MT_APRE then (false, false, true)
  else if mt == MT_PAD then (false, false, false)
  else (true, false, false)

/-! ## A tiny builder: segments in order, `nextS = s + 1` unless overridden -/

structure SB where
  mt : Nat
  segs : List Seg := []

def SB.n (b : SB) : Nat := b.segs.length

def SB.add (b : SB) (f : Nat → Seg) : SB := { b with segs := b.segs ++ [f b.n] }

/-- constant bytes -/
def SB.consts (b : SB) (vs : List Nat) : SB :=
  vs.foldl (fun b v => b.add fun s => { mt := b.mt, s, kind := K_C, cv := v, nextS := s + 1 }) b

def SB.def (b : SB) (fid L : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_D, fid, fixL := L, nextS := s + 1 }
def SB.defV (b : SB) (fid : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_D, var := true, fid, fixL := 0, nextS := s + 1 }
def SB.use (b : SB) (fid L : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_U, fid, fixL := L, nextS := s + 1 }
def SB.useV (b : SB) (fid : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_U, var := true, fid, fixL := 0, nextS := s + 1 }
def SB.useR (b : SB) (fid : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_UV, var := true, fid, fixL := 0, nextS := s + 1 }
/-- parsed length prefix of the following variable field `fid` (skip it when empty) -/
def SB.lp (b : SB) (fid : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_LP, fid, fixL := 4, nextS := s + 1, skipS := s + 2 }
/-- emitted length prefix of the following variable field `fid` -/
def SB.le (b : SB) (fid : Nat) : SB :=
  b.add fun s => { mt := b.mt, s, kind := K_LE, fid, fixL := 4, nextS := s + 1, skipS := s + 2 }

/-- Mark the last segment: the message may end there; `cont` = it may also continue at `next`. -/
def SB.fin (b : SB) (cont : Bool := false) (next : Nat := 0) : List Seg :=
  match b.segs.reverse with
  | [] => []
  | x :: r => (x :: r).reverse.take r.length ++ [{ x with endOK := true, cont, nextS := next }]

def u32b (v : Nat) : List Nat := leBytes v 4

/-! ## The message types -/

/-- `encodeRcpts` of single-`FunctionCall` action receipts (V1, ED25519 signer). -/
def segRL : List Seg :=
  let b : SB := { mt := MT_RL }
  let b := b.add fun s => { mt := MT_RL, s, kind := K_CNT, fid := F_COUNT, fixL := 4, nextS := s + 1 }
  -- s1: predecessor (opens receipt family `qf + 1`)
  let b := b.add fun s => { mt := MT_RL, s, kind := K_LP, fid := F_PRED, fixL := 4, nextS := s + 1,
                            skipS := s + 2, newR := true }
  let b := b.defV F_PRED
  let b := b.lp F_RECV
  let b := b.defV F_RECV
  let b := b.def F_RID 32
  let b := b.consts [0]                      -- ReceiptEnum::Action (V1)
  let b := b.lp F_SIGNER
  let b := b.defV F_SIGNER
  let b := b.consts [0]                      -- PublicKey::ED25519
  let b := b.def F_PK 32
  let b := b.def F_GPRICE 16
  let b := b.consts (u32b 0 ++ u32b 0 ++ u32b 1 ++ [2])   -- no outputs, no inputs, 1 action: FunctionCall
  let b := b.lp F_METHOD
  let b := b.defV F_METHOD
  let b := b.lp F_ARGS
  let b := b.defV F_ARGS
  let b := b.def F_GAS 8
  let b := b.def F_DEPOSIT 16
  b.fin (cont := true) (next := 1)

def segKey (mt : Nat) : List Seg :=
  let b : SB := { mt }
  let b := b.consts [0]                      -- TrieKey::Account
  let b := b.useR F_RECV
  b.fin

def segAPre : List Seg :=
  let b : SB := { mt := MT_APRE }
  ((((b.def F_AMT 16).def F_LOCKED 16).def F_CODEH 32).def F_USAGE 8).fin

def segAPost : List Seg :=
  let b : SB := { mt := MT_APOST }
  ((((b.use F_AMT2 16).use F_LOCKED 16).use F_CODEH 32).use F_VUSAGE 8).fin

def segAH : List Seg :=
  let b : SB := { mt := MT_AH }
  (((b.use F_RID 32).use F_HEIGHT 8).consts (leBytes (2 ^ 64 - 1) 8)).fin

def segSeed : List Seg :=
  let b : SB := { mt := MT_SEED }
  ((b.use (F_DIG MT_AH) 32).use F_RANDV 32).fin

def segRid : List Seg :=
  let b : SB := { mt := MT_RID }
  (((b.use F_RID 32).use F_HEIGHT 8).consts (leBytes 0 8)).fin

/-- "system" -/
def systemId : List Nat := [115, 121, 115, 116, 101, 109]

def segRRef : List Seg :=
  let b : SB := { mt := MT_RREF }
  let b := b.consts (u32b 6 ++ systemId)
  let b := (b.le F_SIGNER).useV F_SIGNER
  let b := b.use (F_DIG MT_RID) 32
  let b := b.consts [0]
  let b := (b.le F_SIGNER).useV F_SIGNER
  let b := b.consts [0]
  let b := b.use F_PK 32
  let b := b.consts (leBytes 0 16 ++ u32b 0 ++ u32b 0 ++ u32b 1 ++ [3])
  let b := b.use F_REFUND 16
  b.fin

def segLog (i : Nat) : List Seg :=
  let b : SB := { mt := MT_LOG0 + i }
  (b.useR (F_LOG0 + i)).fin

def segPart : List Seg :=
  let b : SB := { mt := MT_PART }
  let b := b.consts (u32b 1)
  let b := b.use (F_DIG MT_RID) 32
  let b := b.use F_GB 8
  let b := b.use F_TB 16
  let b := (b.le F_RECV).useV F_RECV
  let b := b.consts [2]
  -- `SuccessValue`: u32 length and the return bytes (an empty value ends the message)
  let b := b.add fun s => { mt := MT_PART, s, kind := K_LE, fid := F_RET, fixL := 4, nextS := s + 1,
                            skipS := s + 2, skipEnd := true }
  let b := b.useV F_RET
  b.fin

def segLeaf (n : Nat) : List Seg :=
  let b : SB := { mt := MT_LEAF0 + n }
  let b := b.use F_LEAFN 4
  let b := b.use F_RID 32
  let b := b.use (F_DIG MT_PART) 32
  let b := (List.range n).foldl (fun b i => b.use (F_DIG (MT_LOG0 + i)) 32) b
  b.fin

def segPad : List Seg := [{ mt := MT_PAD, s := 0, kind := K_PAD, fixL := 0, cont := false }]

def schema : List Seg :=
  segRL ++ segKey MT_KEYR ++ segAPre ++ segKey MT_KEYW ++ segAPost ++ segAH ++ segSeed ++ segRid ++
  segRRef ++ (List.range MAX_LOGS).flatMap segLog ++ segPart ++
  (List.range (MAX_LOGS + 1)).flatMap segLeaf ++ segPad

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- The `SCH` message of a segment: `[mt, s, act, kC, kD, kU, kUV, kLP, kLE, kCNT, var, fid, fixL,
cv, nextS, skipS, endOK, cont, newR, skipEnd, hsh, hb, hbr]`. -/
def Seg.msg (g : Seg) : List Nat :=
  let (hsh, hb, hbr) := mflags g.mt
  [g.mt, g.s, b2n (g.kind != K_PAD), b2n (g.kind == K_C), b2n (g.kind == K_D), b2n (g.kind == K_U),
   b2n (g.kind == K_UV), b2n (g.kind == K_LP), b2n (g.kind == K_LE), b2n (g.kind == K_CNT),
   b2n g.var, g.fid, g.fixL, g.cv, g.nextS, g.skipS, b2n g.endOK, b2n g.cont, b2n g.newR,
   b2n g.skipEnd, b2n hsh, b2n hb, b2n hbr]

/-- The names of the `SCH` message fields (= the `MSG` columns the entry pins, in order). -/
def schFields : List String :=
  ["mt", "s", "act", "kC", "kD", "kU", "kUV", "kLP", "kLE", "kCNT", "var", "fid", "fixL", "cv",
   "nextS", "skipS", "endOK", "cont", "newR", "skipEnd", "hsh", "hb", "hbr"]

end M5T1
