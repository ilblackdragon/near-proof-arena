import M5T1.Msg

/-!
# M5T1.Rx — `RX`: one row per incoming receipt (the runtime part of the receipt step)

The row is `NearSpecV3.Successor.StorageExecution.processWithInstant` for an action receipt with one
`FunctionCall` action (`applyActionReceipt` → `actionLoop` → `functionCallRecordedF` → the VM call
→ merge → storage stake → refunds → burnt amounts → receipt ids → outcome → totals), with the VM
call answered on `VMRES`/`FB` by the Wasm side. Every number is little-endian bytes (each
`RNG`-checked) and every `u64`/`u128` operation is a carry chain (`lin`): limb `k` satisfies
`terms_k + carry_{k−1} = r_k + 256·carry_k`, with the top carry `0` (the spec's `add64`/`add128`
overflow checks, which make the checker reject) or a flag (comparisons).

| group | spec |
|---|---|
| `nb`, `fcx` | `actExec recv (fcall m a _ _) = fcBase.exec + fcByte.exec·(|m| + |a|)` (`D2/Fees.lean`); `execCompute` equal |
| `gb`, `gu`, `cu` | `res.gasBurnt = nar.exec + (ex + burnt)`, `gasUsed = nar.exec + (ex + used + 0)`, compute (merge `add64`) |
| `dvu` | merge: `ar.gasBurnt ≤ ar.gasUsed` |
| `ad`, `iam`, `ich` | `acct.amount + deposit < 2^128`; V1 account (`amount ≠ u128::MAX`); local contract (code hash `≠ 0`) |
| `req`, `ak`, `s1`, `s2` | `storageStakeOk acct' acct'.amount = some true` |
| `burn`, `dmn` | `burn = min purchase env.gasPrice` |
| `sA`, `sB` | `r.pred ≠ "system"` |
| `pexec`, `tot`, `gross`, `unu`, `gpb`, `sur`, `bc`, `rf` | `D2.refunds`: `gasRefund = purchase·(tot − gasUsed) + (purchase − burn)·gasBurnt − 0`, `> 0` |
| `tb` | `tokens_burnt = burn·gasBurnt` |
| `fc3`, `q10`, `r10`, `rew`, `amt2`, `txb` | receiver reward `burn·⌊3·gasFC/10⌋`, new amount, `tx_burnt` share |
| `*out` | the receipt state's totals (`processWithTotals`, `rs.txBurnt`, `rs.subsidized`, `rs.wasmGas`) |
-/

namespace M5T1

open ZkFormal.Air

namespace Rx

/-! ## Public values -/

def PL : Layout :=
  [("egp", 16), ("hgt", 8), ("tst", 8), ("eph", 8), ("rv", 32), ("glim", 8), ("seg", 1),
   ("tIn", 1), ("tOut", 1),
   ("gin", 8), ("cin", 8), ("tbin", 16), ("oth", 16), ("sbin", 16), ("wgin", 16), ("noin", 1), ("ngin", 1),
   ("gout", 8), ("cout", 8), ("tbout", 16), ("othout", 16), ("sbout", 16), ("wgout", 16), ("noout", 1),
   ("ngout", 1)]

def pub (s : String) (j : Nat := 0) : Expr := .pub (PL.off s + j)
def NUM_PUB : Nat := PL.width

/-! ## Columns -/

/-- byte groups (each byte `RNG`-checked) -/
def byteGroups : Layout :=
  [-- env (= public values)
   ("egp", 16), ("hgt", 8), ("tst", 8), ("eph", 8), ("rv", 32), ("glim", 8),
   -- receipt state in / out
   ("gin", 8), ("cin", 8), ("tbin", 16), ("oth", 16), ("sbin", 16), ("wgin", 16),
   ("gout", 8), ("cout", 8), ("tbout", 16), ("sbout", 16), ("wgout", 16),
   -- inputs: receipt fields, account, VM answer, digests
   ("gp", 16), ("gas", 8), ("dep", 16), ("amt", 16), ("lck", 16), ("ch", 32),
   ("vb", 8), ("vu", 8), ("vc", 8), ("vbal", 16), ("vus", 8), ("vsub", 16),
   ("rrh", 32), ("leaf", 32), ("pb", 6),
   -- computed
   ("nb", 3), ("fcx", 8), ("gb", 8), ("gu", 8), ("cu", 8), ("dvu", 8), ("ad", 16), ("req", 16),
   ("ak", 16), ("s1", 16), ("s2", 8), ("dmn", 16), ("burn", 16), ("pexec", 8), ("tot", 8),
   ("gross", 8), ("unu", 16), ("gpb", 16), ("sur", 16), ("bc", 16), ("rf", 16), ("tb", 16),
   ("fc3", 8), ("q10", 8), ("r10", 1), ("rew", 16), ("amt2", 16), ("txb", 16), ("dgl", 8),
   ("e1", 2), ("e2", 3), ("gte", 3), ("lmb", 2), ("lab", 3),
   -- carries of the products (2 bytes per limb) and of the 3-term sums (1 byte per limb)
   ("cfx", 14), ("crq", 30), ("cun", 46), ("csu", 46), ("cbc", 42), ("ctb", 46), ("crw", 46),
   ("cgb", 7), ("cgu", 7), ("ccu", 7), ("cf3", 7), ("cq", 7)]

/-- bit groups (carries of two-term sums, flags) -/
def bitGroups : Layout :=
  [("act", 1), ("la1", 1), ("cdv", 7), ("cad", 15), ("cak", 15), ("cs1", 15), ("b1", 1), ("cs2", 7), ("b2", 1),
   ("cmn", 15), ("bm", 1), ("sA", 1), ("sB", 1), ("cpx", 7), ("cto", 7), ("cgr", 7), ("cgp", 15),
   ("crf", 15), ("cam", 15), ("ctx", 15), ("ctbo", 15), ("csbo", 15), ("cwg", 15), ("cgo", 7),
   ("cco", 7), ("cgl", 7), ("lg", 4)]

/-- other columns (field elements) -/
def otherGroups : Layout :=
  [("qf", 1), ("seg", 1), ("lm", 1), ("la", 1), ("lp", 1), ("kl", 1), ("ts0", 1), ("tse", 1),
   ("noin", 1), ("ngin", 1), ("iam", 1), ("ich", 1), ("iA", 1), ("iB", 1), ("irf", 1), ("igs", 1)]

def L : Layout := otherGroups ++ bitGroups ++ byteGroups
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def n (s : String) (j : Nat := 0) : Expr := T.n s j
def bv (s : String) : Nat → Expr := fun k => c s k
def zero : Nat → Expr := fun _ => K 0
def kb (v : Nat) : Nat → Expr := fun k => K (v / 256 ^ k % 256)

/-! ## Gadgets -/

/-- carry chain over `N` limbs: `terms k + cy (k−1) = r k + 256·cy k`, `cy (N−1) = top` -/
def lin (N : Nat) (terms r cy : Nat → Expr) (top : Expr) : List Expr :=
  (List.range N).map fun k =>
    terms k + (if k = 0 then K 0 else cy (k - 1)) - r k - K 256 * (if k + 1 = N then top else cy k)

/-- `Σ_{i<na, j<nb, i+j=k} a i · b j` -/
def mulT (a : Nat → Expr) (na : Nat) (b : Nat → Expr) (nb : Nat) (k : Nat) : Expr :=
  sumE ((List.range na).filterMap fun i =>
    if i ≤ k ∧ k - i < nb then some (a i * b (k - i)) else none)

def cy2 (s : String) : Nat → Expr := fun k => c s (2 * k) + K 256 * c s (2 * k + 1)
def bytes (n : Nat) (a : Nat → Expr) : Nat → Expr := fun k => if k < n then a k else K 0
def add2 (a b : Nat → Expr) : Nat → Expr := fun k => a k + b k
def add3 (a b d : Nat → Expr) : Nat → Expr := fun k => a k + b k + d k

/-- `a·b` (`na`, `nb` bytes) into `nr` result bytes: the product's bytes `nr ≤ k < na + nb` are zero
(the product is `< 256^nr`); `na + nb − 1` two-byte carries -/
def mulG (a : Nat → Expr) (na : Nat) (b : Nat → Expr) (nb : Nat) (r : String) (nr : Nat)
    (cy : String) : List Expr :=
  lin (na + nb) (mulT a na b nb) (bytes nr (bv r)) (cy2 cy) (K 0)

def nonzero (a : Nat → Expr) (n : Nat) (inv : String) : Expr :=
  sumE ((List.range n).map a) * c inv - 1

/-! ## Constraints -/

/-- The receipt step's arithmetic (every constraint is gated by `act` in `constraints`). -/
def arith : List Expr :=
  let A := c "act"
  -- |method| + |args| (each below 2^16 / 2^24), fcBase/fcByte exec gas
  [c "lm" - leVal (bv "lmb") 2, c "la" - leVal (bv "lab") 3,
   leVal (bv "nb") 3 - c "lm" - c "la"] ++
  lin 8 (fun k => kb FC_BASE_EXEC k + mulT (bv "nb") 3 (kb FC_BYTE_EXEC) 3 k) (bv "fcx") (cy2 "cfx") 0 ++
  -- merge: gas burnt / used / compute
  lin 8 (add3 (kb NAR_EXEC) (bv "fcx") (bv "vb")) (bv "gb") (bv "cgb") 0 ++
  lin 8 (add3 (kb NAR_EXEC) (bv "fcx") (bv "vu")) (bv "gu") (bv "cgu") 0 ++
  lin 8 (add3 (kb NAR_EXEC) (bv "fcx") (bv "vc")) (bv "cu") (bv "ccu") 0 ++
  lin 8 (add2 (bv "vb") (bv "dvu")) (bv "vu") (bv "cdv") 0 ++
  -- functionCallRecorded: deposit overflow, V1 account with a local contract
  lin 16 (add2 (bv "amt") (bv "dep")) (bv "ad") (bv "cad") 0 ++
  [nonzero (fun k => K 255 - c "amt" k) 16 "iam", nonzero (bv "ch") 32 "ich"] ++
  -- storage stake of the new account (amount = VM balance, usage = VM storage usage)
  mulG (bv "vus") 8 (kb STORAGE_PER_BYTE) 8 "req" 16 "crq" ++
  lin 16 (add2 (bv "vbal") (bv "lck")) (bv "ak") (bv "cak") 0 ++
  lin 16 (add2 (bv "req") (bv "s1")) (bv "ak") (bv "cs1") (c "b1") ++
  lin 8 (add2 (bv "vus") (bv "s2")) (kb ZERO_BALANCE_LIMIT) (bv "cs2") (c "b2") ++
  [c "b1" * c "b2"] ++
  -- burn = min purchase env.gasPrice
  lin 16 (add2 (bv "egp") (bv "dmn")) (bv "gp") (bv "cmn") (c "bm") ++
  ((List.range 16).map fun k => c "burn" k - c "bm" * c "gp" k - (1 - c "bm") * c "egp" k) ++
  -- refunds
  lin 8 (add2 (bv "fcx") (kb NAR_EXEC)) (bv "pexec") (bv "cpx") 0 ++
  lin 8 (add2 (bv "gas") (bv "pexec")) (bv "tot") (bv "cto") 0 ++
  lin 8 (add2 (bv "gu") (bv "gross")) (bv "tot") (bv "cgr") 0 ++
  mulG (bv "gp") 16 (bv "gross") 8 "unu" 16 "cun" ++
  lin 16 (add2 (bv "burn") (bv "gpb")) (bv "gp") (bv "cgp") 0 ++
  mulG (bv "gpb") 16 (bv "gb") 8 "sur" 16 "csu" ++
  mulG (bv "burn") 16 (kb CREATE_ACCOUNT_EXEC) 6 "bc" 16 "cbc" ++
  lin 16 (add2 (bv "unu") (bv "sur")) (bv "rf") (bv "crf") 0 ++
  [nonzero (bv "rf") 16 "irf"] ++
  -- tokens burnt, receiver reward, new amount, tx burnt
  mulG (bv "burn") 16 (bv "gb") 8 "tb" 16 "ctb" ++
  lin 8 (fun k => K 3 * c "vb" k) (bv "fc3") (bv "cf3") 0 ++
  lin 8 (fun k => K 10 * c "q10" k + (if k = 0 then c "r10" else K 0)) (bv "fc3") (bv "cq") 0 ++
  mulG (bv "burn") 16 (bv "q10") 8 "rew" 16 "crw" ++
  lin 16 (add2 (bv "vbal") (bv "rew")) (bv "amt2") (bv "cam") 0 ++
  lin 16 (add2 (bv "rew") (bv "txb")) (bv "tb") (bv "ctx") 0 ++
  -- totals
  lin 16 (add2 (bv "tbin") (bv "txb")) (bv "tbout") (bv "ctbo") 0 ++
  lin 16 (add2 (bv "sbin") (bv "vsub")) (bv "sbout") (bv "csbo") 0 ++
  lin 16 (add2 (bv "wgin") (bytes 8 (bv "vb"))) (bv "wgout") (bv "cwg") 0 ++
  lin 8 (add2 (bv "gin") (bv "gb")) (bv "gout") (bv "cgo") 0 ++
  lin 8 (add2 (bv "cin") (bv "cu")) (bv "cout") (bv "cco") 0 ++
  -- compute < gas limit (else the receipt is delayed), gas ≠ 0, method / args size limits
  lin 8 (fun k => c "cin" k + c "dgl" k + (if k = 0 then K 1 else K 0)) (bv "glim") (bv "cgl") 0 ++
  [nonzero (bv "gas") 8 "igs",
   c "lm" + c "e1" 0 + K 256 * c "e1" 1 - K MAX_METHOD_NAME,
   c "la" + c "e2" 0 + K 256 * c "e2" 1 + K 65536 * c "e2" 2 - K MAX_ARGS,
   -- the call's clock: read at ts0, call (ts0 + 1, tse], write at tse + 1
   c "tse" - c "ts0" - 2 - (c "gte" 0 + K 256 * c "gte" 1 + K 65536 * c "gte" 2)] ++
  -- logs: lg is a prefix of ones
  ((List.range (MAX_LOGS - 1)).map fun i => c "lg" (i + 1) * (1 - c "lg" i)) ++
  -- env and segment = public values (every active row)
  (([("egp", 16), ("hgt", 8), ("tst", 8), ("eph", 8), ("rv", 32), ("glim", 8)] : Layout).flatMap
     fun (g, w) => (List.range w).map fun k => c g k - pub g k) ++
  [c "seg" - pub "seg"]

/-- First row, chaining between receipts, last active row. -/
def chain : List Expr :=
  let A := c "act"
  -- the predecessor is not `system` (`sA`: its length is not 6; `sB`: one of its 6 bytes differs)
  [A * (c "sA" + c "sB" - 1), (1 - A) * c "sA", (1 - A) * c "sB",
   c "sA" * ((c "lp" - 6) * c "iA" - 1),
   c "sB" * (c "lp" - 6),
   c "sB" * (sumE ((List.range 6).map fun k =>
      (c "pb" k - K (systemId.getD k 0)) * (c "pb" k - K (systemId.getD k 0))) * c "iB" - 1)] ++
  -- logs: inactive rows demand none
  ((List.range MAX_LOGS).map fun i => (1 - A) * c "lg" i) ++
  -- `la1`: the last active row
  [c "la1" - A * (1 - .isTransition * n "act")] ++
  -- first row: receipt 1, the receipt state in = public
  [.isFirst * (A - 1), .isFirst * (c "qf" - 1), .isFirst * (c "ts0" - pub "tIn"),
   .isFirst * (c "noin" - pub "noin"), .isFirst * (c "ngin" - pub "ngin")] ++
  (([("gin", 8), ("cin", 8), ("tbin", 16), ("oth", 16), ("sbin", 16), ("wgin", 16)] : Layout).flatMap
     fun (g, w) => (List.range w).map fun k => .isFirst * (c g k - pub g k)) ++
  -- chaining: active rows are a prefix; next.in = out
  [.isTransition * (1 - A) * n "act",
   .isTransition * n "act" * (n "qf" - c "qf" - 1),
   .isTransition * n "act" * (n "ts0" - c "tse" - 2),
   .isTransition * n "act" * (n "noin" - c "noin" - 1),
   .isTransition * n "act" * (n "ngin" - c "ngin" - 1)] ++
  (([("gin", "gout", 8), ("cin", "cout", 8), ("tbin", "tbout", 16), ("oth", "oth", 16),
     ("sbin", "sbout", 16), ("wgin", "wgout", 16)] : List (String × String × Nat)).flatMap
     fun (g, o, w) => (List.range w).map fun k => .isTransition * n "act" * (n g k - c o k)) ++
  -- last active row: out = public
  (let lastA := c "la1"
   [lastA * (c "tse" + 2 - pub "tOut"), lastA * (c "noin" + 1 - pub "noout"),
    lastA * (c "ngin" + 1 - pub "ngout")] ++
   (([("gout", "gout", 8), ("cout", "cout", 8), ("tbout", "tbout", 16), ("oth", "othout", 16),
      ("sbout", "sbout", 16), ("wgout", "wgout", 16)] : List (String × String × Nat)).flatMap
     fun (g, p, w) => (List.range w).map fun k => lastA * (c g k - pub p k)))

def constraints : List Expr :=
  let A := c "act"
  let nLogs := sumE ((List.range MAX_LOGS).map fun i => c "lg" i)
  -- booleanity of the bit groups
  ((bitGroups.flatMap fun (g, w) => (List.range w).map fun i => bool (c g i))) ++
  [(1 - A) * c "qf"] ++
  -- the arithmetic of the receipt step, on active rows
  (arith.map fun e => A * e) ++
  chain


/-! ## Interactions -/

def sidOf (fid : Nat) : Expr := K 128 * c "qf" + K fid
def mOf (mt : Expr) : Expr := K 128 * c "qf" + K 96 + mt
def fbRecv (fid : Nat) (g : String) (w : Nat) (m : Expr) : List Interaction :=
  (List.range w).map fun k => rcv B_FB m [sidOf fid, K k, c g k]
def fbSend (fid : Nat) (g : String) (w : Nat) (bits : List Expr) : List Interaction :=
  (List.range w).map fun k => sndBits B_FB bits [sidOf fid, K k, c g k]
def tsw : Expr := c "tse" + 1

def interactions : List Interaction :=
  let A := c "act"
  let nLogs := sumE ((List.range MAX_LOGS).map fun i => c "lg" i)
  let lastA := c "la1"
  -- range checks
  (byteGroups.flatMap fun (g, w) => (List.range w).map fun k => rcv B_RNG A [c g k]) ++
  [rcv B_RNG A [c "r10" 0 + K 246]] ++
  -- inputs
  fbRecv F_GPRICE "gp" 16 A ++ fbRecv F_GAS "gas" 8 A ++ fbRecv F_DEPOSIT "dep" 16 A ++
  fbRecv F_AMT "amt" 16 A ++ fbRecv F_LOCKED "lck" 16 A ++ fbRecv F_CODEH "ch" 32 A ++
  fbRecv F_VBURNT "vb" 8 A ++ fbRecv F_VUSED "vu" 8 A ++ fbRecv F_VCOMP "vc" 8 A ++
  fbRecv F_VBAL "vbal" 16 A ++ fbRecv F_VUSAGE "vus" 8 A ++ fbRecv F_VSUB "vsub" 16 A ++
  fbRecv (F_DIG MT_RREF) "rrh" 32 A ++ fbRecv F_PRED "pb" 6 (c "sB") ++
  ((List.range 32).map fun k =>
    rcv B_FB A [K 128 * c "qf" + K (F_DIG MT_LEAF0) + nLogs, K k, c "leaf" k]) ++
  [rcv B_FLEN A [sidOf F_METHOD, c "lm"], rcv B_FLEN A [sidOf F_ARGS, c "la"],
   rcv B_FLEN A [sidOf F_PRED, c "lp"],
   rcv B_FLEN lastA [K F_COUNT, c "qf"]] ++
  -- computed fields offered to the emitted messages (and the Wasm side's context)
  fbSend F_AMT2 "amt2" 16 [A] ++ fbSend F_REFUND "rf" 16 [A] ++ fbSend F_GB "gb" 8 [A] ++
  fbSend F_TB "tb" 16 [A] ++ fbSend F_HEIGHT "hgt" 8 [A, A] ++ fbSend F_RANDV "rv" 32 [A] ++
  fbSend F_TSTAMP "tst" 8 [A] ++ fbSend F_EPOCHH "eph" 8 [A] ++
  ((List.range 4).map fun k =>
    sndBits B_FB [A] [sidOf F_LEAFN, K k, if k = 0 then K 2 * A + nLogs else K 0]) ++
  -- the messages this receipt demands (the first row: also the receipt list), and the lengths
  [snd B_MBEG (.isFirst * A) [K (msgId 0 MT_RL), 0, 0],
   snd B_MBEG A [mOf (K MT_KEYR), c "ts0", K PTR_KEY], snd B_MBEG A [mOf (K MT_APRE), c "ts0", K PTR_VAL],
   snd B_MBEG A [mOf (K MT_KEYW), tsw, K PTR_KEY], snd B_MBEG A [mOf (K MT_APOST), tsw, K PTR_VAL],
   snd B_MBEG A [mOf (K MT_AH), 0, 0], snd B_MBEG A [mOf (K MT_SEED), 0, 0],
   snd B_MBEG A [mOf (K MT_RID), 0, 0], snd B_MBEG A [mOf (K MT_RREF), 0, 0],
   snd B_MBEG A [mOf (K MT_PART), 0, 0], snd B_MBEG A [mOf (K MT_LEAF0 + nLogs), 0, 0]] ++
  ((List.range MAX_LOGS).map fun i => snd B_MBEG (c "lg" i) [mOf (K (MT_LOG0 + i)), 0, 0]) ++
  [rcv B_MLEN A [mOf (K MT_KEYR), c "kl"], rcv B_MLEN A [mOf (K MT_APRE), K 72],
   rcv B_MLEN A [mOf (K MT_KEYW), c "kl"], rcv B_MLEN A [mOf (K MT_APOST), K 72],
   -- the receiver account: read before the call, written after it (lane B's read / `SREQ`)
   snd B_SRQ A [c "ts0", c "seg", c "kl", K PTR_KEY],
   rcv B_SRS A [c "ts0", A, K 72, K PTR_VAL],
   snd B_SREQ A [tsw, A, c "seg", c "kl", K PTR_KEY, K 72, K PTR_VAL],
   -- the Wasm call (lane A): request, answer
   snd B_VMCALL A [c "qf", c "ts0" + 1],
   rcv B_VMRES A [c "qf", c "tse", A, nLogs, 0, 0],
   -- outputs: the outcome leaf and the refund receipt's hash
   snd B_OUTC A ([c "qf"] ++ (List.range 32).map fun k => c "leaf" k),
   snd B_OUTR A ([c "qf"] ++ (List.range 32).map fun k => c "rrh" k)]

def table : Table := { width := L.width, constraints, interactions, maxLog := 16 }

end Rx

end M5T1
