import WasmBase.Main.HostIfTape
import WasmBase.SegAirJ

/-!
# WasmBase.Main.HostJoin — what lane B's rows must provide in the joined segment (E2E A-T1 item 5)

In the joined segment AIR `wasmBaseSegAirMPJ` (`WasmBase/SegAirJ.lean`) the in-trace oracle `HOSTO`
cannot answer `storage_write` (58) / `storage_remove` (60) (`hostOJ_no_storage`), and `HOSTB` does not
consume those calls' request bytes (`hostBJ_reqRecv_stg`).  So for every such call the HOSTQ 208
request, the HOSTR 209 response and the request bytes on HOSTB 210 are balanced by lane B's rows
(`StateM5a.StwH`: HOSTQ receive / HOSTR send; `StateM5a.StbH`: HOSTB receive).  `HOSTB` still
**sends** the register-fill bytes (`reg = 1`, interaction 4, received by `REG`) of the evicted
value, so their values are a lane-B obligation too.

This file states, in `ProducerObl`'s vocabulary, what that means for the M6.4 producer contract:

* `ProducerOblOn S` — `ProducerObl` restricted to the HOST rows satisfying `S`;
  `producerObl_split` / `producerOblOn_of`: `ProducerObl` is exactly the conjunction of the two
  restrictions to `StgCall` and `¬ StgCall` (so nothing is lost by the split);
* **`StorageJoinObl`** — lane B's part: `ProducerOblOn StgCall` (HOSTQ/HOSTR answers, the arm
  agreement, registers, host side) plus `hb` (the request bytes it consumes are exactly the key /
  value buffers of the request) and `regFill` (the register-fill bytes are the evicted value);
* **`producerObl_join`** — `ProducerOblOn (¬ StgCall)` (the oracle's / other producers' part, as
  before) and `StorageJoinObl` give `ProducerObl`, which feeds `HostIf` as before.

Stated, not discharged (the lane-B side).  Why an honest run satisfies each clause: see the
docstrings.
-/

namespace WasmBase
namespace HostIf

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide HostAns

/-! ## Storage calls and their buffers -/

/-- The storage ids answered by lane B in the joined segment. -/
def stgIds : List Nat := [58, 60]

/-- HOST row `r` is a storage call answered by lane B (`storage_write` / `storage_remove`). -/
def StgCall (tr : Trace) (r : Nat) : Prop := hostHid tr r = 58 ∨ hostHid tr r = 60

instance (tr : Trace) (r : Nat) : Decidable (StgCall tr r) := by unfold StgCall; infer_instance

/-- A byte buffer `(len, ptr)` of a host call as linear-memory addresses; `ptr = u64::MAX` reads a
register instead (`memOrRegH`), so no memory byte. -/
def bufAddrs (len ptr : Nat) : List Nat :=
  if ptr = 2 ^ 64 - 1 then [] else (List.range len).map (ptr + ·)

/-- The request buffers of a storage call: the key `(a0, a1)`, and for `storage_write` the value
`(a2, a3)` (`StateM5a.StwH.qMsg`: `klen, kptr, vlen, vptr, rid` / `klen, kptr, rid`). -/
def stgAddrs (hid : Nat) (args : List Nat) : List Nat :=
  bufAddrs (args.getD 0 0) (args.getD 1 0) ++
    (if hid = 58 then bufAddrs (args.getD 2 0) (args.getD 3 0) else [])

/-- The register the evicted value goes to: `a4` for `storage_write`, `a2` for `storage_remove`. -/
def stgRid (hid : Nat) (args : List Nat) : Nat := if hid = 58 then args.getD 4 0 else args.getD 2 0

/-- The request bytes (`dir = 0`, `reg = 0`) of HOST row `r` as `(addr, byte)`, `addr = ptr + pos`
(the 4th field of their bus-210 message, `HostBK.msgM`). -/
def hostReqBytes (tr : Trace) (pub : List F) (r : Nat) : List (Nat × Nat) :=
  ((hostBytes tr pub r).filter fun x => x.1 = 0 ∧ x.2.1 = 0).map fun x => (x.2.2.1, x.2.2.2)

/-- The register-fill bytes (`dir = 1`, `reg = 1`) of HOST row `r` as `(pos, byte)` (the message
`HostBK.msgW` that `REG` receives). -/
def hostRegFill (tr : Trace) (pub : List F) (r : Nat) : List (Nat × Nat) :=
  (hostbOf tr pub r).filterMap fun r' =>
    if rowNat tr 25 r' HostB.act = 1 ∧ rowNat tr 25 r' HostB.dir = 1 ∧ rowNat tr 25 r' HostB.reg = 1 then
      some (rowNat tr 25 r' HostB.pos, rowNat tr 25 r' HostB.bv)
    else none

/-- The bytes of register `rid` in a register file, as `(pos, byte)` (empty if absent). -/
def regBytesOf (R : Array (Nat × ByteArray)) (rid : Nat) : List (Nat × Nat) :=
  match R.find? (·.1 = rid) with
  | some e => (List.range e.2.size).map fun i => (i, (e.2[i]!).toNat)
  | none => []

/-- The answer `A` gives at HOST row `r` (the term every `ProducerObl` clause uses). -/
def ansAt (tr : Trace) (pub : List F) (hts : List Nat) (σc : Nat → St) (A : HostAnsF)
    (memSz : Nat → Nat) (r : Nat) : HAns :=
  A.ans (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
    (hostReadMem tr pub r) (memSz r)

/-! ## `ProducerObl` restricted to a set of HOST rows -/

/-- **`ProducerObl` on the HOST rows satisfying `S`** (every per-row clause guarded by `S r`). -/
structure ProducerOblOn (S : Nat → Prop) (X : Ctx) (tr : Trace) (pub : List F) (hts : List Nat)
    (σc : Nat → St) (A : HostAnsF) (memSz : Nat → Nat) : Prop where
  spec : ∀ r, HAct tr pub r → S r → ∀ s : St,
    sideR s = σc (rank hts (rowNat tr 22 r 1)) →
    (∀ i, i < (hostArgs tr r).length → vNum (s.stack[s.stack.size - (hostArgs tr r).length + i]?.getD (.i32 0)) =
      (hostArgs tr r).getD i 0) →
    (∀ x ∈ hostBytes tr pub r, x.1 = 0 → x.2.1 = 0 → (readByte s x.2.2.1).toNat = x.2.2.2) →
    memBytes s = memSz r →
    (hostCall (hidName (hostHid tr r))).get!.run s =
      runOf { s with stack := s.stack.extract 0 (s.stack.size - (hostArgs tr r).length) }
        (A.ans (hidName (hostHid tr r)) s (hostArgs tr r) (hostReadMem tr pub r) (memSz r))
  st : ∀ r, HAct tr pub r → S r → (hostSt tr r = 0 ↔ (ansAt tr pub hts σc A memSz r).err = none)
  word : ∀ r, HAct tr pub r → S r → hostRes tr r = (ansAt tr pub hts σc A memSz r).res
  gas : ∀ r, HAct tr pub r → S r → hostSt tr r = 0 →
    hostGAfter tr r = (ansAt tr pub hts σc A memSz r).gas.remaining
  resp : ∀ r, HAct tr pub r → S r → hostRespBytes tr pub r = wrBytes (ansAt tr pub hts σc A memSz r)
  regs : ∀ r, HAct tr pub r → S r →
    (σc (rank hts (rowNat tr 22 r 1) + 1)).registers = (ansAt tr pub hts σc A memSz r).regs ∧
    RegStep (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (σc (rank hts (rowNat tr 22 r 1))).registers (σc (rank hts (rowNat tr 22 r 1) + 1)).registers
  next : ∀ r, HAct tr pub r → S r →
    σc (rank hts (rowNat tr 22 r 1) + 1) =
      A.side (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
        (hostReadMem tr pub r) (memSz r)
  cap : ∀ j, ∀ e ∈ (σc j).registers.toList, e.2.size < Register.cap

variable {X : Ctx} {tr : Trace} {pub : List F} {hts : List Nat} {σc : Nat → St} {A : HostAnsF}
  {memSz : Nat → Nat}

/-- A full `ProducerObl` restricts to any set of rows. -/
theorem producerOblOn_of (h : ProducerObl X tr pub hts σc A memSz) (S : Nat → Prop) :
    ProducerOblOn S X tr pub hts σc A memSz :=
  ⟨fun r hr _ => h.spec r hr, fun r hr _ => h.st r hr, fun r hr _ => h.word r hr,
   fun r hr _ => h.gas r hr, fun r hr _ => h.resp r hr, fun r hr _ => h.regs r hr,
   fun r hr _ => h.next r hr, h.cap⟩

/-- **The split is lossless**: the restrictions to `S` and to `¬ S` give `ProducerObl`. -/
theorem producerObl_split (S : Nat → Prop) (h1 : ProducerOblOn S X tr pub hts σc A memSz)
    (h2 : ProducerOblOn (fun r => ¬ S r) X tr pub hts σc A memSz) :
    ProducerObl X tr pub hts σc A memSz := by
  classical
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_, h1.cap⟩ <;>
  by_cases hs : S r
  all_goals first
    | exact h1.spec r hr hs | exact h2.spec r hr hs
    | exact h1.st r hr hs | exact h2.st r hr hs
    | exact h1.word r hr hs | exact h2.word r hr hs
    | exact h1.gas r hr hs | exact h2.gas r hr hs
    | exact h1.resp r hr hs | exact h2.resp r hr hs
    | exact h1.regs r hr hs | exact h2.regs r hr hs
    | exact h1.next r hr hs | exact h2.next r hr hs

/-! ## Lane B's obligation in the joined segment -/

/-- **`StorageJoinObl`: what lane B's state rows must provide** for the joined segment, per active
HOST row `r` that is a storage call (`hid ∈ {58, 60}`), with `a := ansAt … r` the answer of the arm
(`A.ans "storage_write"` / `"storage_remove"` at the host side `σc j`, the request arguments and the
bytes `hostReadMem` on `HOSTB`):

* `ans` — `ProducerObl` at the storage rows.  Bus-wise: lane B's `STWH` row receives the HOSTQ
  request `[ts, hid, S, np, a0lo, a0hi, …]` (so `klen, kptr, vlen, vptr, rid` are the HOST row's
  arguments) and sends the HOSTR answer `[ts, st, rLo, rHi, gLo, gHi, ar, 0]` that the HOST row
  consumes; `st` / `word` / `gas` say that answer is `a` (status, the `1`/`0` eviction word,
  `g_after`); `spec` that `a` is the arm's run; `resp` that no memory byte is written (`wrBytes a =
  []` for both arms); `regs` / `next` the register file and the host side after (trie / real,
  storageUsage, gas counters);
* `hb` — **HB consumption**: the request bytes of the call (the `HOSTB` rows with `dir = 0`,
  `reg = 0`, whose bus-210 message `[ts, wire, 0, ptr + pos, byte]` only lane B's `STBH` rows
  receive, `hostBJ_reqRecv_stg`) sit exactly at the key buffer `[kptr, kptr + klen)` and, for
  `storage_write`, the value buffer `[vptr, vptr + vlen)` (as a multiset of addresses).  Lane B's
  `STBH` receives `HOSTB [ts, hid, 0, base + j, b]` for `j < len` with `(base, len)` from its `STWH`
  row's request, so a byte at another address, a missing one, or a duplicate would be unbalanced;
* `regFill` — **register fill of the evicted value**: on a continuing call (`a.err = none`) the
  `reg = 1` bytes `HOSTB` sends to `REG` are the bytes of register `rid` in `a.regs` if the call
  evicted a value (`a.res = [1]`, the arm's `regSetH rid old`), and there are none otherwise.

Honest runs: the HOSTQ/HOSTR pair is lane B's `STWH` row for the call, whose answer is the spec arm's
(`spec`/`st`/`word`/`gas`/`regs`/`next` are the M6.4 clauses lane B already owes for these ids, now on
lane A's buses instead of HOSTO); the honest tracer emits one `HOSTB` group per buffer read from
memory (`memOrRegH` with `ptr ≠ u64::MAX`), `klen` resp. `vlen` bytes at `ptr + pos`, so `hb` holds
with equality (in group order); on eviction the tracer emits `|old|` `reg = 1` rows with
`pos = 0 … |old| − 1` and the old value's bytes, which is `regBytesOf a.regs rid` since `regSetH`
stores `(rid, old)`, and none without eviction. -/
structure StorageJoinObl (X : Ctx) (tr : Trace) (pub : List F) (hts : List Nat) (σc : Nat → St)
    (A : HostAnsF) (memSz : Nat → Nat) : Prop where
  ans : ProducerOblOn (StgCall tr) X tr pub hts σc A memSz
  hb : ∀ r, HAct tr pub r → StgCall tr r →
    ((hostReqBytes tr pub r).map Prod.fst).Perm (stgAddrs (hostHid tr r) (hostArgs tr r))
  regFill : ∀ r, HAct tr pub r → StgCall tr r → (ansAt tr pub hts σc A memSz r).err = none →
    hostRegFill tr pub r =
      if (ansAt tr pub hts σc A memSz r).res = [1] then
        regBytesOf (ansAt tr pub hts σc A memSz r).regs (stgRid (hostHid tr r) (hostArgs tr r))
      else []

/-- **The joined producer contract**: the non-storage rows' obligations (the oracle's / other
producers', unchanged) and lane B's `StorageJoinObl` give the M6.4 `ProducerObl`, from which
`HostIf` follows as for the standalone segment. -/
theorem producerObl_join (hN : ProducerOblOn (fun r => ¬ StgCall tr r) X tr pub hts σc A memSz)
    (hS : StorageJoinObl X tr pub hts σc A memSz) : ProducerObl X tr pub hts σc A memSz :=
  producerObl_split (StgCall tr) hS.ans hN

/-- Conversely the storage part of `ProducerObl` is `StorageJoinObl.ans`: the join adds exactly the
`hb` and `regFill` clauses. -/
theorem storageJoinObl_of (h : ProducerObl X tr pub hts σc A memSz)
    (hb : ∀ r, HAct tr pub r → StgCall tr r →
      ((hostReqBytes tr pub r).map Prod.fst).Perm (stgAddrs (hostHid tr r) (hostArgs tr r)))
    (hr : ∀ r, HAct tr pub r → StgCall tr r → (ansAt tr pub hts σc A memSz r).err = none →
      hostRegFill tr pub r =
        if (ansAt tr pub hts σc A memSz r).res = [1] then
          regBytesOf (ansAt tr pub hts σc A memSz r).regs (stgRid (hostHid tr r) (hostArgs tr r))
        else []) :
    StorageJoinObl X tr pub hts σc A memSz :=
  ⟨producerOblOn_of h _, hb, hr⟩

/-! ## Non-vacuity of the buffer / register-fill readers -/

/-- `storage_write(klen = 3, kptr = 100, vlen = 2, vptr = 200, rid = 7)` reads `100, 101, 102, 200, 201`
and fills register 7. -/
theorem stgAddrs_write : stgAddrs 58 [3, 100, 2, 200, 7] = [100, 101, 102, 200, 201] ∧
    stgRid 58 [3, 100, 2, 200, 7] = 7 := by decide
/-- `storage_remove(klen = 2, kptr = 40, rid = 1)` reads `40, 41` and fills register 1. -/
theorem stgAddrs_remove : stgAddrs 60 [2, 40, 1] = [40, 41] ∧ stgRid 60 [2, 40, 1] = 1 := by decide
/-- A key taken from a register (`kptr = u64::MAX`) reads no memory. -/
theorem stgAddrs_regKey : stgAddrs 60 [5, 2 ^ 64 - 1, 1] = [] := by decide
/-- An evicted 2-byte value `[9, 8]` in register 7 is the fill `[(0, 9), (1, 8)]`. -/
theorem regBytesOf_ex : regBytesOf #[(3, ByteArray.mk #[1]), (7, ByteArray.mk #[9, 8])] 7 = [(0, 9), (1, 8)] := by
  decide

end HostIf
end WasmBase
