import WasmBase.Main.HostIf
import WasmBase.Main.HostAns

/-!
# WasmBase.Main.HostIfTape — `HostIf` ↔ lane E's call tape (M6.5) and the producer obligations (M6.4)

## 1. The tie to the call machine (M6.5)

Lane E's refined machine carries, inside a Wasm call, the configuration
`CallConf.ent p k (.cont s) n` (`WmV = Option (VmQ × CallConf)`); its state `s` at a cut is
(`StepSide.st_eq_of_sideG`) determined by its Wasm-visible part `vis s`, its host side `sideR s` and
its gas register.  The chained segments (`Cuti.seg_chain_csteps_σ`) end at a state with
`sideR sN = σ (t_out + 1)`; with the per-segment thread of `HostIf` that is `σc m` (`HostIf.thread_out`,
`seg_sound_hostIf`).  Here:

* `confSt` — the state a call configuration carries at a cut;
* **`cden_of_parts`** — the call's denotation from a cut depends only on `(vis, sideR, gas.g)` of the
  state (so on the thread's σ at that cut and the Wasm part);
* **`callResult_of_chainσ`** — composing a call's entry (`CSteps q .pre (.ent p k (.cont s0) n)`, the
  CHAIN sub-lane's entry composition) with the σ-pinned chained segments: either SHA-384 collides, or
  the tape answer `callResult q` is the denotation from the last cut's state `sN`, which is on the
  thread (`OutSσ`).  So the `Run` (logs, return data, promises, gas) is a function of the last σ, the
  final Wasm part and the remaining fuel/entries.

The global thread across segments (one `σ` for the chain, agreeing with each segment's
`thread hts σc` on its time range) is the CHAIN sub-lane's combined statement and not done here.

## 2. The producer obligations (M6.4, lane B)

`ProducerObl` lists, per active HOST row, what lane B's state rows must prove so that `HostIf` holds:
the `HOSTR` columns, the response `HOSTB` bytes and the REG-C effect are the answer function's
(`HostAns.HAns`) at the thread's `σc j`, and `σc (j + 1)` is the answer's host side.  The
per-function answers for the corpus functions:

| host (hid) | request | reads | `HOSTR` (st, word, g_after) | `HOSTB` response | REG-C | σ' |
|---|---|---|---|---|---|---|
| `register_len` (6) | `id` | registers | ok/err of base charge; `|reg id|` or `2^64−1`; `remaining` | — | — | gas |
| `input` (48) | `id` | `ctx.input` | base + `writeRegisterBase`; regSetH domain; — ; `remaining` | — | reg `id := ctx.input` (`reg = 1` bytes) | gas, registers, regUsage |
| `read_register` (49) | `id, ptr` | register `id`, mem size | base, read-reg base/byte, write-mem base/byte; — | bytes of reg `id` at `ptr` | — | gas |
| `storage_write` (58) | `klen, kptr, vlen, vptr, reg` | key/value bytes (request), trie (σ) | storage charges; 1 iff evicted; | — | reg `reg := old value` if any | gas, trie/real, storageUsage, registers |
| `log_utf8` (45) | `len, ptr` | the bytes (request) | log charges, utf8 check; — | — | — | gas, logs, totalLogLen |
| `value_return` (50) | `len, ptr` | the bytes (or a register) | base + data-receipt burn; — | — | — | gas, ret |
| `ed25519_verify` (61) | `sig_len, sig_ptr, msg_len, msg_ptr, pk_len, pk_ptr` | the three byte strings | charges; 1/0 verdict | — | — | gas |

Answer functions are explicit (and proved equal to the arm, `HostAns.register_len_ans`,
`input_ans`, `read_register_ans`) for the first three; the others are the obligation shape
`HostAnsF` (an answer function per name, with the arm-agreement `spec` clause still to be proved).
-/

namespace WasmBase
namespace HostIf

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide HostAns

/-! ## 1. The tie to the call machine -/

section Tape
open NearSpecV3.Wasm.CallCut

/-- The state a call configuration carries at a Wasm cut. -/
def confSt : CallConf → Option St
  | .ent _ _ (.cont s) _ => some s
  | _ => none

/-- **The call's denotation from a cut reads the state only through `(vis, sideR, gas.g)`.** -/
theorem cden_of_parts (q : CallArgs) (p : Prepared) (k : EntK) (n : Nat) {s s' : St}
    (hv : vis s = vis s') (hσ : sideR s = sideR s') (hg : s.gas.g = s'.gas.g) :
    cden q (.ent p k (.cont s) n) = cden q (.ent p k (.cont s') n) := by
  rw [st_eq_of_sideG hv (sideG_of_sideR hσ) hg]

/-- **The tape answer of a call from its σ-pinned segments.**  The call's entry reaches the first
segment's in-state `s0` (`hpre`), the chained segments are σ-pinned (`seg_chain_csteps_σ`'s
hypotheses): either SHA-384 collides, or `callResult q` is the denotation from the last cut's state
`sN`, which is on the thread (`OutSσ`: `sideR sN = σ (t_out + 1)`). -/
theorem callResult_of_chainσ (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St}
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : Cuti.SegD) (ds : List Cuti.SegD) (hok : ∀ d ∈ d0 :: ds, Cuti.SegPremσ X nloc ngl sg σ d)
    (hL : Cuti.LinkL (fun d d' => Cuti.LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St}
    (h0 : Cuti.InSσ X sg σ d0 s0) (n : Nat) (hn : ((d0 :: ds).map Cuti.SegD.n).sum ≤ n)
    (hpre : CSteps q .pre (.ent X.toCtx.p k (.cont s0) n)) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, callResult q = cden q (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map Cuti.SegD.n).sum)) ∧
        Cuti.OutSσ X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases Cuti.seg_chain_csteps_σ X hstepgas hg64 q hq k d0 ds hok hL h0 n hn with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · refine Or.inr ⟨sN, ?_, h2⟩
    have e0 : cden q .pre = callResult q := rfl
    rw [← e0, cden_of_csteps hpre, cden_of_csteps h1]

#print axioms cden_of_parts
#print axioms callResult_of_chainσ

end Tape

/-! ## 2. Trace readers of a HOST row -/

/-- A 64-bit word from four 16-bit limbs of HOST row `r` starting at column `c`. -/
def limb4 (tr : Trace) (r c : Nat) : Nat :=
  rowNat tr 22 r c + 65536 * rowNat tr 22 r (c + 1) + 65536 ^ 2 * rowNat tr 22 r (c + 2) +
    65536 ^ 3 * rowNat tr 22 r (c + 3)

/-- The request's host id. -/
def hostHid (tr : Trace) (r : Nat) : Nat := rowNat tr 22 r Host.hid
/-- The request's arguments (`np` words). -/
def hostArgs (tr : Trace) (r : Nat) : List Nat :=
  (List.range (rowNat tr 22 r Host.np)).map fun j => limb4 tr r (Host.P j)
/-- The response status, `g_after` and result words. -/
def hostSt (tr : Trace) (r : Nat) : Nat := rowNat tr 22 r Host.st
def hostGAfter (tr : Trace) (r : Nat) : Nat := limb4 tr r Host.ga
def hostRes (tr : Trace) (r : Nat) : List Nat :=
  if rowNat tr 22 r Host.ar = 0 then [] else [limb4 tr r Host.rb]

/-- The HOSTB rows of call `r` as `(dir, reg, addr, byte)`, `addr = ptr + pos`. -/
def hostBytes (tr : Trace) (pub : List F) (r : Nat) : List (Nat × Nat × Nat × Nat) :=
  (hostbOf tr pub r).filterMap fun r' =>
    if rowNat tr 25 r' HostB.act = 0 then none else
    some (rowNat tr 25 r' HostB.dir, rowNat tr 25 r' HostB.reg,
      rowNat tr 25 r' HostB.ptrLo + 65536 * rowNat tr 25 r' HostB.ptrHi + rowNat tr 25 r' HostB.pos,
      rowNat tr 25 r' HostB.bv)

/-- The memory the request reads, as a byte function (absent addresses read `0`; only request
bytes, `dir = 0`, `reg = 0`, count). -/
def hostReadMem (tr : Trace) (pub : List F) (r : Nat) (a : Nat) : UInt8 :=
  match (hostBytes tr pub r).find? (fun x => x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = a) with
  | some x => UInt8.ofNat x.2.2.2
  | none => 0

/-- The response's plain payload bytes (`dir = 1`, `reg = 0`) as `(addr, byte)`. -/
def hostRespBytes (tr : Trace) (pub : List F) (r : Nat) : List (Nat × Nat) :=
  ((hostBytes tr pub r).filter fun x => x.1 = 1 ∧ x.2.1 = 0).map fun x => (x.2.2.1, x.2.2.2)

/-- The name of a host id in the M2 table. -/
def hidName (hid : Nat) : String := ((hostFnsM2.find? (·.1 = hid)).map (·.2.1)).getD ""

/-! ## 3. The producer obligations (M6.4) -/

/-- **An answer function per host name**: from the post-sync state `σ` (host side read), the
arguments, the memory bytes and the memory size, the answer, and the host side after the call. -/
structure HostAnsF where
  ans : String → St → List Nat → (Nat → UInt8) → Nat → HAns
  side : String → St → List Nat → (Nat → UInt8) → Nat → St

/-- `HostAnsF` for the three proved functions (others: the empty answer, to be filled). -/
def ansKnown (name : String) (σ : St) (args : List Nat) (_mem : Nat → UInt8) (memSz : Nat) : HAns :=
  match name with
  | "register_len" => ansRegisterLen σ (args.getD 0 0)
  | "input" => ansInput σ (args.getD 0 0)
  | "read_register" => ansReadRegister σ (args.getD 0 0) (args.getD 1 0) memSz
  | _ => ⟨some "unmodeled", [], σ.gas, σ.registers, σ.regUsage, []⟩

/-- The flattening of an answer's memory writes to `(addr, byte)`. -/
def wrBytes (a : HAns) : List (Nat × Nat) :=
  a.wr.flatMap fun w => (List.range w.2.size).map fun i => (w.1 + i, (w.2[i]!).toNat)

/-- **What lane B's state rows must prove (M6.4)**, per active HOST row `r` with rank `j`, request
`(hid, args)`, memory read `hostReadMem` and memory size `memSz r`, `a := A.ans name (σc j) args mem memSz`:

* `spec` — `A` is the arm: for every post-sync state `s` whose popped arguments are `args`, whose
  memory agrees with `mem` and whose host side is `σc j`, the arm's run is `runOf (pop s) a` and the
  host side after is `A.side …` (discharged for `register_len`/`input`/`read_register` by
  `HostAns.*_ans`; FOOT2's two-run lemma in general);
* `st` / `word` / `gas` — the `HOSTR` columns encode `a`: status `0` iff `a.err = none`, the result
  words, `g_after = a.gas.remaining`;
* `resp` — the response payload bytes on `HOSTB` are `a`'s memory writes;
* `regs` — `(σc (j+1)).registers = a.regs` and the REG-C traffic moves `(σc j).registers` to it;
* `next` — `σc (j + 1)` is the answer's host side;
* `cap` — the register files stay below the cap.

With the AIR facts and `HostFootprint` these give `HostIf` (the `ans` clause is `spec` read at the
honest pre-state).  This is the statement only. -/
structure ProducerObl (X : Ctx) (tr : Trace) (pub : List F) (hts : List Nat) (σc : Nat → St)
    (A : HostAnsF) (memSz : Nat → Nat) : Prop where
  spec : ∀ r, HAct tr pub r → ∀ s : St,
    sideR s = σc (rank hts (rowNat tr 22 r 1)) →
    (∀ i, i < (hostArgs tr r).length → vNum (s.stack[s.stack.size - (hostArgs tr r).length + i]?.getD (.i32 0)) =
      (hostArgs tr r).getD i 0) →
    (∀ x ∈ hostBytes tr pub r, x.1 = 0 → x.2.1 = 0 → (readByte s x.2.2.1).toNat = x.2.2.2) →
    memBytes s = memSz r →
    (hostCall (hidName (hostHid tr r))).get!.run s =
      runOf { s with stack := s.stack.extract 0 (s.stack.size - (hostArgs tr r).length) }
        (A.ans (hidName (hostHid tr r)) s (hostArgs tr r) (hostReadMem tr pub r) (memSz r))
  st : ∀ r, HAct tr pub r →
    (hostSt tr r = 0 ↔ (A.ans (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
      (hostReadMem tr pub r) (memSz r)).err = none)
  word : ∀ r, HAct tr pub r →
    hostRes tr r = (A.ans (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
      (hostReadMem tr pub r) (memSz r)).res
  gas : ∀ r, HAct tr pub r → hostSt tr r = 0 →
    hostGAfter tr r = (A.ans (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
      (hostReadMem tr pub r) (memSz r)).gas.remaining
  resp : ∀ r, HAct tr pub r →
    hostRespBytes tr pub r = wrBytes (A.ans (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1)))
      (hostArgs tr r) (hostReadMem tr pub r) (memSz r))
  regs : ∀ r, HAct tr pub r →
    (σc (rank hts (rowNat tr 22 r 1) + 1)).registers =
      (A.ans (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
        (hostReadMem tr pub r) (memSz r)).regs ∧
    RegStep (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (σc (rank hts (rowNat tr 22 r 1))).registers (σc (rank hts (rowNat tr 22 r 1) + 1)).registers
  next : ∀ r, HAct tr pub r →
    σc (rank hts (rowNat tr 22 r 1) + 1) =
      A.side (hidName (hostHid tr r)) (σc (rank hts (rowNat tr 22 r 1))) (hostArgs tr r)
        (hostReadMem tr pub r) (memSz r)
  cap : ∀ j, ∀ e ∈ (σc j).registers.toList, e.2.size < Register.cap

end HostIf
end WasmBase
