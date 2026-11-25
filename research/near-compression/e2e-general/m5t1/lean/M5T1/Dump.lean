import NearSpecV3.E2E.Machine
import NearSpecV3.E2E.CutW
import NearSpecV3.E2E.Refined
import NearSpecV3.E2E.StEnc
import Lean.Data.Json

/-!
# M5T1.Dump — the Lean run of one incoming receipt, recorded

`dumpCase cb wb` runs the checker's own `INTAKE` (`intakeK afDriver`) and engine steps
(`estep I.prog`, the `CM` machine of lane E) on a claim/witness pair. At every `incoming` position
it runs the receipt step **through the oracle form `pwO o`** (`CutW.lean`: the verbatim receipt
step with its VM calls answered by `o`; `pwO_std : pwO vmStd = processWithInstant`), with `o` the
checker's own VM (`vmStd`) plus a recorder, and prints, per receipt:

* the receipt (fields and Borsh bytes), the chunk context (gas price, height);
* the receipt state `RS` before and after (the counters of plan §3.2's gas/balance group and the
  output accumulators), the receiver account before and after;
* the VM query (the `CallCtx` fields the runtime builds) and answer (`Run`: gas, logs, return
  data, balance, storage usage, storage writes, promise actions);
* the outcome record and the new outgoing receipts with their Borsh bytes.

The JSON is what `../tracegen.py` turns into the M5-T1 trace. It is produced by the spec's code;
the recorder is a side channel only (`vmRec` returns exactly `vmStd q`).
-/

namespace M5T1.Dump

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution NearSpecV3.E2E
open NearSpecV3.Successor.StorageExecution.CutW
open Lean (Json)
open NearSpecV3.E2E.Enc (Ser)

def hexB (b : Bytes) : String :=
  let d (n : Nat) : Char := "0123456789abcdef".get ⟨n⟩
  String.mk (b.flatMap fun x => [d (x.toNat / 16), d (x.toNat % 16)])

def hexA (b : ByteArray) : String := hexB b.toList

def jn (n : Nat) : Json := Json.str (toString n)
def jb (b : Bytes) : Json := Json.str (hexB b)

initialize vmLog : IO.Ref (Array (VmQ × Run)) ← IO.mkRef #[]

@[noinline] unsafe def vmRecImpl (q : VmQ) : Except String Run :=
  match vmStd q with
  | .ok r => unsafeBaseIO (do vmLog.modify (·.push (q, r)); pure (.ok r))
  | .error e => .error e

/-- `vmStd` with a recorder (the recorder is a side channel; the value is `vmStd q`). -/
@[implemented_by vmRecImpl] def vmRec (q : VmQ) : Except String Run := vmStd q

def acctJ (a : Option Acct) : Json :=
  match a with
  | none => Json.null
  | some x => Json.mkObj [("amount", jn x.amount), ("locked", jn x.locked), ("usage", jn x.usage),
      ("v2", Json.bool x.v2), ("encode", jb x.encode),
      ("contract", jb x.contract.encode)]

def baseJ : Base → Json
  | .fcall m a g d => Json.mkObj [("kind", "fcall"), ("method", jb m), ("args", jb a),
      ("gas", jn g), ("deposit", jn d)]
  | .transfer d => Json.mkObj [("kind", "transfer"), ("deposit", jn d)]
  | _ => Json.mkObj [("kind", "other")]

def actJ : Act → Json
  | .base b => Json.mkObj [("raw", jb b.raw), ("base", baseJ b.b)]
  | .delegate r _ => Json.mkObj [("raw", jb r), ("base", Json.mkObj [("kind", "delegate")])]

def rcptJ (r : Rcpt) : Json :=
  let body : Json := match r.body with
    | .action y a => Json.mkObj [("kind", "action"), ("yield", Json.bool y), ("v2", Json.bool a.v2),
        ("signer", jb a.signer), ("refundTo", match a.refundTo with | some t => jb t | none => Json.null),
        ("signerPk", jb a.signerPk.encode), ("gasPrice", jn a.gasPrice),
        ("outputs", Json.arr (a.outputs.map (fun (d, x) => Json.arr #[jb d, jb x])).toArray),
        ("inputs", Json.arr (a.inputs.map jb).toArray),
        ("actions", Json.arr (a.actions.map actJ).toArray)]
    | .data rs d x => Json.mkObj [("kind", "data"), ("resume", Json.bool rs), ("dataId", jb d),
        ("data", match x with | some v => jb v | none => Json.null)]
    | .distribution _ => Json.mkObj [("kind", "distribution")]
  Json.mkObj [("pred", jb r.pred), ("recv", jb r.recv), ("rid", jb r.rid), ("body", body),
    ("encode", jb r.encode), ("bodyEncode", jb r.body.encode), ("ser", jb (Ser.enc r))]

def statusJ : OStatus → Json
  | .value => Json.mkObj [("kind", "value")]
  | .receipt rid => Json.mkObj [("kind", "receipt"), ("rid", jb rid)]
  | .failure => Json.mkObj [("kind", "failure")]
  | .valueBytes v => Json.mkObj [("kind", "valueBytes"), ("v", jb v)]

def outJ (x : OutD1) : Json :=
  Json.mkObj [("id", jb x.o.id), ("receiptIds", Json.arr (x.o.receiptIds.map jb).toArray),
    ("gasBurnt", jn x.o.gasBurnt), ("tokensBurnt", jn x.o.tokensBurnt),
    ("executor", jb x.o.executorId), ("status", statusJ x.status),
    ("statusEncode", jb x.status.encode),
    ("logs", Json.arr (x.logs.map jb).toArray), ("partialEncode", jb x.partialEncode),
    ("leaf", jb x.leaf), ("ser", jb (Ser.enc x))]

def rsJ (rs : RS) (recv : Bytes) : Json :=
  let acct : Json := match rs.o.getAcct recv with
    | .ok a => acctJ a
    | .error e => Json.str s!"error: {e}"
  Json.mkObj [("gas", jn rs.gas), ("compute", jn rs.compute), ("txBurnt", jn rs.txBurnt),
    ("otherBurnt", jn rs.otherBurnt), ("subsidized", jn rs.subsidized), ("wasmGas", jn rs.wasmGas),
    ("nOutcomes", jn rs.outcomes.length),
    ("outcomesChain", jb (NearSpecV3.E2E.Bnd.chainD Ser.enc rs.outcomes)),
    ("outgoingChain", jb (NearSpecV3.E2E.Bnd.chainD Ser.enc rs.outgoing)), ("nOutgoing", jn rs.outgoing.length),
    ("nInstant", jn rs.instant.length), ("nProposals", jn rs.proposals.length),
    ("outcomes", Json.arr (rs.outcomes.map outJ).toArray),
    ("outgoing", Json.arr (rs.outgoing.map rcptJ).toArray),
    ("recvAcct", acct),
    ("committed", Json.arr ((rs.o.committed ++ rs.o.prosp).map fun (k, v) =>
        Json.arr #[jb k, match v with | some b => jb b | none => Json.null]).toArray)]

def ctxJ (c : CallCtx) : Json :=
  Json.mkObj [("currentAccount", Json.str (hexB c.currentAccount.toUTF8.toList)),
    ("signer", Json.str (hexB c.signer.toUTF8.toList)),
    ("predecessor", Json.str (hexB c.predecessor.toUTF8.toList)),
    ("refundTo", Json.str (hexB c.refundTo.toUTF8.toList)),
    ("signerPk", Json.str (hexA c.signerPk)), ("input", Json.str (hexA c.input)),
    ("actionHash", match c.actionHash with | some h => Json.str (hexA h) | none => Json.null),
    ("blockHeight", jn c.blockHeight), ("blockTimestamp", jn c.blockTimestamp),
    ("epochHeight", jn c.epochHeight), ("accountBalance", jn c.accountBalance),
    ("accountLocked", jn c.accountLocked), ("storageUsage", jn c.storageUsage),
    ("attachedDeposit", jn c.attachedDeposit), ("prepaidGas", jn c.prepaidGas),
    ("randomSeed", Json.str (hexA c.randomSeed)), ("nPromiseResults", jn c.promiseResults.size),
    ("nReceivers", jn c.receivers.size)]

def runJ : Run → Json
  | .line l => Json.mkObj [("kind", "line"), ("line", Json.str l)]
  | .done s err => Json.mkObj [("kind", "done"),
      ("err", match err with | some e => Json.str e | none => Json.null),
      ("burnt", jn s.gas.burnt), ("used", jn s.gas.used), ("promisesGas", jn s.gas.promises),
      ("prepaid", jn s.gas.prepaid), ("compute", jn s.gas.computeUsage),
      ("logs", Json.arr (s.logs.map (fun b => Json.str (hexA b)))),
      ("ret", match s.ret with
        | none => Json.null
        | some (.inl v) => Json.mkObj [("value", Json.str (hexA v))]
        | some (.inr k) => Json.mkObj [("receiptIdx", jn k)]),
      ("balance", jn s.balance), ("storageUsage", jn s.storageUsage),
      ("subsidized", jn s.subsidized), ("nActions", jn s.actions.size),
      ("actions", Json.arr (s.actions.map (fun a => Json.str a.text))),
      ("writes", match s.real with
        | some r => Json.arr (r.writes.map fun (k, v) =>
            Json.arr #[Json.str (hexA k), match v with | some b => Json.str (hexA b) | none => Json.null])
        | none => Json.null)]

/-- Step the engine from `c` until it reaches an `incoming` position with a receipt, a `done`
position, an error, or the fuel runs out. -/
def toIncoming (P : Prog) : Nat → EConf → Except String EConf
  | 0, c => .ok c
  | n + 1, c => match c.pos with
    | .incoming (_ :: _) _ => .ok c
    | .done _ => .ok c
    | _ => do toIncoming P n (← estep P c)

def dumpCase (cb wb : Bytes) : IO Json := do
  let I ← IO.ofExcept (intakeK afDriver true cb wb fun I => pure I)
  let P := I.prog
  let env := I.env
  let mut c : EConf := ⟨.start, initRec afCfg.wasm env⟩
  let mut out : Array Json := #[]
  for _ in [0:64] do
    c ← IO.ofExcept (toIncoming P 100000 c)
    match c.pos with
    | .incoming (r :: rest) rs =>
      vmLog.set #[]
      -- the receipt step through the oracle form, recorded
      let stepO := incomingBodyO (pwO vmRec) P.fl P.hooks P.env (decodeOf P.fl.globalActions) rs r
      let (rs', st') ← IO.ofExcept (stepO c.st P.env)
      -- the checker's own step (estep) gives the same next configuration's RS
      let c' ← IO.ofExcept (estep P c)
      let same : Bool := match c'.pos with
        | .incoming _ rs2 => rs2.gas == rs'.gas && rs2.txBurnt == rs'.txBurnt &&
            rs2.outcomes.length == rs'.outcomes.length && rs2.outgoing.length == rs'.outgoing.length &&
            (rs2.outcomes.map OutD1.leaf) == (rs'.outcomes.map OutD1.leaf) &&
            (rs2.outgoing.map Rcpt.encode) == (rs'.outgoing.map Rcpt.encode)
        | _ => false
      let calls ← vmLog.get
      let _ := st'
      out := out.push (Json.mkObj [
        ("receipt", rcptJ r),
        ("env", Json.mkObj [("gasPrice", jn env.ctx.gasPrice), ("height", jn env.ctx.height),
                            ("gasLimit", jn env.ctx.gasLimit), ("own", jn env.ctx.own),
                            ("numShards", jn env.ctx.layout.numShards)]),
        ("before", rsJ rs r.recv), ("after", rsJ rs' r.recv),
        ("estepAgrees", Json.bool same),
        ("calls", Json.arr (calls.map fun (q, x) =>
            Json.mkObj [("method", Json.str q.method), ("codeLen", jn q.code.size),
                        ("ctx", ctxJ q.ctx), ("run", runJ x)]))])
      c := { c' with pos := .incoming rest rs' }
      c := c'
    | _ => break
  pure (Json.mkObj [("receipts", Json.arr out),
    ("incoming", Json.arr (I.receipts.map rcptJ).toArray),
    ("encodeIncoming", jb (encodeRcpts I.receipts)),
    ("appliedReceiptsHash", jb I.w.appliedReceiptsHash),
    ("env", Json.mkObj [("gasPrice", jn env.ctx.gasPrice), ("height", jn env.ctx.height),
       ("gasLimit", jn env.ctx.gasLimit), ("blockTimestamp", jn env.blockTimestamp),
       ("epochHeight", jn env.epochHeight), ("randomValue", jb env.randomValue),
       ("chainId", jb env.chainId)])])

end M5T1.Dump
