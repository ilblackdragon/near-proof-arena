import ZkFormal.Near.Render.Common

/-!
# ZkFormal.Near.Render.RcptSim — the `rcpt` side, simulated from an `Ext`

Until the `rcpt` table lands, the cross-table bus checks use the messages
`rcpt` sends and receives (NEAR-AIR.md §2, §3.3), computed directly from the
records and the claim:

* SHA messages `RC`, `RF`, `PEO(r)`, `LEAF(r)`, `RID(r)` (refunds only);
* `DIGEST` receives of `RC`, `RF`, `PEO(r)`, `RID(r)` (the `LEAF` digests go to
  `mrk`);
* `KEYNIB (r, t, sym, last)` sends, `FINAL (r, k)` receives;
* `MEM` read `(k, tprev, i, bef_i, l_i, s_i)` / write `(k, r+1, i, aft_i, l_i, s_i)`;
* `RIDS (r, i, id_i)` and `MPOS (0, r, LEAF(r), 68)` sends.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- One bus message of a simulated table: bus, send?, message, multiplicity. -/
structure BusMsg where
  bus : Nat
  send : Bool
  msg : List Nat
  mult : Nat := 1
  deriving Repr, Inhabited

def peoBytes (I : Info) (r : Nat) : List Nat := toNats (I.e.outcomeOf I.c r).partialEncode

def leafBytes (I : Info) (r : Nat) : List Nat :=
  leBytes 4 2 ++ toNats (I.e.rc r).receiptId ++ shaN (peoBytes I r)

def hasRefund (I : Info) (r : Nat) : Bool := I.e.refundOf I.c r ≠ []

def ridBytes (I : Info) (r : Nat) : List Nat :=
  toNats (I.e.rc r).receiptId ++ leBytes 8 I.c.blockHeight ++ leBytes 8 0

def rcBytes (I : Info) : List Nat :=
  toNats (u64 I.c.shardId ++ encodeReceipts I.e.rs)

def rfBytes (I : Info) : List Nat := toNats (encodeReceipts (I.e.refunds I.c))

/-- The SHA messages `rcpt` emits. -/
def rcptMsgs (I : Info) : List Msg :=
  [⟨msgId K_RC 0, rcBytes I⟩, ⟨msgId K_RF 0, rfBytes I⟩] ++
  (List.range I.nRcpt).flatMap fun r =>
    [⟨msgId K_PEO r, peoBytes I r⟩, ⟨msgId K_LEAF r, leafBytes I r⟩] ++
    (if hasRefund I r then [⟨msgId K_RID r, ridBytes I r⟩] else [])

def digestMsg (m : Msg) : List Nat := [m.id, m.bytes.length] ++ shaN m.bytes

/-- Bus traffic of `rcpt` (everything except its BYTES sends, which are
`rcptMsgs`; use `shaSim`/`bytesSends`). -/
def rcptBus (I : Info) : List BusMsg :=
  let e := I.e
  let digs := (rcptMsgs I).filter (fun m => m.id % 16 ≠ K_LEAF) |>.map fun m =>
    ({ bus := B_DIGEST, send := false, msg := digestMsg m } : BusMsg)
  digs ++ (List.range I.nRcpt).flatMap fun r =>
    let rc := e.rc r
    let syms := keySyms rc
    let k := e.slot r
    let a0 := (e.acc0 k)
    let bef := leBytes 16 (e.amtAt k r)
    let aft := leBytes 16 (e.amtAt k r + rc.deposit)
    let lk := leBytes 16 a0.locked
    let st := leBytes 8 a0.storageUsage
    (syms.zip (List.range syms.length)).map (fun (s, t) =>
      ({ bus := B_KEYNIB, send := true, msg := [r, t, s, if s = SYM_END then 1 else 0] } : BusMsg)) ++
    [{ bus := B_FINAL, send := false, msg := [r, k] }] ++
    (List.range 16).flatMap (fun i =>
      [{ bus := B_MEM, send := false, msg := [k, tprevOf e r, i, bef.getD i 0, lk.getD i 0, st.getD i 0] },
       { bus := B_MEM, send := true, msg := [k, r + 1, i, aft.getD i 0, lk.getD i 0, st.getD i 0] }]) ++
    (List.range 32).map (fun i =>
      ({ bus := B_RIDS, send := true, msg := [r, i, (toNats rc.receiptId).getD i 0] } : BusMsg)) ++
    [{ bus := B_MPOS, send := true, msg := [0, r, msgId K_LEAF r, 68] }]

/-- `BYTES` sends of a message list. -/
def bytesSends (ms : List Msg) : List BusMsg :=
  ms.flatMap fun m => (m.bytes.zip (List.range m.bytes.length)).map fun (b, p) =>
    { bus := B_BYTES, send := true, msg := [m.id, p, b] }

/-- The `sha` table's side, simulated: receives every byte, provides every digest once. -/
def shaSim (ms : List Msg) : List BusMsg :=
  ms.flatMap fun m =>
    ((m.bytes.zip (List.range m.bytes.length)).map fun (b, p) =>
      ({ bus := B_BYTES, send := false, msg := [m.id, p, b] } : BusMsg)) ++
    [{ bus := B_DIGEST, send := true, msg := digestMsg m }]

end ZkFormal.Near.Render
