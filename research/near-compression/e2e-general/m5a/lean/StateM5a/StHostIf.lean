import StateM5a.Tmpl

/-!
# StateM5a.StHostIf — B-T1 item 3: the STATE rows fed by lane A's HOST rows (the M6 join, state side)

M5b's STATE rows take the execution side's requests on `SREQ [ts, pr, seg, klen, kptr, vlen, vptr]`
and bytes on `HB [ts, addr, byte]` (sent by the cached `HTAPE` on T1).  In the joined segment (plan
§3.3) the producer is lane A's HOST chip in the same trace, on its own cross-proof buses
(`WasmBase/HostChip.lean`):

* `HOSTQ` (208) `[ts, hid, S, np, a0lo, a0hi, …, a8lo, a8hi]` — one request per host call, the
  arguments as 32-bit halves (`aLo = P0 + 2^16 P1`, `aHi = P2 + 2^16 P3`);
* `HOSTR` (209) `[ts, st, rLo, rHi, gLo, gHi, ar, 0]` — the response the HOST row consumes;
* `HOSTB` (210) `[ts, hid, dir, pos, byte]` — the request / response bytes.

`StwH` / `StbH` are `Stw` / `Stb` with these buses in place of `SREQ` / `HB` (`m5tSegH D`); every
other table of the segment template is unchanged, so the working-set side cannot tell who fed it.
Storage calls (`NearSpecV3.Wasm.Host`, ids of `WasmBase.Chips.hostStorageFns`):

| call | `hid` | `np` | arguments |
|---|---|---|---|
| `storage_write` | 58 | 5 | `key_len, key_ptr, value_len, value_ptr, register_id` |
| `storage_remove` | 60 | 3 | `key_len, key_ptr, register_id` |

So `hid = 60 − 2·pr`, `np = 3 + 2·pr`, and the request is `a0 = klen`, `a1 = kptr`,
`a2 = pr·vlen + (1 − pr)·rid`, `a3 = pr·vptr`, `a4 = pr·rid`, high halves and `a5…a8` zero.

**Bus shape the state side needs from lane A (coordination, README §B-T1).**  A `storage_write`
reads two buffers in one call, so a `HOSTB` byte must say *which* buffer it belongs to: the state
side reads the 4th field as the byte's **linear-memory address** (`ptr + pos`, lane A's `memAddr`),
not the offset in its buffer.  `StbH` receives `HOSTB [ts, hid, 0, base + j, b]` with `base` the
buffer's pointer.  (Lane A's `HOSTB.msg` today carries the offset `pos`; with one buffer per call —
the only byte calls it has — the two agree up to the constant `ptr`.)

**Not yet the state side's (M6.4):** the response.  `StwH` sends `HOSTR [ts, 0, rLo, rHi, gLo, gHi,
1, 0]` with `r`, `g` witness columns: the evicted-value flag needs the entry's value before the
write (the `WM` read `WSA` already consumes) and `g_after` the gas counters of the host-side state
`σ`; both are open.  In a joined trace lane A's oracle `HOSTO` must not also answer storage calls.
Times: within one Wasm segment `ts` is the HOST row's step counter (`< 2^24`, ranged by `WSA`), and
every write of the segment is in one internal working-set segment (`WRITE` carries `seg = 0`), so
the `WM` chain orders all of them by `ts`.
-/

namespace StateM5a

open ZkFormal.Air

/-- Lane A's cross-proof host buses (`WasmBase.Chips.busHostQ/R/B`). -/
def B_HOSTQ : Nat := 208
def B_HOSTR : Nat := 209
def B_HOSTB : Nat := 210
def HID_WRITE : Nat := 58
def HID_REMOVE : Nat := 60
/-- The host chip's argument count (`Host.nArgs`). -/
def HOST_NARGS : Nat := 9

namespace StbH
def L : Layout := Stb.L ++ [("hid", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j

/-- `Stb`'s constraints (same columns, same offsets) plus: `hid` is constant on a run and is a
storage call's id. -/
def constraints : List Expr :=
  Stb.constraints ++
  [.isTransition * nx "act" * (1 - c "last") * (nx "hid" - c "hid"),
   c "act" * (c "hid" - K HID_WRITE) * (c "hid" - K HID_REMOVE)]

def interactions : List Interaction :=
  let A := c "act"
  [snd B_SHA_BYTES A [K ID_ST + c "m", c "j", c "b"],
   rcv B_HOSTB A [c "ts", c "hid", 0, c "base" + c "j", c "b"],
   snd B_DESC (c "last") [c "m", c "ts", c "base", c "j" + 1, c "hid"]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end StbH

namespace StwH
def L : Layout := Stw.L ++ [("S", 1), ("rid", 1), ("rlo", 1), ("rhi", 1), ("glo", 1), ("ghi", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

def hidE : Expr := K HID_REMOVE - K 2 * c "pr"

/-- The `HOSTQ` request of a storage call (`(lo, hi)` per argument). -/
def qMsg : List Expr :=
  let pr := c "pr"
  let args : List Expr :=
    [c "klen", c "kptr", pr * c "vlen" + (1 - pr) * c "rid", pr * c "vptr", pr * c "rid"]
  [c "ts", hidE, c "S", K 3 + K 2 * pr] ++
    ((List.range HOST_NARGS).flatMap fun j => [args.getD j 0, 0])

def constraints : List Expr := Stw.constraints

def interactions : List Interaction :=
  let A := c "act"; let gv := c "pr" - c "ve"; let gk := c "act" - c "ke"
  [rcv B_HOSTQ A qMsg,
   snd B_HOSTR A [c "ts", 0, c "rlo", c "rhi", c "glo", c "ghi", 1, 0],
   rcv B_DESC gk [c "mk", c "ts", c "kptr", c "klen", hidE],
   rcv B_SHA_DIGEST gk ([K ID_ST + c "mk", c "klen"] ++ (List.range 32).map fun b => c "dk" b),
   rcv B_DESC gv [c "mv", c "ts", c "vptr", c "vlen", hidE],
   rcv B_SHA_DIGEST gv ([K ID_ST + c "mv", c "vlen"] ++ (List.range 32).map fun b => c "dv" b),
   snd B_WRITE A ([0, c "ts"] ++ pack2 (fun b => c "dk" b) ++ [c "pr", c "vlen"] ++
     pack2 (fun b => c "dv" b))]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end StwH

/-- One STATE segment fed by lane A's HOST rows. -/
def m5tSegH (D : Nat) : Air :=
  { tables := [shaTable, Wsa.table, Wsl.table, Wsp.table D, Rng.table, StbH.table, StwH.table,
      Wsx.tableSeg D],
    numBuses := B_HOSTB + 1, numPub := NUM_PUB_SEG }

def tableNamesSegH : List String := ["SHA", "WSA", "WSL", "WSP", "RNG", "STBH", "STWH", "WSX"]

def namesJsonH (D : Nat) : String :=
  let q (s : String) := "\"" ++ s ++ "\""
  let ls := layoutsB D ++ [("WSX", Wsx.L), ("STBH", StbH.L), ("STWH", StwH.L)]
  "{" ++ ",".intercalate (ls.map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++
  s!",\"D\":{D},\"ws_depth\":{WS_DEPTH},\"zero_limbs\":[" ++
    ",".intercalate ((zeroLimbs D).map toString) ++ "],\"tables\":[" ++
    ",".intercalate (tableNamesSegH.map q) ++ "]}"

/-- The HOST-fed template differs from `m5tSeg` only in the two STATE tables. -/
theorem m5tSegH_tables (D : Nat) :
    (m5tSegH D).tables = [shaTable, Wsa.table, Wsl.table, Wsp.table D, Rng.table] ++
      [StbH.table, StwH.table] ++ [Wsx.tableSeg D] := rfl

/-- The HOST request shape of a storage call: `storage_write` sends 5 arguments under id 58,
`storage_remove` 3 under id 60 (`StwH.qMsg` at `pr = 1` / `pr = 0`). -/
theorem stwH_hid (pr : Nat) (hpr : pr = 0 ∨ pr = 1) :
    HID_REMOVE - 2 * pr = (if pr = 1 then HID_WRITE else HID_REMOVE) ∧
      3 + 2 * pr = (if pr = 1 then 5 else 3) := by
  rcases hpr with rfl | rfl <;> decide

end StateM5a
