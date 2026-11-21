import M5T1.Dsl

/-!
# M5T1.Ids — buses, message types, field ids

**Families.** Receipt `q` (1-based, in the order of the chunk's incoming list) owns the family
`qf = q`; family `0` is the receipt list itself. A field of family `qf` has the id
`sid = 128·qf + fid` (`fid < 128`) on the field-byte bus `FB`; the message of type `mt` of family
`mf` has the id `m = 128·mf + 96 + mt` (the SHA-256 message id), and its SHA-256 digest is the
field `fid = 96 + mt` of the same family.

**Buses** (table-local numbering; the prover adds no other bus):

| bus | message | role |
|---|---|---|
| `SHA_BYTES` | `(m, pos, byte)` | message bytes into the SHA-256 table |
| `SHA_DIGEST` | `(m, len, d₀..d₃₁)` | its digest |
| `RNG` | `(v)` | `v < 256` |
| `SCH` | the schema entry of a message row (`Schema.lean`) | pins every descriptor column |
| `FB` | `(sid, k, byte)` | byte `k` of field `sid` (a parsed or computed value) |
| `FLEN` | `(sid, len)` | the length of a variable field |
| `MBEG` / `MLEN` | `(m, ts, ptr)` / `(m, len)` | a message is demanded / its length |
| `HB` | `(ts, pos, byte)` | **lane B's `HB` = lane A's `HOSTB`** (execution → state bytes) |
| `SREQ` | `(ts, pr, seg, klen, kptr, vlen, vptr)` | **lane B's `SREQ`**: a write the STATE rows commit |
| `SRQ` / `SRS` / `HBR` | `(ts, seg, klen, kptr)` / `(ts, present, vlen, vptr)` / `(ts, pos, byte)` | a read (lane B's §M5b read design: key bytes on `HB`, value bytes back) |
| `VMCALL` / `VMRES` | `(qf, ts)` / `(qf, tsEnd, ok, nLogs, nActions, retIdx)` | the Wasm call of receipt `qf` (lane A): the context is the family's `FB` fields |
| `OUTC` / `OUTR` | `(qf, d₀..d₃₁)` | the outcome leaf / an outgoing receipt's hash (to `FINAL`) |
-/

namespace M5T1

def B_SHA_BYTES : Nat := 0
def B_SHA_DIGEST : Nat := 1
def B_RNG : Nat := 2
def B_SCH : Nat := 3
def B_FB : Nat := 4
def B_FLEN : Nat := 5
def B_MBEG : Nat := 6
def B_MLEN : Nat := 7
def B_HB : Nat := 8
def B_SREQ : Nat := 9
def B_SRQ : Nat := 10
def B_SRS : Nat := 11
def B_HBR : Nat := 12
def B_VMCALL : Nat := 13
def B_VMRES : Nat := 14
def B_OUTC : Nat := 15
def B_OUTR : Nat := 16
def NUM_BUSES : Nat := 17

/-! ## Message types -/

def MT_RL : Nat := 0
def MT_KEYR : Nat := 1
def MT_APRE : Nat := 2
def MT_KEYW : Nat := 3
def MT_APOST : Nat := 4
def MT_AH : Nat := 5
def MT_SEED : Nat := 6
def MT_RID : Nat := 7
def MT_RREF : Nat := 8
/-- `LOG0 + i`, `i < 4`. -/
def MT_LOG0 : Nat := 9
def MT_PART : Nat := 13
/-- `LEAF0 + n` for `n` logs, `n ≤ 4`. -/
def MT_LEAF0 : Nat := 14
def MT_PAD : Nat := 31
def MAX_LOGS : Nat := 4

/-- Message id of type `mt` in family `mf`. -/
def msgId (mf mt : Nat) : Nat := 128 * mf + 96 + mt

/-! ## Field ids (`fid`) -/

-- parsed from the receipt (RL)
def F_COUNT : Nat := 0
def F_PRED : Nat := 2
def F_RECV : Nat := 4
def F_RID : Nat := 5
def F_SIGNER : Nat := 8
def F_PK : Nat := 10
def F_GPRICE : Nat := 11
def F_METHOD : Nat := 17
def F_ARGS : Nat := 19
def F_GAS : Nat := 20
def F_DEPOSIT : Nat := 21
-- parsed from the receiver account (APRE)
def F_AMT : Nat := 30
def F_LOCKED : Nat := 31
def F_CODEH : Nat := 32
def F_USAGE : Nat := 33
-- computed by RX
def F_AMT2 : Nat := 40
def F_REFUND : Nat := 42
def F_GB : Nat := 43
def F_TB : Nat := 44
def F_LEAFN : Nat := 45
def F_HEIGHT : Nat := 50
def F_RANDV : Nat := 52
def F_TSTAMP : Nat := 53
def F_EPOCHH : Nat := 54
-- defined by the Wasm side (VM answer)
def F_LOG0 : Nat := 56
def F_RET : Nat := 61
def F_VBURNT : Nat := 70
def F_VUSED : Nat := 71
def F_VCOMP : Nat := 72
def F_VBAL : Nat := 73
def F_VUSAGE : Nat := 74
def F_VSUB : Nat := 75
/-- The digest of message type `mt` (same family). -/
def F_DIG (mt : Nat) : Nat := 96 + mt

/-! ## Segment kinds -/

def K_PAD : Nat := 0
/-- one constant byte `cv` -/
def K_C : Nat := 1
/-- a defined field (parse): bytes are free, sent on `FB` -/
def K_D : Nat := 2
/-- a used field: bytes received from `FB` -/
def K_U : Nat := 3
/-- a used variable field with no length prefix: its length is received on `FLEN` -/
def K_UV : Nat := 4
/-- a u32 length prefix being parsed: defines the next field's length (sent on `FLEN`) -/
def K_LP : Nat := 5
/-- a u32 length prefix being emitted: received on `FLEN` -/
def K_LE : Nat := 6
/-- the receipt count of the receipt list (u32, sent on `FLEN` as field `0` of family `0`) -/
def K_CNT : Nat := 7

/-! ## Constants of the spec (`NearSpecV3.D2.Fees`, `Params`) -/

def NAR_EXEC : Nat := 108059500000
def FC_BASE_EXEC : Nat := 780000000000
def FC_BYTE_EXEC : Nat := 2235934
def CREATE_ACCOUNT_EXEC : Nat := 7200000000000
def STORAGE_PER_BYTE : Nat := 10000000000000000000
def ZERO_BALANCE_LIMIT : Nat := 770
def MAX_METHOD_NAME : Nat := 256
def MAX_ARGS : Nat := 4194304

/-- Virtual addresses of the runtime's account key / value messages on `HB`/`HBR`. -/
def PTR_KEY : Nat := 0
def PTR_VAL : Nat := 128

end M5T1
