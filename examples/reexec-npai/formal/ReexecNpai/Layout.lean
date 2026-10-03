import NpaiIR.Lib.Num
import NpaiIR.Asm
import ReexecNpai.Canon

/-!
# Memory layout and data segment of the `reexec-npai` verifier

All addresses are compile-time constants below `memSize = 13 844 304`
(`≤ 2^24`, the NPAI limit).

| region | address | size | content |
|---|---|---|---|
| `DATA` | 0 | 168 | constants (data segment) |
| `SCR` | 512 | 2048 | scratch buffers |
| `CLM` | 2560 | 309 | `claim.bin` |
| `CELL` | 3072 | 512 | 4/8/16-byte cells (lengths, counters, accumulators) |
| `RT` | 3584 | 256 × 64 | receipt table (field pointers) |
| `OL` | 19968 | 256 × 32 | outcome leaves |
| `RB` | 28160 | 88 840 | `u32 count ‖ refund receipts` |
| `AR` | 117000 | 24 × `NCAP` | trie arena |
| `KL` | `AR + 24 NCAP` | 4 × `NCAP` | child lists |
| `STK` | `KL + 4 NCAP` | 4 × `NCAP` | parse stack |
| `SH8` | `PF - 8` | 8 | shard id (for the receipts commitment) |
| `PF` | | `PMAX` | `proof.bin` |
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1 ArenaCore NpaiIR

/-! ## Limits -/

/-- Largest accepted proof (honest proofs are ≤ 4 997 930 bytes). -/
def PMAX : Nat := 5000000
/-- Largest number of trie records (honest tries have ≤ 3 000 000 / 11). -/
def NCAP : Nat := 272728

/-! ## Regions -/

def DATA : Nat := 0
def SCR : Nat := 512
def CLM : Nat := 2560
def CELL : Nat := 3072
def RT : Nat := 3584
def OL : Nat := 19968
def RB : Nat := 28160
def AR : Nat := 117000
def KL : Nat := AR + 24 * NCAP
def STK : Nat := KL + 4 * NCAP
def SH8 : Nat := STK + 4 * NCAP
def PF : Nat := SH8 + 8
def MEMSIZE : Nat := PF + PMAX

/-! ## Data segment -/

def D_CPRE : Nat := 0      -- claimPrefix (77)
def D_SYS : Nat := 80      -- "system" (6)
def D_MID : Nat := 88      -- receiptMid (13)
def D_FF : Nat := 104      -- 16 × 0xFF (u128::MAX)
def D_G : Nat := 120       -- G, u64 LE
def D_P519 : Nat := 128    -- 5^19, u64 LE
def D_ZERO : Nat := 136    -- 32 zero bytes
def DATALEN : Nat := 168

def dataSeg : List UInt8 :=
  claimPrefix ++ zeros 3 ++ AccountId.system ++ zeros 2 ++ receiptMid ++ zeros 3 ++
  List.replicate 16 (255 : UInt8) ++ u64 Params.G ++ u64 (5 ^ 19) ++ zeros 32

/-! ## Cells -/

def C_PEND : Nat := CELL         -- u32: PF + |proof|
def C_N : Nat := CELL + 4        -- u32: receipt count
def C_REND : Nat := CELL + 8     -- u32: end of the receipts section
def C_TOK : Nat := CELL + 16     -- 17 bytes: tokens burnt accumulator (u128 + carry byte)
def C_NREF : Nat := CELL + 40    -- u32: refund count
def C_RBEND : Nat := CELL + 44   -- u32: end of the refund buffer
def C_NODES : Nat := CELL + 48   -- u32: number of trie records
def C_ROOT : Nat := CELL + 64    -- 32 bytes: computed root hash
def C_I : Nat := CELL + 96       -- u32: loop index saved across calls
def C_KC : Nat := CELL + 100     -- u32: next free child-list index (parse)

/-! ## Scratch -/

def S_KEY : Nat := SCR           -- target key nibbles (≤ 130)
def S_HP : Nat := SCR + 256      -- hex-prefix build buffer (≤ 66)
def S_A : Nat := SCR + 384       -- 32-byte bignum temporaries
def S_B : Nat := SCR + 416
def S_C : Nat := SCR + 448
def S_D : Nat := SCR + 480
def S_E : Nat := SCR + 512
def S_ID : Nat := SCR + 576      -- refund id preimage (48) / digest
def S_OUT : Nat := SCR + 640     -- outcome partial encoding (≤ 133)
def S_LEAF : Nat := SCR + 800    -- outcome leaf preimage (68)
def S_H : Nat := SCR + 896       -- digests

end ReexecNpai
