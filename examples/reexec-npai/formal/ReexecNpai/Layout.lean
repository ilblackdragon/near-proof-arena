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
def KL : Nat := 6662472
def STK : Nat := 7753384
def SH8 : Nat := 8844296
def PF : Nat := 8844304
def MEMSIZE : Nat := 13844304

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

def C_PEND : Nat := 3072         -- u32: PF + |proof|
def C_N : Nat := 3076        -- u32: receipt count
def C_REND : Nat := 3080     -- u32: end of the receipts section
def C_TOK : Nat := 3088     -- 17 bytes: tokens burnt accumulator (u128 + carry byte)
def C_NREF : Nat := 3112    -- u32: refund count
def C_RBEND : Nat := 3116   -- u32: end of the refund buffer
def C_NODES : Nat := 3120   -- u32: number of trie records
def C_ROOT : Nat := 3136    -- 32 bytes: computed root hash
def C_I : Nat := 3168       -- u32: loop index saved across calls
def C_KC : Nat := 3172     -- u32: next free child-list index (parse)

/-! ## Scratch -/

def S_KEY : Nat := 512           -- target key nibbles (≤ 130)
def S_HP : Nat := 768      -- hex-prefix build buffer (≤ 66)
def S_A : Nat := 896       -- 32-byte bignum temporaries
def S_B : Nat := 928
def S_C : Nat := 960
def S_D : Nat := 992
def S_E : Nat := 1024
def S_ID : Nat := 1088      -- refund id preimage (48) / digest
def S_OUT : Nat := 1152     -- outcome partial encoding (≤ 133)
def S_LEAF : Nat := 1312    -- outcome leaf preimage (68)
def S_H : Nat := 1408       -- digests

theorem layout_ok : KL = AR + 24 * NCAP ∧ STK = KL + 4 * NCAP ∧ SH8 = STK + 4 * NCAP ∧ PF = SH8 + 8 ∧
    MEMSIZE = PF + PMAX ∧ MEMSIZE ≤ 16777216 := by decide

end ReexecNpai
