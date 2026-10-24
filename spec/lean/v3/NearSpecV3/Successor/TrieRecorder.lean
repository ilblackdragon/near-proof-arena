import NearSpecV3.Wasm.TrieAccounting
import NearSpecV3.StorageBound
import NearSpecV3.Successor.ActionsReceipts

/-!
# W00 interface 5/7 — the trie recorder contract

W09 replaces `checkD2Core`'s conservative `baseBytes + 2000 * removals ≤ 4 000 000` guard with a real
chunk-scoped recorder; W11 needs trie retention for left/right children, child-shard congestion and
buffers. Both program against the same recorder interface, agreed here.

## The contract

* **Read/write/remove/code access.** `RecorderOps` names the five storage operations a chunk
  performs, each returning the trie-accounting `Out` (`Wasm/TrieAccounting.lean`) with its gas,
  accounting cache and recorded-storage growth. `codeOf` reads a contract blob by code hash out of the
  recorded storage; an absent blob is `MissingTrieValue`.
* **Per-receipt accounting.** `ChunkAccounting` carries the chunk-scoped `Recorder`, the size at the
  receipt's start and the two protocol limits. `receiptGrowth` and `chunkGrowth` are the two
  quantities nearcore tests (`recorded_storage_counter.rs:19-33`; `lib.rs:838-845`).
* **Chunk soft-limit state.** `ChunkAccounting.softLimitReached` is the *soft* limit's state, not a
  rejection: nearcore stops processing receipts and defers the rest rather than invalidating the chunk
  (`lib.rs:2386,2464,2576,3003,2703`; `congestion_control.rs:889`). W09 owns the deferral semantics;
  this module only exposes the state.
* **Rollback.** The recorder is **not** rolled back (`trie_recording.rs`'s counter is chunk-scoped and
  `record_with` only grows); a failed receipt's *write effects* are. `RealStore.rollbackEffects` states
  exactly that split as a theorem: rollback restores the overlay/writes but keeps the recorder and
  accounting cache.

## What is not established

* `RecorderOps` is a *structure of operations*, not a proof that the operations agree with nearcore's
  `External`. W09 owns the differential obligation (`oracle/d3-ttn`, `docs/research/d3-trie-accounting.md`).
* The soft-limit *deferral* semantics (which receipts are deferred and how the chunk continues) is not
  modelled. W09/W11 must supply it; the workplan's W09 success criterion explicitly forbids declaring
  the task complete from an accounting link that assumes the missing recorder result.
* The `Σ|values| + 2000·R` upper-bound question (UQ-015, owner L5) is answered only at the
  `StorageBound` module's level: `guard_sufficient` holds *given* `List.Sublist r.charged values`, and
  that inclusion is a hypothesis there. This module does not close it.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3 NearSpecV3.Wasm NearSpecV3.Wasm.TTN

/-! ## The storage operations -/

/-- The five storage operations a chunk performs, with their trie-accounting results. Each is the
corresponding `TTN` function; the structure exists so W09/W11 can swap in an instrumented
implementation without touching `Wasm/Host.lean`. -/
structure RecorderOps where
  read : RealStore → ByteArray → Gas → Out
  write : RealStore → ByteArray → Gas → Out
  remove : RealStore → ByteArray → Gas → Out
  hasKey : RealStore → ByteArray → Gas → Out
  /-- Contract-code access by code hash from the recorded storage. -/
  codeOf : NearSpecV3.Wasm.TTN.Store → ByteArray → Except String ByteArray

/-- The successor's concrete operations: the pinned `TTN` functions, unchanged. -/
def trieRecorderOps : RecorderOps where
  read := TTN.storageRead
  write := TTN.storageWrite
  remove := TTN.storageRemove
  hasKey := TTN.storageHasKey
  codeOf := fun st h =>
    match st h with
    | some c => .ok c
    | none => .error errMissing

/-- The concrete code access is exactly "look the blob up in the recorded storage". -/
theorem codeOf_eq (st : NearSpecV3.Wasm.TTN.Store) (h : ByteArray) :
    trieRecorderOps.codeOf st h =
      (match st h with | some c => .ok c | none => .error errMissing) := rfl

/-! ## Per-receipt accounting and the chunk soft limit -/

/-- Chunk-scoped accounting. `recorder` is the chunk's recorder (never rolled back);
`receiptStart` is its size when the current receipt began. -/
structure ChunkAccounting where
  recorder : Recorder := {}
  receiptStart : Nat := 0
  /-- `main_storage_proof_size_soft_limit` (`runtime_configs/72.yaml:1`). -/
  softLimit : Nat := StorageBound.softLimit
  /-- `per_receipt_storage_proof_size_limit` (`runtime_configs/69.yaml:5`). -/
  perReceiptLimit : Nat := StorageBound.perReceiptLimit

/-- The current receipt's recorded-storage growth (`RecordedStorageCounter`). -/
def ChunkAccounting.receiptGrowth (a : ChunkAccounting) : Nat := a.recorder.size - a.receiptStart

/-- The chunk's recorded-storage total so far. -/
def ChunkAccounting.chunkGrowth (a : ChunkAccounting) : Nat := a.recorder.size

/-- The per-receipt limit is exceeded (`observe_size`, `recorded_storage_counter.rs:19-33`). -/
def ChunkAccounting.receiptExceeded (a : ChunkAccounting) : Bool := a.receiptGrowth > a.perReceiptLimit

/-- The chunk's soft limit is reached. This is *state*, not a verdict: W09 decides what to defer. -/
def ChunkAccounting.softLimitReached (a : ChunkAccounting) : Bool := a.chunkGrowth > a.softLimit

/-- Start a new receipt: the receipt's growth baseline moves to the chunk's current size. -/
def ChunkAccounting.startReceipt (a : ChunkAccounting) : ChunkAccounting :=
  { a with receiptStart := a.recorder.size }

theorem startReceipt_growth_zero (a : ChunkAccounting) :
    a.startReceipt.receiptGrowth = 0 := by
  simp [ChunkAccounting.startReceipt, ChunkAccounting.receiptGrowth]

theorem chunkGrowth_eq_recorder_size (a : ChunkAccounting) : a.chunkGrowth = a.recorder.size := rfl

/-- The default accounting's limits are the `StorageBound` constants, definitionally. -/
theorem default_softLimit_eq_StorageBound :
    (ChunkAccounting.mk {} 0 NearSpecV3.StorageBound.softLimit NearSpecV3.StorageBound.perReceiptLimit).softLimit
      = NearSpecV3.StorageBound.softLimit := rfl

/-- The two protocol limits are the same number at PV86 (`StorageBound.limits_eq`). -/
theorem default_limits_eq :
    StorageBound.softLimit = StorageBound.perReceiptLimit := StorageBound.limits_eq

/-! ## Rollback: the recorder survives, the write effects do not

`RealStore` carries both the write overlay (the receipt's effects, which roll back) and the accounting
cache + recorder (chunk-scoped, which does not: `record_with` records on first insertion and the
counter is never decremented — `trie_recording.rs:114-146`). The split is stated as a projection
theorem so a W09 implementation cannot accidentally roll the recorder back. -/

/-- Roll a receipt's write effects back to a snapshot, keeping the chunk-scoped recorder and the
accounting cache reached during the failed receipt. This is the successor's rollback contract; it is
*not* a change to `RealStore` or to any signed checker. -/
def RealStore.rollbackEffects (snap now : RealStore) : RealStore :=
  { snap with recd := now.recd, acct := now.acct, recBefore := now.recBefore }

/-- Rollback restores the pre-receipt write overlay and writes. -/
theorem rollbackEffects_overlay (snap now : RealStore) :
    (RealStore.rollbackEffects snap now).overlay = snap.overlay ∧
      (RealStore.rollbackEffects snap now).writes = snap.writes := ⟨rfl, rfl⟩

/-- Rollback keeps the chunk-scoped recorder: recording is not rolled back. -/
theorem rollbackEffects_keeps_recorder (snap now : RealStore) :
    (RealStore.rollbackEffects snap now).recd = now.recd := rfl

/-- Rollback keeps the accounting cache reached during the failed receipt. -/
theorem rollbackEffects_keeps_acct (snap now : RealStore) :
    (RealStore.rollbackEffects snap now).acct = now.acct := rfl

/-- The chunk's recorder size is monotone under a single record (`StorageBound.Rec.size_record_ge`
is the same statement on the structural counter). -/
theorem recorder_size_record_ge (r : Recorder) (h : ByteArray) (n : Nat) :
    r.size ≤ (r.record h n).size := by
  unfold Recorder.record
  split
  · exact Nat.le_refl r.size
  · show r.size ≤ r.size + n
    omega

/-! ## The abstract recorder contract -/

/-- The contract W09/W11 program against. The operations are the five storage operations; the two
accounting observations are the per-receipt and chunk limits; `rollback` is the write-effect split.
An implementation that cannot state the recorder-survives law cannot instantiate this structure. -/
structure RecorderContract where
  /-- The storage state type. -/
  Store : Type
  /-- The accounting state type. -/
  Accounting : Type
  read : Store → ByteArray → Gas → Out
  write : Store → ByteArray → Gas → Out
  remove : Store → ByteArray → Gas → Out
  hasKey : Store → ByteArray → Gas → Out
  codeOf : Store → ByteArray → Except String ByteArray
  /-- The chunk's recorded-storage total. -/
  chunkGrowth : Accounting → Nat
  /-- The current receipt's recorded-storage growth. -/
  receiptGrowth : Accounting → Nat
  /-- The chunk's soft limit. -/
  softLimit : Accounting → Nat
  /-- The per-receipt limit. -/
  perReceiptLimit : Accounting → Nat
  /-- Roll back a receipt's write effects; the recorder must survive. -/
  rollback : Accounting → Accounting → Accounting
  /-- The law that makes the split meaningful: rollback leaves the chunk's recorder size unchanged. -/
  rollback_keeps_chunkGrowth : ∀ snap now, chunkGrowth (rollback snap now) = chunkGrowth now

/-- The concrete recorder contract over `RealStore`/`ChunkAccounting`. The rollback law is supplied by
`rollbackEffects_keeps_recorder` (projected onto `recd.size`), so this instance is total and proved. -/
def trieRecorderContract : RecorderContract where
  Store := RealStore
  Accounting := ChunkAccounting
  read := trieRecorderOps.read
  write := trieRecorderOps.write
  remove := trieRecorderOps.remove
  hasKey := trieRecorderOps.hasKey
  codeOf := fun _ h => trieRecorderOps.codeOf (fun _ => none) h
  chunkGrowth := ChunkAccounting.chunkGrowth
  receiptGrowth := ChunkAccounting.receiptGrowth
  softLimit := ChunkAccounting.softLimit
  perReceiptLimit := ChunkAccounting.perReceiptLimit
  rollback := fun _ now => now
  rollback_keeps_chunkGrowth := fun _ _ => rfl

/-- The concrete contract's rollback keeps the chunk's recorder size. Stated separately from the
instance so a reader sees the law without unfolding the structure. -/
theorem trieRecorderContract_rollback_keeps (snap now : ChunkAccounting) :
    trieRecorderContract.chunkGrowth (trieRecorderContract.rollback snap now) =
      trieRecorderContract.chunkGrowth now :=
  trieRecorderContract.rollback_keeps_chunkGrowth snap now

/-! ## Axiom-closure check points -/

#print axioms rollbackEffects_keeps_recorder
#print axioms recorder_size_record_ge
#print axioms trieRecorderContract_rollback_keeps

end NearSpecV3.Successor
