import NearSpecV3.E2E.OvlInv

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# E2E-M11h, item 3: committed value lengths

Lane B's state view needs every value committed in the overlay at a configuration of an accepting
run to be `< 2^24` bytes (`IntakeOk.cur`, `join/StViewE.lean`). This file is the value-length
analogue of `OvlInv.lean`'s pass: the same walk over every overlay operation of the engine's
programs (logged store programs, recorder programs, actions, the Wasm write-back, receipts,
queues, `finalizeStep`), with the invariant

* **`OV t S o`**: every entry `(k, v)` of `o.committed` and of `o.prosp` is **`Good`**: either
  `k` is a key of a **`Hard`** shape (below) or `v` is `none` or `< 2^24` bytes.

`Ovl.set k v` needs `Good (k, some v)` at the write site; `remove` writes `none`; `commit` moves
prospective entries into the committed list; `rollback` drops them. Each write site is closed by
one of:

* **a fixed-size encoding** (`good_tac`): `u32`, `u64`, `encIndices`, `Meta.encode`,
  `encodeGroup`, for the pending-data count, access-key nonces, the global contract nonce, the
  delayed-queue and yield-queue indices, the buffered-receipt group metadata and group entries;
* **a `Hard` key** — the writes whose value carries bytes of an incoming receipt, a transaction,
  the pre-state, the bandwidth-scheduler primitive or the layout, for which this file proves no
  length bound (see `Hard`; two of them are unbounded by the spec, see `Hard`'s docstring);
* **the Wasm write-back** (`functionCallRecordedF`): the call's storage writes, bounded by the
  host's `storage_write` check (`v.size > maxLengthStorageValue = 4 MiB` fails the call before the
  write is recorded, `Wasm/Host.lean`). That the interpreter's recorded writes all passed that
  check is the class **`VmWritesShort`**, a statement about `vmCall` alone (no intake, no run);
  it is not proved here (it needs an invariant over the Wasm interpreter's host calls).

Main results: `reach_vals` (every entry of every overlay reached from `start` is `Good`, given
`VmWritesShort`) and `reach_committed_short` (its committed values at non-`Hard` keys are
`< 2^24` bytes).

Nothing here changes a definition the checker uses.
-/

namespace NearSpecV3.E2E.OvlVal
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution
open NearSpecV3.E2E.OvlInv (keys)
open NearSpecV3.D3 (ofBA toBA)
open NearSpecV3.D3.L4 (kGlobalContractCode Gci)

/-! ## Values and keys -/

/-- A value of the overlay is `none` or shorter than `2^24` bytes (lane B's `okB`). -/
def vok (v : Option Bytes) : Prop := ∀ x, v = some x → x.length < 2 ^ 24

theorem vok_none : vok none := fun _ h => by cases h

theorem vok_some {x : Bytes} (h : x.length < 2 ^ 24) : vok (some x) := by
  intro y hy; cases hy; exact h

/-- **The keys whose values this file does not bound** (the remaining hypothesis of
`IntakeOk`, `join/StViewE.lean`). Each constructor is a write site class whose value carries bytes
that are not of fixed size:

* `acct` (`setAcct`, column 0): `Acct.encode`, whose contract field carries a global contract's
  account id (`useGlobal`, `stateInit` of a receipt) — bounded by `AccountId.valid` /
  `gciValid` of the action, not tracked here.
* `code` (column 1): deployed code, `≤ maxContractSize` by `validBase` of the action (incoming
  receipts: `validReceipt false`; transactions: `TxD2.valid`), not tracked here.
* `ak` (`setAK`, column 2): `AK.encode`, whose function-call permission carries the receiver id
  and method names (`validAddKey`: `≤ 2000` method-name bytes), not tracked here.
* `rdata` (column 3): `encOptBytes x` of a data receipt (`≤ maxReturnedData = 4 MiB` by
  `validReceipt` for incoming and delayed receipts; Wasm yield resumes), not tracked here.
* `ppid` (column 4): the postponed receipt's id `r.rid`, of the receipt's length.
* `pp` (column 6), `yrcpt` (column 12): `r.encode` of a postponed / promise-yield receipt.
  **Unbounded by the spec**: an incoming action receipt passes `validReceipt false`, which does
  not check `r.encode.length` (the `maxReceiptSize` check is for `newMode` only), with up to
  `maxActions = 100` actions of `maxArgs = 4 MiB` arguments each; with an input data id not yet
  received it is stored verbatim at `kPostponed` (`processReceipt`, `.action false`). Five such
  arguments make `r.encode.length > 20 MiB > 2^24`; the witness cap (`maxWitnessChunk` ≈ 75 MB)
  admits it. In nearcore such a receipt is never created (`validate_receipt` in `New` mode at
  creation enforces `max_receipt_size = 4 MiB`), so the bound is a fact about the chain history
  behind the intake's incoming receipts, not about this chunk's run.
* `delayed` (column 7 items), `buf` (column 14): `encodeStoredV1 r gas size` of a delayed /
  buffered receipt (incoming, local or decoded from the pre-state), unbounded as above.
* `data` (column 9): contract data written by `stateInit` (`≤ 4 MiB` per value by `validBase`
  of the action, not tracked here); the Wasm write-back is covered by `VmWritesShort` instead.
* `ytimeout` (column 11): the yield timeout `borshBytes recv ++ did ++ u64 _`, of the receiver
  id's and the Wasm data id's length.
* `bufIdx` (column 13): `encodeBufIdx`, `4 + 24·n` bytes for `n` shards with a buffer (shard ids
  from the layout).
* `bw` (column 15): the bandwidth scheduler's state, the output of the abstract primitive
  `prims.sched`.
* `gcode` (`kGlobalContractCode`): the code of a global contract distribution receipt.
  **Unbounded by the spec**: `validReceipt` accepts every `.distribution` body, and
  `applyDistributionL` stores `d.code` (checked only against its hash) with no length check. -/
inductive Hard : Bytes → Prop
  | acct (a : Bytes) : Hard (kAccount a)
  | code (a : Bytes) : Hard (kCode a)
  | ak (a : Bytes) (pk : PublicKey) : Hard (kAK a pk)
  | rdata (a d : Bytes) : Hard (kReceivedData a d)
  | ppid (a d : Bytes) : Hard (kPostponedId a d)
  | pp (a r : Bytes) : Hard (kPostponed a r)
  | delayed (i : Nat) : Hard (kDelayed i)
  | data (a key : Bytes) : Hard (kDataPrefix a ++ key)
  | ytimeout (i : Nat) : Hard (kYieldTimeout i)
  | yrcpt (a d : Bytes) : Hard (kYieldReceipt a d)
  | bufIdx : Hard kBufIdx
  | buf (s i : Nat) : Hard (kBuf s i)
  | bw : Hard kBw
  | gcode (g : Gci) : Hard (kGlobalContractCode g)

/-- An overlay entry is good: a `Hard` key or a short value. -/
def Good (p : Bytes × Option Bytes) : Prop := Hard p.1 ∨ vok p.2

theorem good_none (k : Bytes) : Good (k, none) := Or.inr vok_none

/-- **The Wasm write-back is short** (not proved here): every write the Wasm interpreter records
in a finished call's real store (`TTN.RealStore.writes`) has a value `< 2^24` bytes. The writes
are pushed by `realSetH` and `realPutH` (`Wasm/Host.lean`) only: `storage_write`, which fails the
call with `ValueLengthExceeded` when `v.size > maxLengthStorageValue = 4 MiB` before
`realSetH … (some v)`; `storage_remove` (`none`); and the promise-yield bookkeeping
(`realPutH`: a one-byte status, the data / yield ids). It is a statement about `vmCall` alone
(no intake, no run); proving it needs an invariant of the interpreter's host-call state. -/
class VmWritesShort : Prop where
  short : ∀ fuelOf cfg code method ctx real s err, vmCall fuelOf cfg code method ctx real =
    .ok (.done s err) → ∀ r, s.real = some r → ∀ kv ∈ r.writes, ∀ v, kv.2 = some v →
      (ofBA v).length < 2 ^ 24

/-! ## Byte lengths of the fixed-size encodings -/

theorem leN_len : ∀ (w x : Nat), (NearSpec.leN w x).length = w
  | 0, _ => rfl
  | w + 1, x => by
    simp only [NearSpec.leN, List.length_cons]
    exact congrArg (fun n => n + 1) (leN_len w (x / 256))

theorem u32_len (x : Nat) : (u32 x).length = 4 := leN_len 4 x
theorem u64_len (x : Nat) : (u64 x).length = 8 := leN_len 8 x
theorem u128_len (x : Nat) : (u128 x).length = 16 := leN_len 16 x
theorem encIndices_len (f n : Nat) : (encIndices f n).length = 16 := by
  simp only [encIndices, List.length_append, u64_len]
theorem metaEncode_len (m : Meta) : m.encode.length = 49 := by
  simp only [Meta.encode, List.length_append, List.length_cons, List.length_nil, u64_len, u128_len]
theorem encodeGroup_len (s g : Nat) : (encodeGroup s g).length = 25 := by
  simp only [encodeGroup, List.length_append, List.length_cons, List.length_nil, u64_len, u128_len]

/-- Close `Good (k, some v)`: a `Hard` key, or a fixed-size value. -/
macro "good_tac" : tactic => `(tactic| first
  | exact Or.inl (Hard.acct _) | exact Or.inl (Hard.code _) | exact Or.inl (Hard.ak _ _)
  | exact Or.inl (Hard.rdata _ _) | exact Or.inl (Hard.ppid _ _) | exact Or.inl (Hard.pp _ _)
  | exact Or.inl (Hard.delayed _) | exact Or.inl (Hard.data _ _) | exact Or.inl (Hard.ytimeout _)
  | exact Or.inl (Hard.yrcpt _ _) | exact Or.inl Hard.bufIdx | exact Or.inl (Hard.buf _ _)
  | exact Or.inl Hard.bw | exact Or.inl (Hard.gcode _)
  | exact Or.inr (vok_some (by simp only [u32_len, u64_len, u128_len, encIndices_len,
      metaEncode_len, encodeGroup_len]; decide)))

/-! ## `kvPut` and `commit` keep good entries -/

theorem mem_of_kvFind {k : Bytes} {v : Option Bytes} :
    ∀ {l : List (Bytes × Option Bytes)}, kvFind k l = some v → (k, v) ∈ l
  | [], h => by cases h
  | (k', v') :: rest, h => by
    unfold kvFind at h
    split at h
    · rename_i hk
      have : k' = k := by simpa using hk
      subst this; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_kvFind h)

theorem mem_kvPut_val (k : Bytes) (v : Option Bytes) :
    ∀ (l : List (Bytes × Option Bytes)) p, p ∈ kvPut k v l → p ∈ l ∨ p = (k, v)
  | [], p, h => by simp only [kvPut, List.mem_singleton] at h; exact Or.inr h
  | (k', v') :: rest, p, h => by
    unfold kvPut at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · rcases mem_kvPut_val k v rest p h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem good_kvPut {k : Bytes} {v : Option Bytes} {l : List (Bytes × Option Bytes)}
    (hl : ∀ p ∈ l, Good p) (hv : Good (k, v)) : ∀ p ∈ kvPut k v l, Good p := by
  intro p hp
  rcases mem_kvPut_val k v l p hp with h | h
  · exact hl p h
  · subst h; exact hv

theorem good_commitFold : ∀ (p c : List (Bytes × Option Bytes)), (∀ x ∈ p, Good x) →
    (∀ x ∈ c, Good x) → ∀ x ∈ OvlInv.commitFold p c, Good x
  | [], _, _, hc => hc
  | (k, v) :: rest, c, hp, hc =>
    good_commitFold rest (kvPut k v c) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (good_kvPut hc (hp _ List.mem_cons_self))

/-! ## The overlay predicate -/

/-- **The value invariant**: every committed and prospective entry is `Good`. (`t` and `S` are
kept from `OvlInv.OG` so that the walk below has the same shape; they are not constrained.) -/
structure OV (t : PTrie) (S : List Bytes) (o : Ovl) : Prop where
  com : ∀ p ∈ o.committed, Good p
  pro : ∀ p ∈ o.prosp, Good p

section ov
variable {t : PTrie} {S : List Bytes}

theorem OV.ofTrie (t : PTrie) : OV t [] (Ovl.ofTrie t) :=
  ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩

theorem OV.set {o : Ovl} (h : OV t S o) (k v : Bytes) (hv : Good (k, some v)) :
    OV t S (o.set k v) := ⟨h.1, good_kvPut h.2 hv⟩
theorem OV.remove {o : Ovl} (h : OV t S o) (k : Bytes) : OV t S (o.remove k) :=
  ⟨h.1, good_kvPut h.2 (good_none k)⟩
theorem OV.rollback {o : Ovl} (h : OV t S o) : OV t S o.rollback := ⟨h.1, fun _ h => by cases h⟩
theorem OV.setAcct {o : Ovl} (h : OV t S o) (a : Bytes) (x : Acct) : OV t S (o.setAcct a x) :=
  OV.set h _ _ (Or.inl (Hard.acct a))
theorem OV.setAK {o : Ovl} (h : OV t S o) (a : Bytes) (pk : PublicKey) (k : AK) :
    OV t S (o.setAK a pk k) := OV.set h _ _ (Or.inl (Hard.ak a pk))
theorem OV.commit {o : Ovl} (h : OV t S o) : OV t S o.commit :=
  ⟨good_commitFold _ _ h.2 h.1, fun _ h => by cases h⟩

theorem OV.foldl {β : Type} {g : Ovl → β → Ovl} (hg : ∀ o b, OV t S o → OV t S (g o b)) :
    ∀ (l : List β) (o : Ovl), OV t S o → OV t S (l.foldl g o)
  | [], _, h => h
  | b :: l, o, h => OV.foldl hg l (g o b) (hg o b h)

/-- A fold whose step needs the element's membership (the Wasm write-back). -/
theorem OV.foldl_mem {β : Type} {g : Ovl → β → Ovl} :
    ∀ (l : List β), (∀ o b, b ∈ l → OV t S o → OV t S (g o b)) →
      ∀ (o : Ovl), OV t S o → OV t S (l.foldl g o)
  | [], _, _, h => h
  | b :: l, hg, o, h => OV.foldl_mem l (fun o' b' hb => hg o' b' (List.mem_cons_of_mem _ hb))
      (g o b) (hg o b List.mem_cons_self h)

theorem OV.afoldl {β : Type} {g : Ovl → β → Ovl} (hg : ∀ o b, OV t S o → OV t S (g o b))
    (l : Array β) (o : Ovl) (h : OV t S o) : OV t S (l.foldl g o) := by
  rw [← Array.foldl_toList]
  exact OV.foldl hg l.toList o h

theorem OV.afoldl_mem {β : Type} {g : Ovl → β → Ovl} (l : Array β)
    (hg : ∀ o b, b ∈ l → OV t S o → OV t S (g o b)) (o : Ovl) (h : OV t S o) :
    OV t S (l.foldl g o) := by
  rw [← Array.foldl_toList]
  exact OV.foldl_mem l.toList (fun o b hb => hg o b (Array.mem_toList_iff.mp hb)) o h

theorem OV.foldl_rs {β : Type} {g : RS → β → RS} (hg : ∀ r b, OV t S r.o → OV t S (g r b).o) :
    ∀ (l : List β) (r : RS), OV t S r.o → OV t S (l.foldl g r).o
  | [], _, h => h
  | b :: l, r, h => OV.foldl_rs hg l (g r b) (hg r b h)

theorem OV.ite {c : Prop} [Decidable c] {a b : Ovl} (ha : OV t S a) (hb : OV t S b) :
    OV t S (if c then a else b) := by
  split <;> assumption

end ov

/-- Close a leaf: an overlay built from overlays satisfying `OV` by the overlay operations; a
write's side condition by `good_tac`. -/
syntax "ov_leaf" : tactic
macro_rules | `(tactic| ov_leaf) => `(tactic| (
  (try dsimp only [RS.setMeta, RS.writeDelayedIdx, ForInStep.value] at *)
  repeat' (first
    | assumption
    | exact True.intro
    | exact OV.ofTrie _
    | good_tac
    | (refine OV.set ?_ _ _ ?_)
    | (refine OV.remove ?_ _)
    | (refine OV.commit ?_)
    | (refine OV.rollback ?_)
    | (refine OV.setAcct ?_ _ _)
    | (refine OV.setAK ?_ _ _ _)
    | (refine OV.foldl (fun _ _ _ => ?_) _ _ ?_)
    | (refine OV.afoldl (fun _ _ _ => ?_) _ _ ?_)
    | (refine OV.foldl_rs (fun _ _ _ => ?_) _ _ ?_)
    | (split <;> (try dsimp only at *))
    | (dsimp only at *))))


/-! ## Logged store programs keep `OV` -/

/-- Close a logged store program by a proved fact (extended below, function by function). -/
syntax "ovl_close" : tactic
macro_rules | `(tactic| ovl_close) => `(tactic| fail "ovl_close")

/-- The walk over a logged store program (`TierO3Inv`'s `lok` with the `OV` leaves). -/
macro "ovlok" : tactic => `(tactic|
  repeat' (first
    | (refine LOk.pure _ ?_; focus (ov_leaf; done))
    | (exact LOk.throw _)
    | (exact LOk.throwThe _)
    | (exact fun _ => SOk.err _)
    | (simp only [pure_bind])
    | ovl_close
    | (show OV _ _ _; ov_leaf; done)
    | ((refine LOk.bind (by ovl_close) fun _ _ => ?_); try dsimp only)
    | ((refine LOk.bind (ite_pure_ov _ _ _ ?_ ?_) fun _ _ => ?_); try dsimp only)
    | ((refine LOk.bind (LOk.tru _) fun _ _ => ?_); try dsimp only)
    | (refine LOk.ite _ (fun _ => ?_) (fun _ => ?_))
    | (dsimp only)
    | (split <;> (try dsimp only))))

section queues
variable (t : PTrie) (S : List Bytes)

theorem ite_pure_ov {c : Prop} [Decidable c] {x : LM RS} (v : RS) (hv : OV t S v.o)
    (hx : LOk (fun y : RS => OV t S y.o) x) :
    LOk (fun y : RS => OV t S y.o) (if c then pure v else x) :=
  LOk.ite _ (fun _ => LOk.pure _ hv) fun _ => hx

theorem groupsPopBackL_ov (rs : RS) (s : Nat) (m : Meta) (h : OV t S rs.o) :
    LOk (fun x : RS × Meta × Option (Nat × Nat) => OV t S x.1.o) (groupsPopBackL rs s m) := by
  unfold groupsPopBackL; ovlok

theorem groupsPushBackL_ov (rs : RS) (s : Nat) (m : Meta) (size gas : Nat) (h : OV t S rs.o) :
    LOk (fun x : RS × Meta => OV t S x.1.o) (groupsPushBackL rs s m size gas) := by
  unfold groupsPushBackL; ovlok

macro_rules | `(tactic| ovl_close) => `(tactic| exact groupsPopBackL_ov _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact groupsPushBackL_ov _ _ _ _ _ _ _ (by assumption))

theorem metaPushedL_ov (rs : RS) (s size gas : Nat) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (metaPushedL rs s size gas) := by
  unfold metaPushedL; ovlok

theorem metaPoppedL_ov (rs : RS) (s size gas : Nat) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (metaPoppedL rs s size gas) := by
  unfold metaPoppedL; ovlok

macro_rules | `(tactic| ovl_close) => `(tactic| exact metaPushedL_ov _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact metaPoppedL_ov _ _ _ _ _ _ (by assumption))

theorem bufferReceiptL_ov (rs : RS) (r : Rcpt) (size gas shard : Nat) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (bufferReceiptL rs r size gas shard) := by
  unfold bufferReceiptL; ovlok

macro_rules | `(tactic| ovl_close) => `(tactic| exact bufferReceiptL_ov _ _ _ _ _ _ _ (by assumption))

theorem forwardOrBufferL_ov (env : Env) (rs : RS) (r : Rcpt) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (forwardOrBufferL env rs r) := by
  unfold forwardOrBufferL; ovlok

theorem forwardOrBufferLWith_ov (pol : QueuePolicy) (env : Env) (rs : RS) (r : Rcpt)
    (h : OV t S rs.o) : LOk (fun x : RS => OV t S x.o) (forwardOrBufferLWith pol env rs r) := by
  unfold forwardOrBufferLWith; ovlok

theorem fwdLoopL_ov (env : Env) (s : Nat) : ∀ fuel i (acc : RS × Nat × List (Nat × Nat)),
    OV t S acc.1.o →
    LOk (fun x : RS × Nat × List (Nat × Nat) => OV t S x.1.o) (fwdLoopL env s fuel i acc)
  | 0, _, _, h => LOk.pure _ h
  | fuel + 1, i, (rs, k, pops), h => by
    unfold fwdLoopL
    dsimp only at h
    ovlok
    all_goals exact fwdLoopL_ov env s fuel _ _ h

theorem fwdLoopLWith_ov (pol : QueuePolicy) (env : Env) (s : Nat) :
    ∀ fuel i (acc : RS × Nat × List (Nat × Nat)), OV t S acc.1.o →
    LOk (fun x : RS × Nat × List (Nat × Nat) => OV t S x.1.o) (fwdLoopLWith pol env s fuel i acc)
  | 0, _, _, h => LOk.pure _ h
  | fuel + 1, i, (rs, k, pops), h => by
    unfold fwdLoopLWith
    dsimp only at h
    ovlok
    all_goals exact fwdLoopLWith_ov pol env s fuel _ _ h

theorem forwardFromBufferToShardL_ov (env : Env) (rs : RS) (s : Nat) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (forwardFromBufferToShardL env rs s) := by
  unfold forwardFromBufferToShardL
  refine LOk.bind (fwdLoopL_ov t S env s _ _ _ h) fun ⟨rs', k, pops⟩ h' => ?_
  dsimp only at h' ⊢
  refine LOk.foldlM _ _ ?_ fun a _ ha => metaPoppedL_ov t S _ _ _ _ ha
  ov_leaf

theorem forwardFromBufferToShardLWith_ov (pol : QueuePolicy) (env : Env) (rs : RS) (s : Nat)
    (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (forwardFromBufferToShardLWith pol env rs s) := by
  unfold forwardFromBufferToShardLWith
  refine LOk.bind (fwdLoopLWith_ov t S pol env s _ _ _ h) fun ⟨rs', k, pops⟩ h' => ?_
  dsimp only at h' ⊢
  refine LOk.foldlM _ _ ?_ fun a _ ha => metaPoppedL_ov t S _ _ _ _ ha
  ov_leaf

theorem forwardFromBufferL_ov (env : Env) (rs : RS) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (forwardFromBufferL env rs) := by
  unfold forwardFromBufferL
  refine LOk.ite _ (fun _ => LOk.throw _) fun _ => ?_
  exact LOk.foldlM (Q := fun x : RS => OV t S x.o) _ _ h
    fun a _ ha => forwardFromBufferToShardL_ov t S _ _ _ ha

theorem forwardFromBufferLWith_ov (pol : QueuePolicy) (env : Env) (rs : RS) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (forwardFromBufferLWith pol env rs) := by
  unfold forwardFromBufferLWith
  refine LOk.ite _ (fun _ => LOk.throw _) fun _ => ?_
  exact LOk.foldlM (Q := fun x : RS => OV t S x.o) _ _ h
    fun a _ ha => forwardFromBufferToShardLWith_ov t S _ _ _ _ ha

theorem forwardFromBufferV3L_ov (ga : Bool) (env : Env) (rs : RS) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (StorageExecution.forwardFromBufferV3L ga env rs) := by
  unfold StorageExecution.forwardFromBufferV3L
  refine LOk.bind (LOk.foldlM (Q := fun x : RS => OV t S x.o) _ _ h fun a _ ha => ?_) fun a ha => ?_
  · split
    · exact forwardFromBufferToShardLWith_ov t S _ _ _ _ ha
    · exact forwardFromBufferToShardL_ov t S _ _ _ ha
  · ovlok

theorem delayPushL_ov (rs : RS) (r : Rcpt) (h : OV t S rs.o) :
    LOk (fun x : RS => OV t S x.o) (delayPushL rs r) := by
  unfold delayPushL; ovlok

theorem delayPopL_ov (env : Env) : ∀ fuel (rs : RS), OV t S rs.o →
    LOk (fun x : RS × Option Rcpt => OV t S x.1.o) (delayPopL env fuel rs)
  | 0, _, h => LOk.pure _ h
  | fuel + 1, rs, h => by
    unfold delayPopL
    ovlok
    all_goals exact delayPopL_ov env fuel _ (by ov_leaf)

theorem delayPopLWith_ov (pol : QueuePolicy) (env : Env) : ∀ fuel (rs : RS), OV t S rs.o →
    LOk (fun x : RS × Option Rcpt => OV t S x.1.o) (delayPopLWith pol env fuel rs)
  | 0, _, h => LOk.pure _ h
  | fuel + 1, rs, h => by
    unfold delayPopLWith
    ovlok
    all_goals exact delayPopLWith_ov pol env fuel _ (by ov_leaf)

macro_rules | `(tactic| ovl_close) => `(tactic| exact forwardOrBufferL_ov _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact forwardOrBufferLWith_ov _ _ _ _ _ _ (by assumption))

theorem processTxD2L_ov (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) (h : OV t S rs.1.o) :
    LOk (fun x : RS × List Bytes => OV t S x.1.o) (processTxD2L env rs tf) := by
  obtain ⟨rs, seen⟩ := rs
  dsimp only at h
  unfold processTxD2L
  ovlok

theorem validatorUpdateL_ov (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts)
    (last : List (Bytes × Nat)) (h : OV t S o) :
    LOk (fun x : Ovl => OV t S x) (validatorUpdateL l own o f last) := by
  unfold validatorUpdateL
  refine LOk.bind (LOk.foldlM (Q := fun x : Ovl => OV t S x) _ _ h fun a _ ha => ?_) fun a ha => ?_
  · ovlok
  · ovlok

theorem schedOvlL_ov (prims : Prims) (ctx : ApplyCtx) (o : Ovl) (h : OV t S o) :
    LOk (fun x : Ovl × SchedOut => OV t S x.1) (schedOvlL prims ctx o) := by
  unfold schedOvlL; ovlok


end queues

section acts
variable (t : PTrie) (S : List Bytes) (c : ActCtx) (st : ActSt) (res : AR) (h : OV t S st.o)
include h

theorem actCreateAccountL_ov : LOk (fun p : ActSt × AR => OV t S p.1.o) (actCreateAccountL c st res) := by
  unfold actCreateAccountL; ovlok
theorem actDeployL_ov (code : Bytes) : LOk (fun p : ActSt × AR => OV t S p.1.o) (actDeployL c st res code) := by
  unfold actDeployL; ovlok
theorem actTransferL_ov (d : Nat) : LOk (fun p : ActSt × AR => OV t S p.1.o) (actTransferL c st res d) := by
  unfold actTransferL; ovlok
theorem actStakeL_ov (s : Nat) (pk : PublicKey) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actStakeL c st res s pk) := by
  unfold actStakeL; ovlok
theorem actAddKeyL_ov (pk : PublicKey) (ak : AK) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actAddKeyL c st res pk ak) := by
  unfold actAddKeyL; ovlok
theorem actDeleteKeyL_ov (pk : PublicKey) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actDeleteKeyL c st res pk) := by
  unfold actDeleteKeyL; ovlok
theorem actDeleteAccountL_ov (ben : Bytes) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actDeleteAccountL c st res ben) := by
  unfold actDeleteAccountL; ovlok
theorem actToGasKeyL_ov (pk : PublicKey) (d : Nat) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actToGasKeyL c st res pk d) := by
  unfold actToGasKeyL; ovlok
theorem actFromGasKeyL_ov (pk : PublicKey) (a : Nat) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actFromGasKeyL c st res pk a) := by
  unfold actFromGasKeyL; ovlok
theorem actDelegateL_ov (d : Delegate) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (actDelegateL c st res d) := by
  unfold actDelegateL; ovlok

end acts


macro_rules | `(tactic| ovl_close) => `(tactic| first
  | exact actCreateAccountL_ov _ _ _ _ _ (by assumption)
  | exact actDeployL_ov _ _ _ _ _ (by assumption) _
  | exact actTransferL_ov _ _ _ _ _ (by assumption) _
  | exact actStakeL_ov _ _ _ _ _ (by assumption) _ _
  | exact actAddKeyL_ov _ _ _ _ _ (by assumption) _ _
  | exact actDeleteKeyL_ov _ _ _ _ _ (by assumption) _
  | exact actDeleteAccountL_ov _ _ _ _ _ (by assumption) _
  | exact actToGasKeyL_ov _ _ _ _ _ (by assumption) _ _
  | exact actFromGasKeyL_ov _ _ _ _ _ (by assumption) _ _
  | exact actDelegateL_ov _ _ _ _ _ (by assumption) _)

section global
variable (t : PTrie) (S : List Bytes)

/-- **The non-call actions keep `OV`** (`ordinaryAction`'s store program). -/
theorem applyActionL_ov (c : ActCtx) (st : ActSt) (a : Act) (h : OV t S st.o) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (applyActionL d2HooksL c st a) := by
  unfold applyActionL; ovlok

theorem useGlobalL_ov (c : ActCtx) (st : ActSt) (res : AR) (g : D3.L4.Gci) (h : OV t S st.o) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (GlobalExecution.useGlobalL c st res g) := by
  unfold GlobalExecution.useGlobalL; ovlok

theorem deployGlobalL_ov (c : ActCtx) (st : ActSt) (res : AR) (d : D3.L4.DeployGlobal)
    (h : OV t S st.o) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (GlobalExecution.deployGlobalL c st res d) := by
  unfold GlobalExecution.deployGlobalL; ovlok

macro_rules | `(tactic| ovl_close) => `(tactic| exact useGlobalL_ov _ _ _ _ _ _ (by assumption))

theorem stateInitL_ov (c : ActCtx) (st : ActSt) (res : AR) (d : D3.L4.Dsi) (h : OV t S st.o) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (GlobalExecution.stateInitL c st res d) := by
  unfold GlobalExecution.stateInitL
  dsimp only
  split
  · refine LOk.bind (useGlobalL_ov t S _ _ _ _ h) fun p hp => ?_
    refine LOk.ite _ (fun _ => ?_) (fun _ => ?_)
    · ovlok
    · split
      · refine LOk.bind (LOk.foldlM (Q := fun x : Ovl × Nat => OV t S x.1) _ _ hp
          fun a _ ha => ?_) fun a ha => ?_
        · ovlok
        · ovlok
      · ovlok
  · ovlok

theorem applyGlobalActionL_ov (c : ActCtx) (st : ActSt) (res : AR) (b : Base) (h : OV t S st.o) :
    LOk (fun p : ActSt × AR => OV t S p.1.o) (GlobalExecution.applyGlobalActionL c st res b) := by
  unfold GlobalExecution.applyGlobalActionL
  split
  · exact deployGlobalL_ov t S _ _ _ _ h
  · exact useGlobalL_ov t S _ _ _ _ h
  · exact stateInitL_ov t S _ _ _ _ h
  · exact LOk.throw _

theorem applyDistributionL_ov (env : Env) (rs : RS) (r : Rcpt) (d : Distribution)
    (h : OV t S rs.o) :
    LOk (fun p : RS × Option Rcpt × Option Bytes => OV t S p.1.o)
      (GlobalExecution.applyDistributionL env rs r d) := by
  unfold GlobalExecution.applyDistributionL
  ovlok

end global

/-! ## Recorder programs keep `OV` (`Post`, `Engine.lean`) -/

theorem Post.tru {α : Type} (x : M α) : Post x (fun _ => True) := fun _ _ _ _ _ => trivial

theorem Post.bind {α β : Type} {Q : α → Prop} {Q' : β → Prop} {x : M α} {f : α → M β}
    (hx : Post x Q) (hf : ∀ a, Q a → Post (f a) Q') : Post (x >>= f) Q' := by
  intro r e b r' h
  rw [M.bind_run] at h
  unfold bindRes at h
  split at h
  · rename_i a r1 heq
    exact hf a (hx r e a r1 heq) r1 e b r' h
  · cases h

theorem Post.throw {α : Type} {Q : α → Prop} (err : String) : Post (throw err : M α) Q := by
  intro r e a r' h; cases h

theorem Post.ite {α : Type} {Q : α → Prop} (c : Prop) [Decidable c] {a b : M α} (ha : c → Post a Q)
    (hb : ¬ c → Post b Q) : Post (if c then a else b) Q := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem Post.logged {α : Type} {Q : α → Prop} {x : LM α} (h : LOk Q x) :
    Post (StorageExecution.logged x) Q := by
  intro r env a r' hx
  rw [logged_run_rr] at hx
  rcases (SRelQ.of_SOk (h env.preRoot)).runR (hGet env.store) with ⟨e, ks, he, _⟩ | ⟨_, hq⟩
  · rw [he] at hx; cases hx
  · revert hx hq
    generalize SM.runR (hGet env.store) (x env.preRoot) = p
    obtain ⟨out, keys⟩ := p
    intro hx hq
    cases out with
    | error e => cases hx
    | ok v =>
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      exact hq _ rfl

theorem Post.tryCatch {α : Type} {Q : α → Prop} {x : M α} {h : String → M α} (hx : Post x Q)
    (hh : ∀ e, Post (h e) Q) : Post (MonadExcept.tryCatch x h) Q := by
  intro r e a r' hr
  have : (MonadExcept.tryCatch x h : M α) r e = Except.tryCatch (x r e) (fun err => h err r e) := rfl
  rw [this] at hr
  cases hxr : x r e with
  | ok p =>
    rw [hxr] at hr
    obtain ⟨a', r1⟩ := p
    simp only [Except.tryCatch, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact hx r e _ _ hxr
  | error err =>
    rw [hxr] at hr
    exact hh err r e a r' hr

theorem Post.foldlM {α β : Type} {Q : α → Prop} (l : List β) (init : α) (hi : Q init) {f : α → β → M α}
    (h : ∀ a b, Q a → Post (f a b) Q) : Post (l.foldlM f init) Q := by
  induction l generalizing init with
  | nil => exact post_pure _ _ hi
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact Post.bind (h init x hi) fun a ha => ih a ha

theorem Post.forIn_list {β σ : Type} {Q : σ → Prop} (l : List β) (init : σ) (hi : Q init)
    {f : β → σ → M (ForInStep σ)} (h : ∀ b s, Q s → Post (f b s) (fun r => Q r.value)) :
    Post (forIn l init f) Q := by
  induction l generalizing init with
  | nil => exact post_pure _ _ hi
  | cons x t ih =>
    rw [List.forIn_cons]
    refine Post.bind (h x init hi) fun r hr => ?_
    cases r with
    | done b => exact post_pure _ _ hr
    | yield b => exact ih b hr

theorem Post.forIn_array {β σ : Type} {Q : σ → Prop} (l : Array β) (init : σ) (hi : Q init)
    {f : β → σ → M (ForInStep σ)} (h : ∀ b s, Q s → Post (f b s) (fun r => Q r.value)) :
    Post (forIn l init f) Q := by
  rw [← Array.forIn_toList]
  exact Post.forIn_list _ _ hi h

theorem Post.forIn_ovl {t : PTrie} {S : List Bytes} {β γ : Type} (l : Array β) (init : MProd Ovl γ)
    (hi : OV t S init.fst) {f : β → MProd Ovl γ → M (ForInStep (MProd Ovl γ))}
    (h : ∀ b s, OV t S s.fst → Post (f b s) (fun r => OV t S r.value.fst)) :
    Post (forIn l init f) (fun s => OV t S s.fst) :=
  Post.forIn_array (Q := fun s => OV t S s.fst) l init hi h

theorem Post.forIn_ovlP {t : PTrie} {S : List Bytes} {β γ : Type} (l : Array β) (init : Ovl × γ)
    (hi : OV t S init.1) {f : β → Ovl × γ → M (ForInStep (Ovl × γ))}
    (h : ∀ b s, OV t S s.1 → Post (f b s) (fun r => OV t S r.value.1)) :
    Post (forIn l init f) (fun s => OV t S s.1) :=
  Post.forIn_array (Q := fun s => OV t S s.1) l init hi h

/-- Close a recorder program by a proved fact (extended below). -/
syntax "mv_close" : tactic
macro_rules | `(tactic| mv_close) => `(tactic| fail "mv_close")

open Lean Elab Tactic Meta in
/-- The head constant of the program of a `Post x Q` goal (`none` for a `let`/`have`, a variable, …). -/
def postHead : TacticM (Option Name) := do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let ty := ty.consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do return none
  let x := (ty.getArg! 1).consumeMData
  return x.getAppFn.constName?

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post x Q` with `x` headed by the constant `n`. -/
elab "pv_head " n:ident : tactic => do
  let some h ← postHead | throwError "pv_head: no head"
  unless h == n.getId.eraseMacroScopes do throwError "pv_head: {h}"

/-- The recorder programs with a proved `OV` fact (`mv_close`): `mv_close` is tried only on these
heads, since unifying a lemma's program with an unrelated head can unfold it (e.g. the Wasm
interpreter behind `vmCall`). -/
def closeHeads : List Lean.Name :=
  [`NearSpecV3.Successor.StorageExecution.logged,
   `NearSpecV3.Successor.StorageExecution.applyAction,
   `NearSpecV3.Successor.StorageExecution.ordinaryAction,
   `NearSpecV3.Successor.StorageExecution.forwardOrBufferR,
   `NearSpecV3.Successor.StorageExecution.emitReceipts,
   `NearSpecV3.Successor.StorageExecution.actionLoop,
   `NearSpecV3.Successor.StorageExecution.applyActionReceipt,
   `NearSpecV3.Successor.StorageExecution.processReceipt,
   `NearSpecV3.Successor.StorageExecution.processWithInstant,
   `NearSpecV3.Successor.StorageExecution.processTxR,
   `NearSpecV3.Successor.StorageExecution.delayPopR,
   `NearSpecV3.Successor.StorageExecution.forwardFromBufferR,
   `NearSpecV3.Successor.StorageExecution.validatorUpdateR,
   `NearSpecV3.Successor.StorageExecution.schedOvlR]

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post x Q` with `x` headed by a program of `closeHeads`. -/
elab "pv_callee" : tactic => do
  let some h ← postHead | throwError "pv_callee: no head"
  unless closeHeads.contains h do throwError "pv_callee: {h}"

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post (x >>= f) Q` with `x` headed by a program of `closeHeads`. -/
elab "pv_bind_callee" : tactic => do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "pv_bind_callee"
  let x := (ty.getArg! 1).consumeMData
  unless x.isAppOfArity ``Bind.bind 6 do throwError "pv_bind_callee: no bind"
  let some h := (x.getArg! 4).consumeMData.getAppFn.constName? | throwError "pv_bind_callee"
  unless closeHeads.contains h do throwError "pv_bind_callee: {h}"

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post x Q` with `x` a `match` application. -/
elab "pv_match" : tactic => do
  let some h ← postHead | throwError "pv_match: no head"
  unless (← isMatcher h) do throwError "pv_match: {h}"

/-- A join point `have jp := v; b jp` of a `do` block, by a specification `Spec` of `jp`: walked
once for `v` and used at every call of `jp` in `b` (zeta-reducing it would copy `v` into every
branch that calls it). -/
theorem Post.have_jp {α F : Type} {Q : α → Prop} (v : F) (b : F → M α) (Spec : F → Prop)
    (hv : Spec v) (hb : ∀ jp, Spec jp → Post (b jp) Q) : Post (b v) Q := hb v hv

open Lean Elab Tactic Meta in
/-- The `OV t S` facts about a join point argument `x` (an overlay, a receipt or action state,
or a pair whose first component is one), for the local `t`, `S`. -/
partial def ovFacts (t S x : Expr) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars (← inferType x))
  if ty.isConstOf ``NearSpecV3.D2.Ovl then
    return #[← mkAppM ``OV #[t, S, x]]
  if ty.isConstOf ``NearSpecV3.D2.RS then
    return #[← mkAppM ``OV #[t, S, ← mkAppM ``NearSpecV3.D2.RS.o #[x]]]
  if ty.isConstOf ``NearSpecV3.D2.ActSt then
    return #[← mkAppM ``OV #[t, S, ← mkAppM ``NearSpecV3.D2.ActSt.o #[x]]]
  if ty.isAppOfArity ``Prod 2 then
    return ← ovFacts t S (← mkAppM ``Prod.fst #[x])
  if ty.isAppOfArity ``MProd 2 then
    return ← ovFacts t S (← mkAppM ``MProd.fst #[x])
  return #[]

open Lean Elab Tactic Meta in
/-- On `Post (let x := v; b) Q`: a value `x` is substituted; a join point (a function into the
monad) is replaced by its specification (`Post.have_jp`): every call with arguments satisfying
their `OV t S` facts satisfies `Q`. Two goals: the specification of `v`, and `b` under it. -/
elab "pv_let" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "pv_let"
  let α := ty.getArg! 0
  let Q := ty.getArg! 2
  let .letE n T v b _ := (ty.getArg! 1).consumeMData | throwError "pv_let: no let"
  let isJp ← forallTelescope T fun xs r => do
    if xs.isEmpty then return false
    let r := r.consumeMData
    return r.isAppOf ``NearSpecV3.Successor.StorageExecution.M || r.isAppOf ``StateT
  if !isJp then
    let g' ← g.replaceTargetDefEq (mkApp3 ty.getAppFn α (b.instantiate1 v) Q)
    replaceMainGoal [g']
    return
  let lctx ← getLCtx
  let some tD := lctx.findFromUserName? `t | throwError "pv_let: no t"
  let some SD := lctx.findFromUserName? `S | throwError "pv_let: no S"
  let specOf (jp : Expr) : MetaM Expr := forallTelescope T fun xs _ => do
    let mut facts : Array Expr := #[]
    for x in xs do
      facts := facts ++ (← ovFacts tD.toExpr SD.toExpr x)
    let post ← mkAppM ``NearSpecV3.E2E.Post #[mkAppN jp xs, Q]
    let inner ← facts.foldrM (fun f acc => mkArrow f acc) post
    mkForallFVars xs inner
  let spec ← withLocalDeclD n T fun jp => do mkLambdaFVars #[jp] (← specOf jp)
  let hv ← mkFreshExprSyntheticOpaqueMVar (← specOf v)
  let hbTy ← withLocalDeclD n T fun jp => do
    mkForallFVars #[jp] (← mkArrow (← specOf jp)
      (← mkAppM ``NearSpecV3.E2E.Post #[b.instantiate1 jp, Q]))
  let hb ← mkFreshExprSyntheticOpaqueMVar hbTy
  let bl := Expr.lam n T b .default
  g.assign (← mkAppOptM ``Post.have_jp #[α, T, Q, v, bl, spec, hv, hb])
  replaceMainGoal [hv.mvarId!, hb.mvarId!]

open Lean Elab Tactic Meta in
/-- On `Post (jp a…) Q` with `jp` a local join point: apply its specification (left as fact
goals). -/
elab "pv_jpcall" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "pv_jpcall"
  let f := (ty.getArg! 1).consumeMData.getAppFn
  unless f.isFVar do throwError "pv_jpcall: not a local"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ok ← forallTelescope d.type fun _ c => do
      let c := c.consumeMData
      return c.isAppOfArity ``NearSpecV3.E2E.Post 3 && (c.getArg! 1).getAppFn == f
    if ok then
      let gs ← g.apply d.toExpr
      replaceMainGoal gs
      return
  throwError "pv_jpcall: no specification"

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is syntactically a `∀` (not a `Post` that unfolds to one). -/
elab "pv_guard_forall" : tactic => do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isForall do throwError "pv_guard_forall"

/-! The walk is a set of small `macro_rules` (one alternative each, tried latest first): large
nested tactic quotations are slow to compile. -/

/-- `mvwalk` on a `pure` leaf. -/
syntax "mvwalk_pure" : tactic
macro_rules | `(tactic| mvwalk_pure) => `(tactic| (refine post_pure _ _ ?_; exact True.intro))
macro_rules | `(tactic| mvwalk_pure) => `(tactic| (refine post_pure _ _ ?_; focus ((show OV _ _ _); ov_leaf; done)))
macro_rules | `(tactic| mvwalk_pure) => `(tactic| (refine post_pure _ _ ?_; focus (ov_leaf; done)))

/-- `mvwalk` on a bind (`>>=`). -/
syntax "mvwalk_bind" : tactic
/-- Any other head: no fact on its value. -/
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Post.tru _) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : ActSt × AR => OV t S x.1.o) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : RS × _ => OV t S x.1.o) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : RS => OV t S x.o) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : Ovl => OV t S x) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : Ovl × _ => OV t S x.1) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Post.foldlM (Q := fun x : Ovl × _ => OV t S x.1) _ _ ?_ fun _ _ _ => ?_) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Post.forIn_ovlP (t := t) (S := S) _ _ ?_ fun _ _ _ => ?_) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mvwalk_bind) => `(tactic| ((refine Post.bind (Post.forIn_ovl (t := t) (S := S) _ _ ?_ fun _ _ _ => ?_) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
/-- A proved head (`mv_close`). -/
macro_rules | `(tactic| mvwalk_bind) => `(tactic| (pv_bind_callee; (refine Post.bind (by mv_close) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
/-- A `pure` head. -/
macro_rules | `(tactic| mvwalk_bind) => `(tactic| simp (config := { zeta := false }) only [pure_bind])

/-- One step of the walk over a recorder program, dispatching on the program's head. -/
syntax "mvwalk1" : tactic
macro_rules | `(tactic| mvwalk1) => `(tactic| dsimp (config := { zeta := false }) only)
macro_rules | `(tactic| mvwalk1) => `(tactic| pv_jpcall)
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_guard_forall; intro))
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_callee; mv_close))
macro_rules | `(tactic| mvwalk1) => `(tactic| ((show OV _ _ _); ov_leaf; done))
macro_rules | `(tactic| mvwalk1) => `(tactic| pv_let)
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_match; split <;> (try (dsimp (config := { zeta := false }) only))))
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_head Bind.bind; mvwalk_bind))
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_head MonadExcept.tryCatch; refine Post.tryCatch ?_ fun _ => ?_))
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_head ite; refine Post.ite _ (fun _ => ?_) (fun _ => ?_)))
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_head MonadExcept.throw; exact Post.throw _))
macro_rules | `(tactic| mvwalk1) => `(tactic| (pv_head Pure.pure; mvwalk_pure))

/-- **The walk over a recorder program** (the overlay predicate's parameters are the local `t`,
`S`). -/
macro "mvwalk" : tactic => `(tactic| repeat' mvwalk1)

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.logged; exact Post.logged (by ovl_close)))
macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.validatorUpdateR; exact Post.logged (by ovl_close)))
macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.schedOvlR; exact Post.logged (by ovl_close)))
macro_rules | `(tactic| ovl_close) => `(tactic| exact applyGlobalActionL_ov _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact applyDistributionL_ov _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact processTxD2L_ov _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact delayPushL_ov _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact delayPopL_ov _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact delayPopLWith_ov _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact forwardFromBufferL_ov _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact forwardFromBufferLWith_ov _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact forwardFromBufferV3L_ov _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact validatorUpdateL_ov _ _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ovl_close) => `(tactic| exact schedOvlL_ov _ _ _ _ _ (by assumption))

section rec
variable (t : PTrie) (S : List Bytes)

theorem ordinaryAction_ov (c : ActCtx) (st : ActSt) (a : Act) (h : OV t S st.o) :
    Post (ordinaryAction c st a) (fun p : ActSt × AR => OV t S p.1.o) := by
  unfold ordinaryAction
  refine Post.bind (Post.logged (applyActionL_ov t S c st a h)) fun p hp => ?_
  mvwalk

theorem applyGlobal_ov (ga : Bool) (c : ActCtx) (st : ActSt) (a : Act) (b : Base) (h : OV t S st.o) :
    Post (applyGlobal ga c st a b) (fun p : ActSt × AR => OV t S p.1.o) := by
  unfold applyGlobal
  mvwalk

end rec

/-! From here on the Wasm write-back is in scope: `VmWritesShort` is assumed. -/
variable [VmWritesShort]
set_option linter.unusedSectionVars false

/-- What a Wasm call's result says about its recorded writes (`VmWritesShort`). -/
def VmOut : Run → Prop
  | .done s _ => ∀ r, s.real = some r → ∀ kv ∈ r.writes, ∀ v, kv.2 = some v →
      (ofBA v).length < 2 ^ 24
  | .line _ => True

theorem post_vmCall (fuelOf : NearCfg → Nat → Nat) (cfg : NearCfg) (code : ByteArray)
    (method : String) (ctx : CallCtx) (real : TTN.RealStore) :
    Post (StorageExecution.liftE (vmCall fuelOf cfg code method ctx real)) VmOut := by
  intro r e a r' h
  unfold StorageExecution.liftE at h
  cases hv : vmCall fuelOf cfg code method ctx real with
  | error err => rw [hv] at h; cases h
  | ok run =>
    rw [hv] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases run with
    | line l => exact True.intro
    | done s err => exact VmWritesShort.short fuelOf cfg code method ctx real s err hv

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post (liftE (vmCall …) >>= f) Q`. -/
elab "pv_bind_vm" : tactic => do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "pv_bind_vm"
  let x := (ty.getArg! 1).consumeMData
  unless x.isAppOfArity ``Bind.bind 6 do throwError "pv_bind_vm: no bind"
  let y := (x.getArg! 4).consumeMData
  unless y.isAppOfArity ``NearSpecV3.Successor.StorageExecution.liftE 2 do throwError "pv_bind_vm"
  unless (y.getArg! 1).consumeMData.isAppOf ``NearSpecV3.Successor.StorageExecution.vmCall do
    throwError "pv_bind_vm: not vmCall"

/-- The Wasm call: its result satisfies `VmOut`. -/
macro_rules | `(tactic| mvwalk_bind) => `(tactic| (pv_bind_vm; (refine Post.bind (post_vmCall _ _ _ _ _ _) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))

/-- The write-back fold of a finished call (`match s.real with …`) keeps `OV`. -/
theorem writeBack_ov {t : PTrie} {S : List Bytes} {o : Ovl} (h : OV t S o) (s : St)
    (err : Option String) (hvm : VmOut (.done s err)) :
    OV t S (match s.real with
      | some r => r.writes.foldl (fun (o : Ovl) (x : ByteArray × Option ByteArray) =>
          match x.2 with
          | some v => o.set (ofBA x.1) (ofBA v)
          | none => o.remove (ofBA x.1)) o
      | none => o) := by
  split
  · rename_i r hr
    refine OV.afoldl_mem _ (fun o' kv hkv ho => ?_) _ h
    split
    · rename_i v hv
      exact OV.set ho _ _ (Or.inr (vok_some (hvm r hr kv hkv v hv)))
    · exact OV.remove ho _
  · exact h

section rec5
variable (t : PTrie) (S : List Bytes)

theorem functionCallRecordedF_ov (fl : Flags) (fuelOf : NearCfg → Nat → Nat) (cfg : NearCfg)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) (h : OV t S st.o) :
    Post (functionCallRecordedF fl fuelOf cfg c st ar b) (fun p : ActSt × AR => OV t S p.1.o) := by
  unfold functionCallRecordedF
  mvwalk
  all_goals first
    | exact writeBack_ov h _ _ ‹VmOut (.done _ _)›
    | (refine post_pure _ _ ?_; exact writeBack_ov h _ _ ‹VmOut (.done _ _)›)

theorem applyAction_ov (fl : Flags) (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act)
    (h : OV t S st.o) :
    Post (StorageExecution.applyAction fl cfg c st a) (fun p : ActSt × AR => OV t S p.1.o) := by
  unfold StorageExecution.applyAction
  split
  · mvwalk
    all_goals exact functionCallRecordedF_ov t S _ _ _ _ _ _ _ h
  · exact applyGlobal_ov t S _ _ _ _ _ h
  · exact applyGlobal_ov t S _ _ _ _ _ h
  · exact applyGlobal_ov t S _ _ _ _ _ h
  · exact ordinaryAction_ov t S _ _ _ h

end rec5

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.applyAction; exact applyAction_ov _ _ _ _ _ _ _ (by assumption)))
macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.ordinaryAction; exact ordinaryAction_ov _ _ _ _ _ (by assumption)))

section rec6
variable (t : PTrie) (S : List Bytes)

theorem actionLoop_ov (fl : Flags) (hooks : NearCfg) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR), OV t S acc.1.o →
      Post (StorageExecution.actionLoop fl hooks env r a inputs deployed attempted i acts acc)
        (fun p : ActSt × AR => OV t S p.1.o)
  | _, [], acc, h => by unfold StorageExecution.actionLoop; exact post_pure _ _ h
  | i, act :: rest, (st, res), h => by
    unfold StorageExecution.actionLoop
    dsimp only at h
    mvwalk
    all_goals exact actionLoop_ov fl hooks env r a inputs deployed attempted _ rest _ (by ov_leaf)

theorem forwardOrBufferR_ov (ga : Bool) (env : Env) (rs : RS) (r : Rcpt) (h : OV t S rs.o) :
    Post (forwardOrBufferR ga env rs r) (fun x : RS => OV t S x.o) := by
  unfold forwardOrBufferR; mvwalk

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.forwardOrBufferR; exact forwardOrBufferR_ov _ _ _ _ _ _ (by assumption)))


theorem emitReceipts_ov (ga : Bool) (env : Env) (parent : Bytes) :
    ∀ (rs : RS) (k : Nat) (l : List Rcpt), OV t S rs.o →
      Post (StorageExecution.emitReceipts ga env parent rs k l) (fun x : RS × List Bytes => OV t S x.1.o)
  | rs, _, [], h => by unfold StorageExecution.emitReceipts; exact post_pure _ _ h
  | rs, k, nr :: rest, h => by
    unfold StorageExecution.emitReceipts
    dsimp only
    refine Post.ite _ (fun _ => ?_) (fun _ => ?_)
    · simp only [pure_bind]
      exact Post.bind (emitReceipts_ov ga env parent _ (k + 1) rest h) fun p hp => post_pure _ _ hp
    · exact Post.bind (forwardOrBufferR_ov t S _ _ _ _ h) fun rs' h' =>
        Post.bind (emitReceipts_ov ga env parent rs' (k + 1) rest h') fun p hp => post_pure _ _ hp

end rec6

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.emitReceipts; exact emitReceipts_ov _ _ _ _ _ _ _ _ (by assumption)))
macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.actionLoop; exact actionLoop_ov _ _ _ _ _ _ _ _ _ _ _ _ _ (by first | assumption | ov_leaf)))

section rec7
variable (t : PTrie) (S : List Bytes)

theorem applyActionReceipt_ov (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (a : ActionR) (h : OV t S rs.o) :
    Post (StorageExecution.applyActionReceipt fl hooks env rs r a)
      (fun x : RS × OutD1 × Nat => OV t S x.1.o) := by
  unfold StorageExecution.applyActionReceipt
  mvwalk


end rec7
macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.applyActionReceipt; exact applyActionReceipt_ov _ _ _ _ _ _ _ _ (by first | assumption | ov_leaf)))

section rec8
variable (t : PTrie) (S : List Bytes)

theorem processReceipt_ov (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (h : OV t S rs.o) :
    Post (StorageExecution.processReceipt fl hooks env rs r)
      (fun x : RS × Option (OutD1 × Nat) => OV t S x.1.o) := by
  unfold StorageExecution.processReceipt
  mvwalk

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.processReceipt; exact processReceipt_ov _ _ _ _ _ _ _ (by assumption)))

theorem processWithTotals_ov (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (h : OV t S rs.o) :
    Post (StorageExecution.processWithTotals fl hooks env rs r) (fun x : RS => OV t S x.o) := by
  unfold StorageExecution.processWithTotals
  mvwalk

theorem drain_ov (fl : Flags) (hooks : NearCfg) (env : Env) : ∀ (fuel : Nat) (rs : RS), OV t S rs.o →
    Post (StorageExecution.processWithInstant.drain fl hooks env fuel rs) (fun x : RS => OV t S x.o)
  | 0, _, _ => by unfold StorageExecution.processWithInstant.drain; exact Post.throw _
  | f + 1, rs, h => by
    unfold StorageExecution.processWithInstant.drain
    split
    · exact post_pure _ _ h
    · exact Post.bind (processWithTotals_ov t S fl hooks env _ _ ⟨h.1, h.2⟩) fun rs' h' =>
        drain_ov fl hooks env f rs' h'

theorem processWithInstant_ov (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (h : OV t S rs.o) :
    Post (StorageExecution.processWithInstant fl hooks env rs r) (fun x : RS => OV t S x.o) := by
  unfold StorageExecution.processWithInstant
  exact Post.bind (processWithTotals_ov t S fl hooks env rs r h) fun rs' h' =>
    drain_ov t S fl hooks env _ rs' h'

end rec8

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.processWithInstant; exact processWithInstant_ov _ _ _ _ _ _ _ (by first | assumption | ov_leaf)))

section eng
variable (t : PTrie) (S : List Bytes)

theorem processTxR_ov (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) (h : OV t S rs.1.o) :
    Post (processTxR env rs tf) (fun x : RS × List Bytes => OV t S x.1.o) := by
  unfold processTxR
  refine Post.bind (Post.logged (processTxD2L_ov t S env rs tf h)) fun p hp => ?_
  mvwalk

end eng

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.processTxR; exact processTxR_ov _ _ _ _ _ (by assumption)))
/-! ## One machine step -/

open NearSpecV3.E2E.OvlInv (ovlOfPos)

/-- **What a step reaches**: an overlay satisfying `OV t S`, or a final output. -/
def PV (t : PTrie) (S : List Bytes) : EPos → Prop
  | .start => False
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs => OV t S rs.o
  | .done _ => True

section steps
variable (t : PTrie) (S : List Bytes)

theorem raceCheck_post (out : MainOutD2) (Q : MainOutD2 → Prop) (h : Q out) :
    Post (raceCheck out) Q := by
  unfold raceCheck
  exact Post.bind (Post.tru _) fun _ _ => Post.ite _ (fun _ => Post.throw _) fun _ => post_pure _ _ h


theorem finalizeStep_ov (env : Env) (yf yn : Nat) (rs : RS) (i : Nat) :
    Post (finalizeStep env yf yn (rs, i)) (fun _ : MainOutD2 => True) := Post.tru _

end steps

section steps2
variable (t : PTrie) (S : List Bytes)

theorem delayPopR_ov (ga : Bool) (env : Env) (fuel : Nat) (rs : RS) (h : OV t S rs.o) :
    Post (delayPopR ga env fuel rs) (fun x : RS × Option Rcpt => OV t S x.1.o) := by
  unfold delayPopR; mvwalk

theorem forwardFromBufferR_ov (ga : Bool) (env : Env) (rs : RS) (h : OV t S rs.o) :
    Post (forwardFromBufferR ga env rs) (fun x : RS => OV t S x.o) := by
  unfold forwardFromBufferR; mvwalk

end steps2

macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.delayPopR; exact delayPopR_ov _ _ _ _ _ _ (by assumption)))
macro_rules | `(tactic| mv_close) => `(tactic| (pv_head NearSpecV3.Successor.StorageExecution.forwardFromBufferR; exact forwardFromBufferR_ov _ _ _ _ _ (by assumption)))

section steps2b
variable (t : PTrie) (S : List Bytes)

theorem localsBody_ov (fl : Flags) (hooks : NearCfg) (env : Env) (dec : Bytes → Except String Rcpt)
    (rs : RS) (r : Rcpt) (h : OV t S rs.o) :
    Post (localsBody fl hooks env dec rs r) (fun x : RS => OV t S x.o) := by
  unfold localsBody
  refine Post.bind (Post.tru _) fun _ _ => ?_
  refine Post.ite _ (fun _ => Post.logged (delayPushL_ov t S rs r h)) fun _ => ?_
  exact Post.bind (Post.tru _) fun _ _ => processWithInstant_ov t S _ _ _ _ _ h

theorem incomingBody_ov (fl : Flags) (hooks : NearCfg) (env : Env) (dec : Bytes → Except String Rcpt)
    (rs : RS) (r : Rcpt) (h : OV t S rs.o) :
    Post (incomingBody fl hooks env dec rs r) (fun x : RS => OV t S x.o) := by
  unfold incomingBody
  refine Post.ite _ (fun _ => Post.throw _) fun _ => ?_
  refine Post.bind (Post.tru _) fun _ _ => ?_
  refine Post.ite _ (fun _ => Post.logged (delayPushL_ov t S rs r h)) fun _ => ?_
  exact Post.bind (Post.tru _) fun _ _ => processWithInstant_ov t S _ _ _ _ _ h

end steps2b
section machine0
variable (t : PTrie) (S : List Bytes)

theorem delayedK_ov (fl : Flags) (hooks : NearCfg) (env : Env) (f : Nat) (rs : RS) (h : OV t S rs.o) :
    Post (delayedK fl hooks env (fun rs => pure (EPos.delayed 0 rs)) (fun rs => pure (EPos.delayed f rs)) rs)
      (PV t S) := by
  unfold delayedK; mvwalk

theorem yieldK_ov (ga : Bool) (env : Env) (yf yn f : Nat) (rs : RS) (i k : Nat) (h : OV t S rs.o) :
    Post (yieldK ga env yn (fun p => pure (EPos.yields yf yn 0 p.2 0 p.1))
      (fun p => pure (EPos.yields yf yn f p.2.1 p.2.2 p.1)) rs i k) (PV t S) := by
  unfold yieldK; mvwalk

end machine0

section machine
variable (S : List Bytes)

/-- **One step keeps `PV`** from every position other than `start`. -/
theorem stepM_pv (P : Prog) (p : EPos) (hp : PV P.t S p) : Post (stepM P p) (PV P.t S) := by
  cases p with
  | start => exact hp.elim
  | txs rest acc rs =>
    cases rest with
    | nil =>
      exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons x rest =>
      exact Post.bind (processTxR_ov P.t S _ _ _ hp) fun q hq => post_pure _ _ hq
  | locals rest rs =>
    cases rest with
    | nil => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons r rest =>
      exact Post.bind (localsBody_ov P.t S _ _ _ _ _ _ hp) fun q hq => post_pure _ _ hq
  | delayed fuel rs =>
    cases fuel with
    | zero => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | succ f =>
      exact delayedK_ov P.t S _ _ _ f rs hp
  | incoming rest rs =>
    cases rest with
    | nil => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons r rest =>
      exact Post.bind (incomingBody_ov P.t S _ _ _ _ _ _ hp) fun q hq => post_pure _ _ hq
  | yields yf yn fuel i k rs =>
    cases fuel with
    | zero =>
      exact Post.bind (Post.bind (finalizeStep_ov _ _ _ _ _) fun out hout =>
        raceCheck_post out _ hout) fun out hout => post_pure _ _ hout
    | succ f =>
      exact yieldK_ov P.t S _ _ yf yn f rs i k hp
  | done out => exact post_pure _ _ hp

end machine
/-- The first step (`preludeK`): the overlay starts as `Ovl.ofTrie P.t`. -/
theorem preludeK_pv (t : PTrie) (fl : Flags) (prims : Prims) (env : Env)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (cong : Congestion)
    (txs : List (TxD2 × Bool)) :
    Post (preludeK fl prims env t vu props cong fun rs => pure (EPos.txs txs [] rs)) (PV t []) := by
  let S : List Bytes := []
  show Post _ (PV t S)
  have h0 : OV t S (Ovl.ofTrie t) := OV.ofTrie t
  unfold preludeK
  mvwalk

theorem start_pv (P : Prog) : Post (stepM P .start) (PV P.t []) :=
  preludeK_pv P.t P.fl P.prims P.env P.vu P.props P.cong P.txs

theorem PV.of_ovl {t : PTrie} {S : List Bytes} {p : EPos} {o : Ovl} (ho : ovlOfPos p = some o)
    (h : OV t S o) : PV t S p := by
  cases p <;> simp only [ovlOfPos, reduceCtorEq, Option.some.injEq] at ho <;> subst ho <;> exact h

theorem PV.og {t : PTrie} {S : List Bytes} {p : EPos} {o : Ovl} (ho : ovlOfPos p = some o)
    (h : PV t S p) : OV t S o := by
  cases p <;> simp only [ovlOfPos, reduceCtorEq, Option.some.injEq] at ho <;> subst ho <;> exact h

theorem estep_post {P : Prog} {c c' : EConf} {Q : EPos → Prop} (hq : Post (stepM P c.pos) Q)
    (h : estep P c = .ok c') : Q c'.pos := by
  unfold estep at h
  split at h
  · rename_i p r heq
    cases h
    exact hq _ _ _ _ heq
  · cases h

/-- **Along any run, `PV` is kept** (from a position other than `start`). -/
theorem esteps_pv (P : Prog) (S : List Bytes) {a b : EConf} (h : ESteps P a b)
    (ha : PV P.t S a.pos) : PV P.t S b.pos := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (estep_post (stepM_pv S P _ ha) hs)

/-- **Every configuration reached from `start`** is `start` or satisfies `PV P.t []`. -/
theorem reach_pv (P : Prog) {a b : EConf} (h : ESteps P a b)
    (ha : a.pos = .start ∨ PV P.t [] a.pos) : b.pos = .start ∨ PV P.t [] b.pos := by
  induction h with
  | refl => exact ha
  | @step a b c hs _ ih =>
    apply ih
    right
    rcases ha with ha | ha
    · obtain ⟨pos, r⟩ := a
      simp only at ha
      subst ha
      exact estep_post (start_pv P) hs
    · exact estep_post (stepM_pv [] P _ ha) hs

/-- **The value invariant along every run**: every entry (committed or prospective) of every
overlay reached from `start` is `Good`. -/
theorem reach_vals [VmWritesShort] (P : Prog) (r0 : Recording) {c : EConf} {o : Ovl}
    (h : ESteps P ⟨.start, r0⟩ c) (ho : ovlOfPos c.pos = some o) : OV P.t [] o := by
  rcases reach_pv P h (Or.inl rfl) with hs | hp
  · rw [hs] at ho; cases ho
  · exact PV.og ho hp

/-- **Committed values are short** at every key that is not `Hard`. -/
theorem reach_committed_short [VmWritesShort] (P : Prog) (r0 : Recording) {c : EConf} {o : Ovl}
    (h : ESteps P ⟨.start, r0⟩ c) (ho : ovlOfPos c.pos = some o) (k : Bytes) (hk : ¬ Hard k)
    (v : Option Bytes) (hv : kvFind k o.committed = some v) : vok v := by
  have hm : (k, v) ∈ o.committed := mem_of_kvFind hv
  rcases (reach_vals P r0 h ho).com _ hm with h' | h'
  · exact absurd h' hk
  · exact h'

#print axioms OV.commit
#print axioms post_vmCall
#print axioms writeBack_ov
#print axioms functionCallRecordedF_ov
#print axioms processReceipt_ov
#print axioms stepM_pv
#print axioms start_pv
#print axioms reach_vals
#print axioms reach_committed_short

end NearSpecV3.E2E.OvlVal
