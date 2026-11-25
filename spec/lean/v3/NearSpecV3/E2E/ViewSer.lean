import NearSpecV3.E2E.ViewE

set_option linter.unusedVariables false

/-!
# E2E-M11i, item 3: serialisers for lane E's view components (`ViewSer`)

`ViewE.lean` takes the prefix-free serialisers (`Ser`, `StEnc.lean`) of `Intake`, `GFin`,
`ChunkInner`, `Outputs`, `VmQ = CallArgs` and `Run` as instance arguments. This file builds the
`Ser` closure of these types (and of `Prepared`, `EntK`, lane A's `encRest` needs), in the style of
`StEnc.lean`: a structure maps to the tuple of its fields, a small inductive to a nested `Sum`, and
`Instr` (47 constructors) / `ConstE` to a `(tag, arguments)` pair with a left inverse.

New base instances: `UInt32`, `UInt64` (their `toNat`), `Fin n` (its value), `Array α` (its list),
`HStore` (the tree itself, node by node, as `implEnc`).

## The function field: `TTN.RealStore.store`

`TTN.RealStore.store : TTN.Store = ByteArray → Option ByteArray` is a function. No injective map
from it into `Bytes` exists (`no_ser_store`, a Cantor argument: it would give an injection
`(Bytes → Bool) → Bytes`). Every type that contains a `RealStore` therefore has **no** `Ser`
instance, and none can be given without changing the type or the view:

* `TTN.RealStore` (field `store`), `Wasm.St` (field `real : Option RealStore`), `Wasm.Res`,
  `Wasm.Run` (`done s`), `CallCut.CallConf` (`ent … (r : Res) …`, `fin (r : Run)`),
  `CallCut.CallArgs` (field `real : RealStore`) — so `VmQ`, `VmV`, `vmDE` and lane A's
  `WRest` (`air q p k s`, `other (q, w)`) are blocked.

What *is* given for them: `Ser` for every other field type (`NearCfg`, `CallCtx`, `Gas`, `Val`,
`Frame`, `Label`, `PRes`, `PromiseV`, `MAct`, `Prepared`, `EntK`, …), and `RealStore` minus its
`store` field (`encRS`, `encRS_pf_mod`: injective on stores with the same `store` function), and
**store-blind encoders** of `St`, `Res`, `Run`, `CallArgs`, `CallConf` (`stN`, `resN`, `runN`,
`argsN`, `confN` into serialisable tuples, injective modulo `strip…` = every store function
replaced by `blankStore`), with the tape-entry encoder `encQRN` (`encQRN_pf_mod`). Binding the
stores themselves is the parent's decision (in the honest run they are a function of the context
component's `Env.store`, `CutW.lean`'s `real`).

`ctxDEc`, `outDEc` (with `coll_ctxDEc`, `coll_outDEc`) are `ViewE.ctxDE` / `ViewE.outDE` with the
instances resolved. `viewEc` is **not** given: `ViewE.viewE` needs `Ser VmQ` and `Ser Run`.

## Root instances

`Ser Intake`, `Ser GFin`, `Ser ChunkInner`, `Ser Outputs` (the context and output components:
`ctxDE`, `outDE`), `Ser Wasm.Prepared`, `Ser CallCut.EntK`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NearSpecV3.E2E.Enc
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd

/-! ## Base instances -/

instance : Ser UInt32 := Ser.ofInj (fun x : UInt32 => x.toNat) (fun _ _ h => UInt32.toNat_inj.mp h)
instance : Ser UInt64 := Ser.ofInj (fun x : UInt64 => x.toNat) (fun _ _ h => UInt64.toNat_inj.mp h)
instance {n : Nat} : Ser (Fin n) := Ser.ofInj (fun x : Fin n => x.val) (fun _ _ h => Fin.ext h)
instance {α : Type} [Ser α] : Ser (Array α) :=
  Ser.ofInj (fun x : Array α => x.toList) (fun _ _ h => Array.toList_inj.mp h)

/-- A serialiser through a map with a left inverse (for wide inductives: `cases` on one value
instead of on pairs). -/
@[instance_reducible] def Ser.ofLeftInv {α β : Type} [Ser β] (g : α → β) (d : β → Option α)
    (hd : ∀ a, d (g a) = some a) : Ser α :=
  Ser.ofInj g (fun a b h => Option.some.inj ((hd a).symm.trans ((congrArg d h).trans (hd b))))

/-! ## The recorded-storage tree `HStore` -/

def hsEnc : HStore → Bytes
  | .tip => [0]
  | .node k v l r => 1 :: (Ser.enc k ++ Ser.enc v ++ hsEnc l ++ hsEnc r)

theorem hsEnc_pf : PF hsEnc := by
  intro t
  induction t with
  | tip =>
    intro t' r r' h
    cases t' with
    | tip => exact ⟨rfl, by simpa [hsEnc] using h⟩
    | node => simp [hsEnc] at h
  | node k v l rt ihl ihr =>
    intro t' r r' h
    cases t' with
    | tip => simp [hsEnc] at h
    | node k' v' l' rt' =>
      simp only [hsEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h
      obtain ⟨rfl, h2⟩ := Ser.pf _ _ _ _ h1
      obtain ⟨rfl, h3⟩ := ihl _ _ _ h2
      obtain ⟨rfl, rfl⟩ := ihr _ _ _ h3
      exact ⟨rfl, rfl⟩

instance : Ser HStore := ⟨hsEnc, hsEnc_pf⟩

/-! ## The claim, the witness, the blocks -/

instance : Ser ChunkSlot := Ser.ofInj (fun (x : ChunkSlot) => (x.1, x.2)) (by inj_tac)
instance : Ser BlockRec := Ser.ofInj (fun (x : BlockRec) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser EpochRec := Ser.ofInj (fun (x : EpochRec) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser ValidatorUpdateFacts := Ser.ofInj
  (fun (x : ValidatorUpdateFacts) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser SplitGate := Ser.ofInj (fun (x : SplitGate) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser ApplyFacts := Ser.ofInj (fun (x : ApplyFacts) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser Claim := Ser.ofInj
  (fun (x : Claim) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12)) (by inj_tac)

/-! ### G-5 (lanes E ∧ G): circuit-friendly serialisers of the `done` components

`ctxDE (.header H) = bdigest (3 ‖ Ser.enc H)` and `outDE (.done o).1 = bdigest (Ser.enc o)` are
recomputed by lane G's FINAL AIR, so `Ser ChunkInner` / `Ser Outputs` use fixed-width forms for the
fields a real header has: a natural is `natW n = 0 ‖ beN 16 n` when `n < 2^128` (`1 ‖ vnat n`
otherwise), a byte string `hashW b = 0 ‖ b` when `|b| = 32` (`1 ‖ Ser.enc b` otherwise); the list
and option fields keep `Ser.enc` (`[0]` when empty). Both are prefix-free (`natW_pf`, `hashW_pf`),
so the two instances are (`Ser.ofInj`), and `ViewE`'s domain separation (`ctxPre`'s tag `3`,
`outDE`'s constructor tag) is unchanged. -/

/-- A natural in the fixed-width form. -/
structure NatW where
  n : Nat

/-- A byte string in the 32-byte fixed-width form. -/
structure HashW where
  b : Bytes

def natW (n : Nat) : Bytes := if n < 2 ^ 128 then 0 :: ArenaCore.Bytes.beN 16 n else 1 :: vnat n

def hashW (b : Bytes) : Bytes := if b.length = 32 then 0 :: b else 1 :: Ser.enc b

theorem natW_pf : PF (fun x : NatW => natW x.n) := by
  intro ⟨a⟩ ⟨b⟩ r r' h
  simp only [natW] at h
  by_cases ha : a < 2 ^ 128 <;> by_cases hb : b < 2 ^ 128 <;>
    simp only [ha, hb, ite_true, ite_false, List.cons_append, List.cons.injEq] at h
  · obtain ⟨e, hr⟩ := ViewE.append_left_eq h.2
      (by rw [ArenaCore.Bytes.beN_length, ArenaCore.Bytes.beN_length])
    have := congrArg ArenaCore.Bytes.beToNat e
    rw [ArenaCore.Bytes.beToNat_beN, ArenaCore.Bytes.beToNat_beN,
      Nat.mod_eq_of_lt (show a < 256 ^ 16 by simpa using ha),
      Nat.mod_eq_of_lt (show b < 256 ^ 16 by simpa using hb)] at this
    exact ⟨by rw [this], hr⟩
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · obtain ⟨e, hr⟩ := vnat_pf a b r r' h.2
    exact ⟨by rw [e], hr⟩

theorem hashW_pf : PF (fun x : HashW => hashW x.b) := by
  intro ⟨a⟩ ⟨b⟩ r r' h
  simp only [hashW] at h
  by_cases ha : a.length = 32 <;> by_cases hb : b.length = 32 <;>
    simp only [ha, hb, ite_true, ite_false, List.cons_append, List.cons.injEq] at h
  · obtain ⟨e, hr⟩ := ViewE.append_left_eq h.2 (by rw [ha, hb])
    exact ⟨by rw [e], hr⟩
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · obtain ⟨e, hr⟩ := Ser.pf a b r r' h.2
    exact ⟨by rw [e], hr⟩

instance : Ser NatW := ⟨fun x => natW x.n, natW_pf⟩
instance : Ser HashW := ⟨fun x => hashW x.b, hashW_pf⟩

/-- The congestion record in the fixed-width form. -/
def congW (c : Congestion) : NatW × NatW × NatW × NatW := (⟨c.1⟩, ⟨c.2⟩, ⟨c.3⟩, ⟨c.4⟩)

theorem congW_inj : ∀ a b : Congestion, congW a = congW b → a = b := by
  intro a b h; cases a; cases b; simp_all [congW]

/-- The tuple a chunk inner is serialised through. -/
def ciW (x : ChunkInner) :=
  (NatW.mk x.tag, HashW.mk x.prevBlockHash, HashW.mk x.prevStateRoot, HashW.mk x.prevOutcomeRoot,
    HashW.mk x.encodedMerkleRoot, NatW.mk x.encodedLength, NatW.mk x.heightCreated,
    NatW.mk x.shardId, NatW.mk x.prevGasUsed, NatW.mk x.gasLimit, NatW.mk x.prevBalanceBurnt,
    HashW.mk x.prevOutgoingReceiptsRoot, HashW.mk x.txRoot, x.proposals, congW x.congestion,
    x.bwRequests, x.proposedSplit)

theorem ciW_inj : ∀ a b : ChunkInner, ciW a = ciW b → a = b := by
  intro a b h
  cases a; cases b
  simp only [ciW, Prod.mk.injEq, NatW.mk.injEq, HashW.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have := congW_inj _ _ h15
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h16 h17 this
  rfl

/-- **Root**: the chunk header's inner part (G-5: fixed-width fields). -/
instance : Ser ChunkInner := Ser.ofInj ciW ciW_inj

instance : Ser BlockHdr := Ser.ofInj
  (fun (x : BlockHdr) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10)) (by inj_tac)
instance : Ser Blk := Ser.ofInj (fun (x : Blk) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser Transition := Ser.ofInj (fun (x : Transition) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser ShardProof := Ser.ofInj (fun (x : ShardProof) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser EntryD2 := Ser.ofInj (fun (x : EntryD2) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser StateWitnessD2 := Ser.ofInj
  (fun (x : StateWitnessD2) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9)) (by inj_tac)
instance : Ser Layout := Ser.ofInj
  (fun (x : Layout) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7)) (by inj_tac)
instance : Ser RetainMode := Ser.ofInj
  (fun | .left => (.inl () : Unit ⊕ Unit) | .right => .inr ()) (by inj_tac)

section Walk
open NearSpecV3.Successor
instance : Ser WalkTransition := Ser.ofInj
  (fun | .old i s => (.inl (i, s) : (Nat × Nat) ⊕ (Bytes × RetainMode × Nat))
       | .split b m s => .inr (b, m, s)) (by inj_tac)
instance : Ser Walk := Ser.ofInj (fun (x : Walk) => (x.1, x.2, x.3, x.4, x.5, x.6)) (by inj_tac)
end Walk

instance : Ser Scheduler.Params := Ser.ofInj
  (fun (x : Scheduler.Params) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser ApplyCtx := Ser.ofInj
  (fun (x : ApplyCtx) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8)) (by inj_tac)
instance : Ser Env := Ser.ofInj
  (fun (x : Env) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10)) (by inj_tac)
instance : Ser ChunkExtra := Ser.ofInj
  (fun (x : ChunkExtra) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10)) (by inj_tac)
instance : Ser D2Fin := Ser.ofInj (fun (x : D2Fin) => (x.1, x.2)) (by inj_tac)

/-- **Root**: the intake record (`ctxDE (.intake I)`). -/
instance : Ser Intake := Ser.ofInj
  (fun (x : Intake) => ((x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10),
    (x.11, x.12, x.13, x.14, x.15, x.16, x.17, x.18, x.19))) (by inj_tac)

/-- **Root**: the genesis intake (`ctxDE (.gen G)`). -/
instance : Ser GFin := Ser.ofInj
  (fun (x : GFin) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11)) (by inj_tac)

/-- The tuple the header outputs are serialised through (G-5: fixed-width fields). -/
def outW (x : Outputs) :=
  (HashW.mk x.stateRoot, HashW.mk x.outcomeRoot, x.proposals, NatW.mk x.gasLimit, NatW.mk x.gasUsed,
    NatW.mk x.balanceBurnt, HashW.mk x.outgoingRoot, congW x.congestion, x.bwRequests,
    x.proposedSplit, HashW.mk x.txRoot, HashW.mk x.encodedMerkleRoot, NatW.mk x.encodedLength)

theorem outW_inj : ∀ a b : Outputs, outW a = outW b → a = b := by
  intro a b h
  cases a; cases b
  simp only [outW, Prod.mk.injEq, NatW.mk.injEq, HashW.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have := congW_inj _ _ h8
  subst h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 this
  rfl

/-- **Root**: the header outputs (`outDE (.done o)`). -/
instance : Ser Outputs := Ser.ofInj outW outW_inj

/-! ## The Wasm machine -/

section Wasm
open NearSpecV3.Wasm

instance : Ser VT := Ser.ofInj
  (fun | VT.i32 => (0 : Nat) | .i64 => 1 | .f32 => 2 | .f64 => 3 | .funcref => 4 | .externref => 5)
  (by inj_tac)

/-- `VT` as a number (for `Instr`'s arguments). -/
def vtN : VT → Nat
  | .i32 => 0 | .i64 => 1 | .f32 => 2 | .f64 => 3 | .funcref => 4 | .externref => 5

def vtD : Nat → Option VT
  | 0 => some .i32 | 1 => some .i64 | 2 => some .f32 | 3 => some .f64 | 4 => some .funcref
  | 5 => some .externref | _ => none

theorem vtD_vtN (t : VT) : vtD (vtN t) = some t := by cases t <;> rfl

/-- `Option VT` as a number: `0` none, `vtN t + 1`. -/
def ovN : Option VT → Nat
  | none => 0
  | some t => vtN t + 1

def ovD : Nat → Option (Option VT)
  | 0 => some none
  | n + 1 => (vtD n).map some

theorem ovD_ovN (t : Option VT) : ovD (ovN t) = some t := by
  cases t with
  | none => rfl
  | some t => simp [ovN, ovD, vtD_vtN]

instance : Ser FuncType := Ser.ofInj (fun (x : FuncType) => (x.1, x.2)) (by inj_tac)
instance : Ser Limits := Ser.ofInj (fun (x : Limits) => (x.1, x.2)) (by inj_tac)
instance : Ser TableType := Ser.ofInj (fun (x : TableType) => (x.1, x.2)) (by inj_tac)
instance : Ser Import := Ser.ofInj (fun (x : Import) => (x.1, x.2, x.3, x.4)) (by inj_tac)

/-- An instruction as `(opcode tag, arguments)`. -/
def instrN : Instr → Nat × List Nat
  | .unreachable => (0, []) | .nop => (1, [])
  | .block bt => (2, [ovN bt]) | .loop bt => (3, [ovN bt]) | .if_ bt => (4, [ovN bt])
  | .else_ => (5, []) | .end_ => (6, [])
  | .br l => (7, [l]) | .brIf l => (8, [l]) | .brTable ls d => (9, d :: ls.toList)
  | .ret => (10, [])
  | .call f => (11, [f]) | .callIndirect ty tab => (12, [ty, tab])
  | .refNull t => (13, [vtN t]) | .refIsNull => (14, []) | .refFunc f => (15, [f])
  | .drop => (16, []) | .select t => (17, [ovN t])
  | .localGet i => (18, [i]) | .localSet i => (19, [i]) | .localTee i => (20, [i])
  | .globalGet i => (21, [i]) | .globalSet i => (22, [i])
  | .tableGet t => (23, [t]) | .tableSet t => (24, [t]) | .tableSize t => (25, [t])
  | .tableGrow t => (26, [t])
  | .tableFill t => (27, [t]) | .tableCopy a b => (28, [a, b]) | .tableInit e t => (29, [e, t])
  | .elemDrop e => (30, [e])
  | .load op a o => (31, [op, a, o]) | .store op a o => (32, [op, a, o])
  | .memSize => (33, []) | .memGrow => (34, []) | .memCopy => (35, []) | .memFill => (36, [])
  | .memInit d => (37, [d]) | .dataDrop d => (38, [d])
  | .i32Const v => (39, [v.toNat]) | .i64Const v => (40, [v.toNat])
  | .num op => (41, [op]) | .float op => (42, [op])
  | .floatLoad op a o => (43, [op, a, o]) | .floatStore op a o => (44, [op, a, o])
  | .f32Const b => (45, [b.toNat]) | .f64Const b => (46, [b.toNat])

def instrD : Nat × List Nat → Option Instr
  | (0, []) => some .unreachable | (1, []) => some .nop
  | (2, [b]) => (ovD b).map .block | (3, [b]) => (ovD b).map .loop | (4, [b]) => (ovD b).map .if_
  | (5, []) => some .else_ | (6, []) => some .end_
  | (7, [l]) => some (.br l) | (8, [l]) => some (.brIf l)
  | (9, d :: ls) => some (.brTable ls.toArray d)
  | (10, []) => some .ret
  | (11, [f]) => some (.call f) | (12, [a, b]) => some (.callIndirect a b)
  | (13, [t]) => (vtD t).map .refNull | (14, []) => some .refIsNull | (15, [f]) => some (.refFunc f)
  | (16, []) => some .drop | (17, [t]) => (ovD t).map .select
  | (18, [i]) => some (.localGet i) | (19, [i]) => some (.localSet i)
  | (20, [i]) => some (.localTee i)
  | (21, [i]) => some (.globalGet i) | (22, [i]) => some (.globalSet i)
  | (23, [t]) => some (.tableGet t) | (24, [t]) => some (.tableSet t)
  | (25, [t]) => some (.tableSize t) | (26, [t]) => some (.tableGrow t)
  | (27, [t]) => some (.tableFill t) | (28, [a, b]) => some (.tableCopy a b)
  | (29, [a, b]) => some (.tableInit a b) | (30, [e]) => some (.elemDrop e)
  | (31, [a, b, c]) => some (.load a b c) | (32, [a, b, c]) => some (.store a b c)
  | (33, []) => some .memSize | (34, []) => some .memGrow | (35, []) => some .memCopy
  | (36, []) => some .memFill
  | (37, [d]) => some (.memInit d) | (38, [d]) => some (.dataDrop d)
  | (39, [v]) => some (.i32Const (UInt32.ofNat v)) | (40, [v]) => some (.i64Const (UInt64.ofNat v))
  | (41, [o]) => some (.num o) | (42, [o]) => some (.float o)
  | (43, [a, b, c]) => some (.floatLoad a b c) | (44, [a, b, c]) => some (.floatStore a b c)
  | (45, [v]) => some (.f32Const (UInt32.ofNat v)) | (46, [v]) => some (.f64Const (UInt64.ofNat v))
  | _ => none

theorem instrD_instrN (i : Instr) : instrD (instrN i) = some i := by
  cases i <;> first
    | rfl
    | (show Option.map _ (ovD (ovN _)) = _; rw [ovD_ovN]; rfl)
    | (show Option.map _ (vtD (vtN _)) = _; rw [vtD_vtN]; rfl)
    | (show some (Instr.i32Const (UInt32.ofNat (UInt32.toNat _))) = _; rw [UInt32.ofNat_toNat])
    | (show some (Instr.i64Const (UInt64.ofNat (UInt64.toNat _))) = _; rw [UInt64.ofNat_toNat])
    | (show some (Instr.f32Const (UInt32.ofNat (UInt32.toNat _))) = _; rw [UInt32.ofNat_toNat])
    | (show some (Instr.f64Const (UInt64.ofNat (UInt64.toNat _))) = _; rw [UInt64.ofNat_toNat])
    | (show some (Instr.brTable (Array.toList _).toArray _) = _; rw [Array.toArray_toList])

instance : Ser Instr := Ser.ofLeftInv instrN instrD instrD_instrN

instance : Ser ConstE := Ser.ofInj
  (fun | ConstE.i32 v => (.inl v : UInt32 ⊕ UInt64 ⊕ VT ⊕ Nat ⊕ Nat ⊕ UInt32 ⊕ UInt64)
       | .i64 v => .inr (.inl v) | .refNull t => .inr (.inr (.inl t))
       | .refFunc f => .inr (.inr (.inr (.inl f))) | .globalGet g => .inr (.inr (.inr (.inr (.inl g))))
       | .f32 b => .inr (.inr (.inr (.inr (.inr (.inl b)))))
       | .f64 b => .inr (.inr (.inr (.inr (.inr (.inr b)))))) (by inj_tac)
instance : Ser Global := Ser.ofInj (fun (x : Global) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser SegMode := Ser.ofInj
  (fun | SegMode.passive => (.inl () : Unit ⊕ Unit ⊕ (Nat × ConstE)) | .declarative => .inr (.inl ())
       | .active t o => .inr (.inr (t, o))) (by inj_tac)
instance : Ser Elem := Ser.ofInj (fun (x : Elem) => (x.1, x.2, x.3, x.4)) (by inj_tac)
instance : Ser Data := Ser.ofInj (fun (x : Data) => (x.1, x.2)) (by inj_tac)
instance : Ser Func := Ser.ofInj (fun (x : Func) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser Module := Ser.ofInj
  (fun (x : Module) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12, x.13))
  (by inj_tac)
instance : Ser Wasm.Ctx := Ser.ofInj
  (fun (x : Wasm.Ctx) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8)) (by inj_tac)
instance : Ser IK := Ser.ofInj
  (fun | IK.pure => (0 : Nat) | .unreach => 1 | .pre => 2 | .post => 3 | .between => 4
       | .linear => 5) (by inj_tac)
instance : Ser Wasm.Fee := Ser.ofInj (fun (x : Wasm.Fee) => (x.1, x.2)) (by inj_tac)
instance : Ser PFunc := Ser.ofInj
  (fun (x : PFunc) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8)) (by inj_tac)

/-- **Root**: a prepared module (lane A's `WRest.air`). -/
instance : Ser Prepared := Ser.ofInj (fun (x : Prepared) => (x.1, x.2, x.3)) (by inj_tac)

/-- **Root**: the entry kind (lane A's `WRest.air`). -/
instance : Ser CallCut.EntK := Ser.ofInj
  (fun | CallCut.EntK.start mi => (.inl mi : Nat ⊕ Unit) | .method => .inr ()) (by inj_tac)

instance : Ser NearCfg := Ser.ofInj
  (fun (x : NearCfg) => ((x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12),
    (x.13, x.14, x.15, x.16, x.17, x.18, x.19, x.20, x.21, x.22, x.23, x.24))) (by inj_tac)
instance : Ser PRes := Ser.ofInj
  (fun | PRes.notReady => (.inl () : Unit ⊕ ByteArray ⊕ Unit) | .ok d => .inr (.inl d)
       | .failed => .inr (.inr ())) (by inj_tac)
instance : Ser CallCtx := Ser.ofInj
  (fun (x : CallCtx) => ((x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11),
    (x.12, x.13, x.14, x.15, x.16, x.17, x.18, x.19, x.20, x.21, x.22))) (by inj_tac)
instance : Ser Val := Ser.ofInj
  (fun | Val.i32 v => (.inl v : UInt32 ⊕ UInt64 ⊕ UInt32 ⊕ UInt64 ⊕ Option Nat)
       | .i64 v => .inr (.inl v) | .f32 b => .inr (.inr (.inl b)) | .f64 b => .inr (.inr (.inr (.inl b)))
       | .ref r => .inr (.inr (.inr (.inr r)))) (by inj_tac)
instance : Ser Wasm.Gas := Ser.ofInj
  (fun (x : Wasm.Gas) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9)) (by inj_tac)
instance : Ser Label := Ser.ofInj (fun (x : Label) => (x.1, x.2, x.3, x.4)) (by inj_tac)
instance : Ser Frame := Ser.ofInj (fun (x : Frame) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser PromiseV := Ser.ofInj
  (fun | PromiseV.receipt i => (.inl i : Nat ⊕ Array Nat) | .joint is => .inr is) (by inj_tac)
instance : Ser MAct := Ser.ofInj
  (fun (x : MAct) => (x.1, x.2, x.3, x.4, x.5, x.6)) (by inj_tac)

/-! ### `RealStore`: no serialiser (a function field) -/

/-- **No prefix-free serialiser of a store function exists** (Cantor). -/
theorem no_ser_store (S : Ser TTN.Store) : False := by
  classical
  let emb : (Bytes → Bool) → TTN.Store := fun p h => if p h.data.toList then some .empty else none
  have hemb : ∀ p q, emb p = emb q → p = q := by
    intro p q e
    funext l
    have := congrFun e ⟨⟨l⟩⟩
    simp only [emb] at this
    cases hp : p l <;> cases hq : q l <;> simp_all
  let G : (Bytes → Bool) → Bytes := fun p => S.enc (emb p)
  have hG : ∀ p q, G p = G q → p = q := fun p q e => hemb p q (S.pf.inj e)
  let D : Bytes → Bool := fun b => decide (¬ ∃ q, G q = b ∧ q b = true)
  have key : D (G D) = true ↔ ¬ D (G D) = true := by
    constructor
    · intro h h'
      have h1 : ¬ ∃ q, G q = G D ∧ q (G D) = true := of_decide_eq_true h
      exact h1 ⟨D, rfl, h'⟩
    · intro h
      apply decide_eq_true
      rintro ⟨q, hq, hq'⟩
      rw [hG q D hq] at hq'
      exact h hq'
  by_cases h : D (G D) = true
  · exact key.mp h h
  · exact h (key.mpr h)

/-- `RealStore` without its `store` function. -/
def encRS (x : TTN.RealStore) : Bytes :=
  Ser.enc (x.root, x.overlay, x.acct, x.pfx, x.recd, x.recBefore, x.writes)

/-- `encRS` determines every field but `store`. -/
theorem encRS_pf_mod (a b : TTN.RealStore) (r r' : Bytes) (h : encRS a ++ r = encRS b ++ r')
    (hs : a.store = b.store) : a = b ∧ r = r' := by
  obtain ⟨e, hr⟩ := Ser.pf _ _ _ _ h
  refine ⟨?_, hr⟩
  cases a; cases b
  simp only [Prod.mk.injEq] at e hs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
  subst hs
  rfl

/-! ### Store-blind encoders (injective modulo the store functions)

Not a `Ser` (no `PF`): each `…N` map forgets the `store` functions, and its injectivity is up to
`strip…` (every `RealStore.store` replaced by `blankStore`). For the parent's choice of how to bind
the stores (they are a function of the context component in the honest run: `CutW`'s
`store := fun hb => (env.codeOf (ofBA hb)).map toBA`). -/

def blankStore : TTN.Store := fun _ => none

def stripRS (x : TTN.RealStore) : TTN.RealStore := { x with store := blankStore }

abbrev RSN := ByteArray × TTN.BMap (Option ByteArray) × TTN.Acct × ByteArray × TTN.Recorder × Nat ×
  Array (ByteArray × Option ByteArray)

def rsN (x : TTN.RealStore) : RSN :=
  (x.root, x.overlay, x.acct, x.pfx, x.recd, x.recBefore, x.writes)

theorem rsN_eq {a b : TTN.RealStore} (h : rsN a = rsN b) : stripRS a = stripRS b := by
  cases a; cases b; simp_all [rsN, stripRS]

theorem map_rsN_eq {a b : Option TTN.RealStore} (h : a.map rsN = b.map rsN) :
    a.map stripRS = b.map stripRS := by
  (cases a <;> cases b <;> simp_all) <;> exact rsN_eq h

def stripSt (s : St) : St := { s with real := s.real.map stripRS }

abbrev StN := (Array Val × List Frame × Array ByteArray × Array Val × Array (Option Nat) × Nat ×
    Array (Array (Option Nat)) × Array ByteArray × Nat × Wasm.Gas × CallCtx × Option (ByteArray ⊕ Nat) ×
    Nat) ×
  (Nat × Array (Nat × ByteArray) × Nat × Array ByteArray × Nat × Array PromiseV ×
    Array (ByteArray × ByteArray) × Array MAct × Nat × Option RSN × Nat × Bool × Bool)

def stN (x : St) : StN :=
  ((x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12, x.13),
   (x.14, x.15, x.16, x.17, x.18, x.19, x.20, x.21, x.22, x.23.map rsN, x.24, x.25, x.26))

theorem stN_eq {a b : St} (h : stN a = stN b) : stripSt a = stripSt b := by
  cases a; cases b
  simp only [stN, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩,
    ⟨h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩⟩ := h
  have := map_rsN_eq h23
  simp only [stripSt] at this ⊢
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h24 h25 h26
  rw [this]

def stripRes : Res → Res
  | .cont s => .cont (stripSt s) | .fin s => .fin (stripSt s)
  | .abort s e => .abort (stripSt s) e | .unmodeled w => .unmodeled w

def resN : Res → StN ⊕ StN ⊕ (StN × String) ⊕ String
  | .cont s => .inl (stN s)
  | .fin s => .inr (.inl (stN s)) | .abort s e => .inr (.inr (.inl (stN s, e)))
  | .unmodeled w => .inr (.inr (.inr w))

theorem resN_eq {a b : Res} (h : resN a = resN b) : stripRes a = stripRes b := by
  (cases a <;> cases b <;> simp_all [resN, stripRes]) <;> first | exact stN_eq h | exact stN_eq h.1

def stripRun : Run → Run
  | .line l => .line l | .done s e => .done (stripSt s) e

def runN : Run → String ⊕ (StN × Option String)
  | .line l => .inl l | .done s e => .inr (stN s, e)

theorem runN_eq {a b : Run} (h : runN a = runN b) : stripRun a = stripRun b := by
  (cases a <;> cases b <;> simp_all [runN, stripRun]) <;> exact stN_eq h.1

def stripArgs (q : CallCut.CallArgs) : CallCut.CallArgs := { q with real := stripRS q.real }

def argsN (q : CallCut.CallArgs) : NearCfg × ByteArray × String × CallCtx × RSN := (q.cfg, q.code, q.method, q.ctx, rsN q.real)

theorem argsN_eq {a b : CallCut.CallArgs} (h : argsN a = argsN b) : stripArgs a = stripArgs b := by
  cases a; cases b
  simp only [argsN, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, h⟩ := h
  simp only [stripArgs, rsN_eq h]

def stripConf : CallCut.CallConf → CallCut.CallConf
  | .pre => .pre | .ent p k r n => .ent p k (stripRes r) n | .fin r => .fin (stripRun r)

def confN : CallCut.CallConf →
    Unit ⊕ (Prepared × CallCut.EntK × (StN ⊕ StN ⊕ (StN × String) ⊕ String) × Nat) ⊕
      (String ⊕ (StN × Option String))
  | .pre => .inl ()
  | .ent p k r n => .inr (.inl (p, k, resN r, n)) | .fin r => .inr (.inr (runN r))

theorem confN_eq {a b : CallCut.CallConf} (h : confN a = confN b) : stripConf a = stripConf b := by
  (cases a <;> cases b <;> simp_all [confN, stripConf]) <;>
    first | exact resN_eq h.2.2.1 | exact runN_eq h | exact runN_eq ‹_›

/-- **The store-blind tape-entry encoder**: prefix-free modulo the store functions. -/
def encQRN (e : CallCut.CallArgs × Run) : Bytes := Ser.enc (argsN e.1, runN e.2)

theorem encQRN_pf_mod (a b : CallCut.CallArgs × Run) (r r' : Bytes)
    (h : encQRN a ++ r = encQRN b ++ r') :
    (stripArgs a.1, stripRun a.2) = (stripArgs b.1, stripRun b.2) ∧ r = r' := by
  obtain ⟨e, hr⟩ := Ser.pf _ _ _ _ h
  simp only [Prod.mk.injEq] at e
  exact ⟨by rw [argsN_eq e.1, runN_eq e.2], hr⟩

end Wasm

/-! ## The `ViewE` application -/

theorem intake_pf : PF (Ser.enc : Intake → Bytes) := Ser.pf
theorem gfin_pf : PF (Ser.enc : GFin → Bytes) := Ser.pf
theorem chunkInner_pf : PF (Ser.enc : ChunkInner → Bytes) := Ser.pf
theorem outputs_pf : PF (Ser.enc : Outputs → Bytes) := Ser.pf
theorem prepared_pf : PF (Ser.enc : Wasm.Prepared → Bytes) := Ser.pf
theorem entK_pf : PF (Ser.enc : Wasm.CallCut.EntK → Bytes) := Ser.pf

/-- **The context commitment**, instances resolved. -/
def ctxDEc (lB : Bytes → Nat) : CtxV → Bytes := ViewE.ctxDE lB

theorem coll_ctxDEc (lB : Bytes → Nat) (h : Coll (ctxDEc lB)) : Sha384Coll := ViewE.coll_ctxDE lB h

/-- **The output commitment**, instances resolved. -/
def outDEc : OutV → Bytes × List Bytes × Bytes × Bytes := ViewE.outDE

theorem coll_outDEc (h : Coll outDEc) : Sha384Coll := ViewE.coll_outDE h

#print axioms intake_pf
#print axioms gfin_pf
#print axioms chunkInner_pf
#print axioms outputs_pf
#print axioms prepared_pf
#print axioms entK_pf
#print axioms coll_ctxDEc
#print axioms coll_outDEc
#print axioms instrD_instrN
#print axioms no_ser_store
#print axioms encRS_pf_mod
#print axioms encQRN_pf_mod
#print axioms confN_eq

end NearSpecV3.E2E.Enc
