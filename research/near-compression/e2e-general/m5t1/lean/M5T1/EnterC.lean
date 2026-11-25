import M5T1.SegRt
import NearSpecV3.E2E.TreeM8C

/-!
# M5T1.EnterC — the `rt` enter leaf in the relative, store-canonical form (F-3)

Lane E's M11i obligation (`StoreBlind.TmplRelC`, `TreeM8C.TmplSoundRel8C`): **every canonical
opening of the input digest steps to a canonical opening of the output digest**. This file proves
it for the `rt` enter leaf (`Ent.lean`, `BndLay.enterCons`) from the leaf's constraints.

## The leaf predicate (`EntHoldsC`)

`Holds entAir pub tr` (the circuit) ∧ every public value a byte ∧ `d`, `d'` the 42-B digests of the
two sides (the leaf wrapper, lane D) ∧ **named checks** `EntChecks` on a ghost query `q` (the
call's `CallArgs`, carried in the trace type like lane A's ghost context):
* `vm`: the output's remainder digest is `vmc q` (lane A's `fbBnd (q, .pre)` remainder digest —
  `encRest` is lane A's, and its preimage cannot be checked by a copying leaf);
* `prepaid`: the output's `rPrepaid` is `pre q` (the view's clear value of the query: since
  lane E's M12 `clearE`, `u64c q.ctx.prepaidGas`, the prepaid gas, as in lane I's driver);
* `code`: the first 32 bytes of the output's `codeRoot` are `SHA-256(q.code)` (S2; the code hash
  the receipt rows read — the account's `code_hash` — and, once joined, lane B's account read);
* `pos`: `posOK` of the input's `stRoot` (lane B: the state commitment shows a non-final position,
  review-D7 I3).

## The view laws (`RtView`)

`wf` (well-formed records), `blind` (`StoreBlind`, S1), `noWasm` (`wasmD none = none`), `preW`
(**S2**: lane A's `.pre` record is `preRec (vmc q) q` — `fbBnd`'s constants with `codeRoot =
preCodeRoot q`), `clearEnter` (the clear fields of `call I c [] q .pre` are those of `eng I c` with
`t := 0`, `rPrepaid := pre q`; lane E's M12 `clearE` meets it with `pre q =
u64c q.ctx.prepaidGas`, `ViewE.clearE_enter`), `outOne` (the engine-state
outgoing accumulator is one digest, as `outDE (.eng a)`), `pos` (lane B: `posOK` of `stD (stOfI …)`
excludes `done`).

## Results

* **`enter_relC`** — `TmplRelC`-shaped, for every view meeting `RtView`: an accepted enter leaf
  whose input digest opens canonically to `x` has an output digest that opens canonically to an
  `MRt.enter` successor of `x` (`x = eng I c`, `x' = call I c [] q' .pre`, `q'` = the ghost query
  with the context's store `sf I`), or a 42-B SHA-384 collision.
* `enter_relC8` — the M8 form (`TmplSoundRel8C` shape, leaf statement `(phase, digest)`),
  `enter_notInit` — the leaf rejects a phase-0 input (`NotInitIn`).
* Proof route: `enc_eng` / `enc_call` (the record encoding is the concatenation of its fields in
  `BndLay` order), `bytesOf_lay` (the public values split the same way), `flat_inj` (equal
  concatenations of equal-width pieces are equal piecewise), the per-field rule semantics of
  `SegRt`, `bnd_enter` (the view of `call I c [] q .pre` is the view of `eng I c` with the four
  relabelled fields and the `.pre` Wasm part).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace M5T1.EnterC

open ZkFormal.Air ZkFormal.Algebra M5T1 M5T1.BndLay M5T1.SegRt
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1 NearSpecV3.E2E.SB
open NearSpecV3.Wasm NearSpecV3.Wasm.CallCut
open ArenaCore.Bytes (beN beN_length beToNat beToNat_beN)
abbrev Bytes := ArenaCore.Bytes

/-! ## 1. Byte strings of public values -/

theorem bytesOf_length (pub : List Fp) (a n : Nat) : (bytesOf pub a n).length = n := by
  simp [bytesOf]

theorem bytesOf_add (pub : List Fp) (a n m : Nat) :
    bytesOf pub a (n + m) = bytesOf pub a n ++ bytesOf pub (a + n) m := by
  simp only [bytesOf, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_assoc]

theorem width_cons (n : String) (k : Nat) (r : Layout) : Layout.width ((n, k) :: r) = k + r.width := by
  simp [Layout.width]

/-- **The public values split along a layout** with distinct names. -/
theorem bytesOf_lay (pub : List Fp) : ∀ (L : Layout) (a : Nat), (L.map (·.1)).Nodup →
    bytesOf pub a L.width = (L.map fun p => bytesOf pub (a + L.off p.1) p.2).flatten
  | [], a, _ => by simp [bytesOf, Layout.width]
  | (n, k) :: r, a, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [width_cons, bytesOf_add, bytesOf_lay pub r (a + k) hn.2]
    simp only [List.map_cons, List.flatten_cons, Layout.off, beq_self_eq_true, ite_true, Nat.add_zero]
    congr 1
    congr 1
    apply List.map_congr_left
    intro p hp
    have hne : (n == p.1) = false := by
      rw [beq_eq_false_iff_ne]
      intro he; exact hn.1 (he ▸ List.mem_map.2 ⟨p, hp, rfl⟩)
    simp only [hne, Bool.false_eq_true, ite_false, Nat.add_assoc]

/-- **Equal concatenations of pieces of equal widths are equal piecewise.** -/
theorem flat_inj {β : Type} : ∀ (L : List β) (F G : β → Bytes) (w : β → Nat),
    (∀ p ∈ L, (F p).length = w p) → (∀ p ∈ L, (G p).length = w p) →
    (L.map F).flatten = (L.map G).flatten → ∀ p ∈ L, F p = G p
  | [], _, _, _, _, _, _ => by simp
  | a :: r, F, G, w, hF, hG, h => by
    simp only [List.map_cons, List.flatten_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hF a List.mem_cons_self, hG a List.mem_cons_self])
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact flat_inj r F G w (fun q hq => hF q (List.mem_cons_of_mem _ hq))
        (fun q hq => hG q (List.mem_cons_of_mem _ hq)) h2 p hp

/-- A big-endian constant from its little-endian byte facts. -/
theorem bytesOf_num (pub : List Fp) (a : Nat) : ∀ (w v : Nat),
    (∀ k < w, pv pub (a + (w - 1 - k)) = v / 256 ^ k % 256) → bytesOf pub a w = beN w v
  | 0, _, _ => rfl
  | w + 1, v, h => by
    rw [bytesOf_add, beN]
    congr 1
    · apply bytesOf_num pub a w (v / 256)
      intro k hk
      have := h (k + 1) (by omega)
      rw [show w + 1 - 1 - (k + 1) = w - 1 - k by omega, Nat.pow_succ, Nat.mul_comm,
        ← Nat.div_div_eq_div_mul] at this
      exact this
    · have := h 0 (by omega)
      simp only [Nat.pow_zero, Nat.div_one, show w + 1 - 1 - 0 = w by omega] at this
      simp [bytesOf, this]

/-- Constant bytes from per-byte facts. -/
theorem bytesOf_dig (pub : List Fp) (a : Nat) (b : List Nat) (h : ∀ j < b.length, pv pub (a + j) = b.getD j 0) :
    bytesOf pub a b.length = b.map UInt8.ofNat := by
  apply List.ext_getElem (by simp [bytesOf_length])
  intro i h1 h2
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  rw [h i (by simpa [bytesOf_length] using h1)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [bytesOf_length] using h1)]

/-- Zero bytes from per-byte facts. -/
theorem bytesOf_zero (pub : List Fp) (a n : Nat) (h : ∀ j < n, pv pub (a + j) = 0) :
    bytesOf pub a n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [bytesOf_length])
  intro i h1 h2
  simp only [bytesOf, List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [h i (by simpa [bytesOf_length] using h1)]
  rfl

/-! ## 2. Records as named fields -/

/-- A default Wasm part (only used off the Wasm fields). -/
def wdflt : WasmBnd := ⟨0, 0, 0, 0, 0, [], [], 0, [], [], [], [], [], []⟩

/-- The bytes of a Wasm field, by `BndLay.wasmF` name. -/
def wasmVal (w : WasmBnd) : String → Bytes
  | "pc" => beN 8 w.pc | "sp" => beN 8 w.sp | "stackRem" => beN 8 w.stackRem
  | "fuel" => beN 8 w.fuel | "gasLeft" => beN 8 w.gasLeft | "framesDigest" => w.framesDigest
  | "memRoot" => w.memRoot | "memPages" => beN 8 w.memPages | "globalsDigest" => w.globalsDigest
  | "registersDigest" => w.registersDigest | "vmCtxDigest" => w.vmCtxDigest
  | "promisesDigest" => w.promisesDigest | "codeRoot" => w.codeRoot | "funcRoot" => w.funcRoot
  | _ => []

/-- The bytes of a record field, by `BndLay.callF` name (`outRcpt0`: the first list entry,
`wasmTag`: the presence byte). -/
def recVal (B : BndRec) : String → Bytes
  | "claimDigest" => B.claimDigest | "phase" => beN 8 B.phase | "blockIdx" => beN 8 B.blockIdx
  | "receiptIdx" => beN 8 B.receiptIdx | "actionIdx" => beN 8 B.actionIdx
  | "inCall" => [if B.inCall then 1 else 0] | "t" => beN 8 B.t | "stRoot" => B.stRoot
  | "ctxRoot" => B.ctxRoot | "gasUsed" => beN 8 B.gasUsed | "gasBurnt" => beN 8 B.gasBurnt
  | "balanceBurnt" => beN 16 B.balanceBurnt | "compute" => beN 8 B.compute
  | "rPrepaid" => beN 8 B.rPrepaid | "rBurnt" => beN 8 B.rBurnt | "rUsed" => beN 8 B.rUsed
  | "outcomeAcc" => B.outcomeAcc | "outRcptN" => beN 8 B.outRcptAcc.length
  | "outRcpt0" => B.outRcptAcc.headD [] | "proposalsAcc" => B.proposalsAcc | "bwAcc" => B.bwAcc
  | "vmAcc" => B.vmAcc | "wasmTag" => (match B.wasm with | none => [0] | some _ => [1])
  | f => wasmVal (B.wasm.getD wdflt) f

/-- **The encoding of an out-of-call record** is its fields in `engF` order. -/
theorem enc_eng (B : BndRec) (hw : B.wasm = none) {d : Bytes} (ho : B.outRcptAcc = [d]) :
    B.encode = (engF.map fun p => recVal B p.1).flatten := by
  obtain ⟨cd, ph, bi, ri, ai, ic, t, sr, cr, gu, gb, bb, co, rp, rb, ru, oa, orl, pa, ba, va, wa⟩ := B
  simp only at hw ho
  subst hw ho
  simp [BndRec.encode, BndRec.codec, mapC, pairC, listC, optC, boolC, bytesC, natC, engF, recVal]

/-- **The encoding of an in-call record** is its fields in `callF` order. -/
theorem enc_call (B : BndRec) {w : WasmBnd} (hw : B.wasm = some w) {d : Bytes} (ho : B.outRcptAcc = [d]) :
    B.encode = (callF.map fun p => recVal B p.1).flatten := by
  obtain ⟨cd, ph, bi, ri, ai, ic, t, sr, cr, gu, gb, bb, co, rp, rb, ru, oa, orl, pa, ba, va, wa⟩ := B
  simp only at hw ho
  subst hw ho
  simp [BndRec.encode, BndRec.codec, WasmBnd.codec, mapC, pairC, listC, optC, boolC, bytesC, natC,
    callF, engF, wasmF, recVal, wasmVal]

theorem engF_nodup : (engF.map (·.1)).Nodup := by decide
theorem callF_nodup : (callF.map (·.1)).Nodup := by decide

/-- Field widths of a well-formed out-of-call record. -/
theorem len_eng {B : BndRec} (hwf : B.WF) (hw : B.wasm = none) {d : Bytes} (ho : B.outRcptAcc = [d]) :
    ∀ p ∈ engF, (recVal B p.1).length = p.2 := by
  obtain ⟨cd, ph, bi, ri, ai, ic, t, sr, cr, gu, gb, bb, co, rp, rb, ru, oa, orl, pa, ba, va, wa⟩ := B
  simp only at hw ho
  subst hw ho
  simp only [BndRec.WF, BndRec.codec, mapC, pairC, listC, optC, boolC, bytesC, natC, digestLen] at hwf
  intro p hp
  simp only [engF, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [recVal, beN_length]

/-- Field widths of a well-formed in-call record. -/
theorem len_call {B : BndRec} (hwf : B.WF) {w : WasmBnd} (hw : B.wasm = some w) {d : Bytes}
    (ho : B.outRcptAcc = [d]) : ∀ p ∈ callF, (recVal B p.1).length = p.2 := by
  obtain ⟨cd, ph, bi, ri, ai, ic, t, sr, cr, gu, gb, bb, co, rp, rb, ru, oa, orl, pa, ba, va, wa⟩ := B
  simp only at hw ho
  subst hw ho
  simp only [BndRec.WF, BndRec.codec, WasmBnd.codec, mapC, pairC, listC, optC, boolC, bytesC, natC,
    digestLen] at hwf
  intro p hp
  simp only [callF, engF, wasmF, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [recVal, wasmVal, beN_length]

/-! ## 3. The constants, the `.pre` record (S2) and the view laws -/

/-- `bdigest []` is `BndLay.emptyDig` (the constant digest cells of the enter AIR). -/
theorem emptyDig_eq : bdigest [] = emptyDig.map UInt8.ofNat := by decide +kernel

/-- **Lane A's `.pre` record with S2**: `fbBnd (q, .pre)`'s constants, remainder digest `v`, and
`codeRoot = preCodeRoot q = SHA-256(q.code) ‖ 0^10`. -/
def preRec (v : Bytes) (q : CallArgs) : WasmBnd :=
  { pc := 0, sp := 0, stackRem := 0, fuel := 0, gasLeft := 0, framesDigest := bdigest [],
    memRoot := bdigest [], memPages := 0, globalsDigest := bdigest [], registersDigest := bdigest [],
    vmCtxDigest := v, promisesDigest := bdigest [], codeRoot := preCodeRoot q, funcRoot := bdigest [] }

/-- **The view laws the enter edge uses** (module header): lane E's view shape, lane A's S2 `.pre`
record, lane B's position check. -/
structure RtView (V : ViewImpl) (vmc : CallArgs → Bytes) (pre : CallArgs → Nat)
    (posOK : Bytes → Prop) : Prop where
  wf : ∀ x, (V.bnd x).WF
  blind : StoreBlind V
  noWasm : V.wasmD none = none
  preW : ∀ q, V.wasmD (some (q, .pre)) = some (preRec (vmc q) q)
  clearEnter : ∀ I c q, V.clear (.call I c [] q .pre) =
    { V.clear (.base (.eng I c)) with t := 0, rPrepaid := pre q }
  outOne : ∀ a, (V.outD (.eng a)).2.1.length = 1
  pos : ∀ I c, posOK (V.stD (stOfI V.keys I c)) → ∀ out, c.pos ≠ .done out

/-- **The view of the call configuration the enter edge produces**: the engine record with
`phase 6`, `inCall`, clock `0`, the query's `rPrepaid` and the `.pre` Wasm part. -/
def enterRec (B : BndRec) (r : Nat) (w : WasmBnd) : BndRec :=
  { B with phase := 6, inCall := true, t := 0, rPrepaid := r, wasm := some w }

theorem bnd_enter {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat} {posOK : Bytes → Prop}
    (hV : RtView V vmc pre posOK) (I : Intake) (c : EConf) (q : CallArgs) :
    V.bnd (.call I c [] q .pre) = enterRec (V.bnd (.base (.eng I c))) (pre q) (preRec (vmc q) q) := by
  simp [ViewImpl.bnd, split, hV.clearEnter, hV.preW, hV.noWasm, enterRec]

/-! ## 4. The leaf predicate -/

/-- The enter leaf's trace: public values, the trace, and the ghost query. -/
abbrev EntW := List Fp × Trace Fp × CallArgs

/-- **The enter leaf's named checks** (module header). -/
structure EntChecks (vmc : CallArgs → Bytes) (pre : CallArgs → Nat) (posOK : Bytes → Prop)
    (pub : List Fp) (q : CallArgs) : Prop where
  vm : bytesOf pub (450 + callF.off "vmCtxDigest") 42 = vmc q
  prepaid : bytesOf pub (450 + callF.off "rPrepaid") 8 = beN 8 (pre q)
  code : bytesOf pub (450 + callF.off "codeRoot") 32 = ArenaCore.sha256 q.code.data.toList
  pos : posOK (bytesOf pub (engF.off "stRoot") 42)

/-- **The enter leaf at digest boundaries**: the AIR holds, every public value is a byte (the
wrapper hashes them as bytes), the digests are the two sides', and the named checks. -/
def EntHoldsC (vmc : CallArgs → Bytes) (pre : CallArgs → Nat) (posOK : Bytes → Prop)
    (d d' : Bytes) (w : EntW) : Prop :=
  Holds Ent.entAir w.1 w.2.1 ∧ (∀ i < 1284, pv w.1 i < 256) ∧ d = bdigest (bytesOf w.1 0 450) ∧
    d' = bdigest (bytesOf w.1 450 834) ∧ EntChecks vmc pre posOK w.1 w.2.2

/-! ## 5. Field facts from the constraints, as byte strings -/

section
variable {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAir pub tr)
include H

omit H in
theorem bytesOf_congr {a b n : Nat} (h : ∀ j < n, pv pub (a + j) = pv pub (b + j)) :
    bytesOf pub a n = bytesOf pub b n := by
  simp only [bytesOf]
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.1 hj)]

omit H in
theorem emptyDig_lt (j : Nat) : emptyDig.getD j 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < emptyDig.length
  · rw [List.getElem?_eq_getElem h]
    have : ∀ x ∈ emptyDig, x < 256 := by decide
    exact this _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; decide

theorem copy_bytes {p : String × Nat} (hp : p ∈ callF) :
    outRule p.1 = .copy → fw engF p.1 = p.2 →
      bytesOf pub (engF.off p.1) p.2 = bytesOf pub (450 + callF.off p.1) p.2 := by
  intro hr hw
  apply bytesOf_congr
  intro j hj
  exact copy_sem H hp hr j (hw ▸ hj)

theorem num_bytes {p : String × Nat} (hp : p ∈ callF) {v : Nat} :
    outRule p.1 = .num v → fw callF p.1 = p.2 → bytesOf pub (450 + callF.off p.1) p.2 = beN p.2 v := by
  intro hr hw
  apply bytesOf_num
  intro k hk
  have := num_sem H hp hr k (hw ▸ hk)
  rwa [hw] at this

theorem dig_bytes {p : String × Nat} (hp : p ∈ callF) :
    outRule p.1 = .dig emptyDig → p.2 = 42 → bytesOf pub (450 + callF.off p.1) p.2 = bdigest [] := by
  intro hr hw
  rw [emptyDig_eq, hw]
  exact bytesOf_dig pub _ emptyDig (fun j hj => dig_sem H hp hr emptyDig_lt j (by rw [hw]; exact hj))

theorem pad_bytes {p : String × Nat} (hp : p ∈ callF) :
    outRule p.1 = .pad 32 → p.2 = 42 →
      bytesOf pub (450 + callF.off p.1) p.2 =
        bytesOf pub (450 + callF.off p.1) 32 ++ List.replicate 10 0 := by
  intro hr hw
  rw [hw, show (42 : Nat) = 32 + 10 from rfl, bytesOf_add]
  congr 1
  apply bytesOf_zero
  intro j hj
  have := pad_sem H hp hr j (by rw [hw]; omega)
  simpa [Nat.add_assoc] using this

/-- The input record's phase bytes. -/
theorem in_phase : bytesOf pub 42 8 = beN 8 1 := by
  apply bytesOf_num
  intro k hk
  exact in_sem H (f := "phase") (by simp) k hk
end

/-! ## 6. The enter edge -/

theorem enc_prefix (B : BndRec) : ∃ rest, B.encode = B.claimDigest ++ (beN 8 B.phase ++ rest) :=
  ⟨_, rfl⟩

/-- The input record of an accepted enter leaf has phase `1`. -/
theorem phase_one {B : BndRec} (hwf : B.WF) {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAir pub tr)
    (he : B.encode = bytesOf pub 0 450) : B.phase = 1 := by
  obtain ⟨rest, hr⟩ := enc_prefix B
  have hcd : B.claimDigest.length = 42 := hwf.1.1
  have hph : B.phase < 256 ^ 8 := hwf.1.2.1
  rw [hr, show (450 : Nat) = 42 + (8 + 400) from rfl, bytesOf_add, bytesOf_add] at he
  obtain ⟨-, he⟩ := List.append_inj he (by rw [hcd, bytesOf_length])
  obtain ⟨he, -⟩ := List.append_inj he (by rw [beN_length, bytesOf_length])
  rw [in_phase H] at he
  have := congrArg beToNat he
  rw [beToNat_beN, beToNat_beN, Nat.mod_eq_of_lt hph] at this
  simpa using this

theorem phase_eng {V : ViewImpl} {x : RConf} (h : (V.bnd x).phase = 1) : ∃ I c, x = .base (.eng I c) := by
  cases x with
  | base c =>
    cases c with
    | eng I c => exact ⟨I, c, rfl⟩
    | _ => simp [ViewImpl.bnd, split] at h
  | call => simp [ViewImpl.bnd, split] at h

/-- **The input record, field by field.** -/
theorem in_fields {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat} {posOK : Bytes → Prop}
    (hV : RtView V vmc pre posOK) {I : Intake} {c : EConf} {pub : List Fp}
    (he : (V.bnd (.base (.eng I c))).encode = bytesOf pub 0 450) :
    ∀ p ∈ engF, recVal (V.bnd (.base (.eng I c))) p.1 = bytesOf pub (engF.off p.1) p.2 := by
  have hw : (V.bnd (.base (.eng I c))).wasm = none := by simp [ViewImpl.bnd, split, hV.noWasm]
  obtain ⟨d, hd⟩ : ∃ d, (V.bnd (.base (.eng I c))).outRcptAcc = [d] := by
    have := hV.outOne (eposAcc c.pos)
    match h : (V.outD (.eng (eposAcc c.pos))).2.1, this with
    | [d], _ => exact ⟨d, by simp [ViewImpl.bnd, split, h]⟩
  rw [enc_eng _ hw hd, show (450 : Nat) = engF.width from by decide, bytesOf_lay pub engF 0 engF_nodup]
    at he
  have := flat_inj engF _ _ (·.2) (len_eng (hV.wf _) hw hd) (fun p _ => bytesOf_length _ _ _) he
  simpa using this

section
attribute [local irreducible] bdigest

/-- **The rules, field by field** (37 cases, each by evaluation): what the enter AIR constrains a
field to, and what the field of `enterRec B r (preRec v q)` is. -/
theorem rules : ∀ p ∈ callF,
    (outRule p.1 = .copy ∧ p ∈ engF ∧ fw engF p.1 = p.2 ∧
      ∀ B r w, recVal (enterRec B r w) p.1 = recVal B p.1) ∨
    (∃ n, outRule p.1 = .num n ∧ fw callF p.1 = p.2 ∧
      ∀ B r v q, recVal (enterRec B r (preRec v q)) p.1 = beN p.2 n) ∨
    (outRule p.1 = .dig emptyDig ∧ p.2 = 42 ∧
      ∀ B r v q, recVal (enterRec B r (preRec v q)) p.1 = bdigest []) ∨
    p = ("rPrepaid", 8) ∨ p = ("vmCtxDigest", 42) ∨ p = ("codeRoot", 42) := by
  intro p hp
  simp only [callF, engF, wasmF, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (refine .inl ⟨rfl, ?_⟩; exact ⟨by simp [engF], rfl, fun _ _ _ => rfl⟩)
    | (refine .inr (.inl ⟨_, rfl, ?_⟩); exact ⟨rfl, fun _ _ _ _ => rfl⟩)
    | (refine .inr (.inr (.inl ⟨rfl, ?_⟩)); exact ⟨rfl, fun _ _ _ _ => rfl⟩)
    | exact .inr (.inr (.inr (.inl rfl)))
    | exact .inr (.inr (.inr (.inr (.inl rfl))))
    | exact .inr (.inr (.inr (.inr (.inr rfl))))


/-- **The output record of an accepted enter leaf is the view of `call I c [] q .pre`.** -/
theorem out_enc {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat} {posOK : Bytes → Prop}
    (hV : RtView V vmc pre posOK) {I : Intake} {c : EConf} {pub : List Fp} {tr : Trace Fp} {q : CallArgs}
    (H : Holds Ent.entAir pub tr) (ch : EntChecks vmc pre posOK pub q)
    (he : (V.bnd (.base (.eng I c))).encode = bytesOf pub 0 450) :
    (V.bnd (.call I c [] q .pre)).encode = bytesOf pub 450 834 := by
  have hin := in_fields hV he
  have hw : (V.bnd (.call I c [] q .pre)).wasm = some (preRec (vmc q) q) := by
    rw [bnd_enter hV]; rfl
  obtain ⟨d, hd⟩ : ∃ d, (V.bnd (.call I c [] q .pre)).outRcptAcc = [d] := by
    have := hV.outOne (eposAcc c.pos)
    match h : (V.outD (.eng (eposAcc c.pos))).2.1, this with
    | [d], _ => exact ⟨d, by simp [ViewImpl.bnd, split, h]⟩
  rw [enc_call _ hw hd, show (834 : Nat) = callF.width from by decide,
    bytesOf_lay pub callF 450 callF_nodup]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [bnd_enter hV]
  rcases rules p hp with ⟨hr, hm, hw, hrec⟩ | ⟨n, hr, hw, hrec⟩ | ⟨hr, hw, hrec⟩ | rfl | rfl | rfl
  · rw [hrec, hin p hm, copy_bytes H hp hr hw]
  · rw [hrec, num_bytes H hp hr hw]
  · rw [hrec, dig_bytes H hp hr hw]
  · exact ch.prepaid.symm
  · exact ch.vm.symm
  · show preCodeRoot q = _
    rw [pad_bytes H hp rfl rfl, ch.code]
    rfl
end

/-- **The opening step**: if the input record is the view of `x`, the output record opens to the
canonical `MRt.enter` successor of `x`. -/
theorem enter_open {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat}
    {posOK : Bytes → Prop} (hV : RtView V vmc pre posOK) (sf : Intake → TTN.Store)
    {pub : List Fp} {tr : Trace Fp} {q : CallArgs} (H : Holds Ent.entAir pub tr)
    (ch : EntChecks vmc pre posOK pub q) (x : RConf) (he : (V.bnd x).encode = bytesOf pub 0 450) :
    ∃ I c, x = .base (.eng I c) ∧ (∀ out, c.pos ≠ .done out) ∧
      Canon sf (.call I c [] (setArgs (sf I) q) .pre) ∧
      (V.bnd (.call I c [] (setArgs (sf I) q) .pre)).encode = bytesOf pub 450 834 := by
  obtain ⟨I, c, rfl⟩ := phase_eng (phase_one (hV.wf x) H he)
  -- the position is not final (lane B's check on the input's `stRoot`)
  have hnf : ∀ out, c.pos ≠ .done out := by
    apply hV.pos I c
    have := in_fields hV he ("stRoot", 42) (by simp [engF])
    have hst : recVal (V.bnd (.base (.eng I c))) "stRoot" = V.stD (stOfI V.keys I c) := rfl
    rw [← hst, this]
    exact ch.pos
  have ho := out_enc hV H ch he
  refine ⟨I, c, rfl, hnf, ?_, ?_⟩
  · show setR (sf I) (.call I c [] (setArgs (sf I) q) .pre) = _
    simp [setR, setK, setArgs_setArgs, setConf]
  · have hb : V.bnd (.call I c [] (setArgs (sf I) q) .pre) = V.bnd (.call I c [] q .pre) := by
      rw [hV.blind, hV.blind (.call I c [] q .pre)]
      simp [stripR, setR, setK, setArgs_setArgs, setConf]
    rw [hb, ho]

/-- The enter edge with the collision branch (`enter_relC`, `enter_relC8` from it). -/
theorem enter_core {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat}
    {posOK : Bytes → Prop} (hV : RtView V vmc pre posOK) (sf : Intake → TTN.Store)
    (d d' : Bytes) (w : EntW) (x : RConf) (hh : EntHoldsC vmc pre posOK d d' w)
    (hx : bndOf V.bnd x = d) :
    Sha384Coll ∨ ∃ I c q, x = .base (.eng I c) ∧ (∀ out, c.pos ≠ .done out) ∧
      Canon sf (.call I c [] q .pre) ∧ bndOf V.bnd (.call I c [] q .pre) = d' := by
  classical
  obtain ⟨pub, tr, q⟩ := w
  obtain ⟨H, -, hd, hd', ch⟩ := hh
  by_cases he : (V.bnd x).encode = bytesOf pub 0 450
  · obtain ⟨I, c, rfl, hnf, hc, ho⟩ := enter_open hV sf H ch x he
    exact .inr ⟨I, c, _, rfl, hnf, hc, by simp only [bndOf]; rw [ho, hd']⟩
  · exact .inl ⟨_, _, he, by rw [← hd]; exact hx⟩

/-- **`TmplRelC` for the `rt` enter edge** (lane F, F-3): under the view laws `RtView`, an accepted
enter leaf whose input digest opens canonically to `x` has an output digest that opens canonically
to an `MRt.enter` successor of `x`, or there is a 42-B SHA-384 collision. -/
theorem enter_relC {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat}
    {posOK : Bytes → Prop} (hV : RtView V vmc pre posOK) (sf : Intake → TTN.Store)
    (d d' : Bytes) (w : EntW) (x : RConf) (hh : EntHoldsC vmc pre posOK d d' w) (hc : Canon sf x)
    (hx : bndOf V.bnd x = d) :
    Sha384Coll ∨ ∃ x', Canon sf x' ∧ bndOf V.bnd x' = d' ∧ Meaning .rt x x' := by
  rcases enter_core hV sf d d' w x hh hx with h | ⟨I, c, q, rfl, hnf, hc', hd'⟩
  · exact .inl h
  · exact .inr ⟨_, hc', hd', .enter I c q hnf⟩

/-! ## 7. The M8 form and the phase check -/

open NearSpecV3.E2E.M8 in
/-- The enter leaf at M8 leaf statements `(phase, digest)`: the digest predicate and the wrapper's
phase cells (`1` in, `6` out — the record's own phase bytes, which the AIR pins). -/
def EntHolds8 (vmc : CallArgs → Bytes) (pre : CallArgs → Nat) (posOK : Bytes → Prop)
    (_ctx : Bytes) (b b' : LB) (w : EntW) : Prop :=
  EntHoldsC vmc pre posOK b.2 b'.2 w ∧ b.1 = 1 ∧ b'.1 = 6

open NearSpecV3.E2E.M8 in
/-- **The M8 form** (`TmplSoundRel8C` shape): with the context link of `rt` (none). -/
theorem enter_relC8 {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat}
    {posOK : Bytes → Prop} (hV : RtView V vmc pre posOK) (sf : Intake → TTN.Store)
    (ctx : Bytes) (b b' : LB) (w : EntW) (hh : EntHolds8 vmc pre posOK ctx b b' w) (x : RConf)
    (hc : Canon sf x) (hx : b = lbOf V x) :
    Sha384Coll ∨ ∃ x', Canon sf x' ∧ b' = lbOf V x' ∧ Meaning .rt x x' ∧ CtxLink .rt ctx x x' := by
  obtain ⟨hh, -, h6⟩ := hh
  rcases enter_core hV sf b.2 b'.2 w x hh (by rw [hx]; rfl) with h | ⟨I, c, q, rfl, hnf, hc', hd'⟩
  · exact .inl h
  · refine .inr ⟨_, hc', ?_, .enter I c q hnf, trivial⟩
    obtain ⟨b1, b2⟩ := b'
    simp only at h6 hd'
    subst h6
    simp [lbOf, hd', rec_phase_call]

open NearSpecV3.E2E.M8 in
/-- **The enter leaf rejects a phase-0 input** (its part of `NotInitIn`). -/
theorem enter_notInit {vmc : CallArgs → Bytes} {pre : CallArgs → Nat} {posOK : Bytes → Prop}
    {ctx : Bytes} {b b' : LB} {w : EntW} (hh : EntHolds8 vmc pre posOK ctx b b' w) : b.1 ≠ 0 := by
  rw [hh.2.1]; decide

#print axioms rules
#print axioms out_enc
#print axioms enter_open
#print axioms enter_core
#print axioms enter_relC
#print axioms enter_relC8
#print axioms enter_notInit

end M5T1.EnterC
