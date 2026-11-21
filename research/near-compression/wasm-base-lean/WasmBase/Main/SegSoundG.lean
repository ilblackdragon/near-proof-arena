import WasmBase.Main.SegGrowMemgQ
/-!
# WasmBase.Main.SegSoundG — segment soundness of `wasmBaseSegAirG`, cut case, from a named action layer (E2E M6, GROW2)

`seg_sound_g` assembles the grow segment's cut case in the σ form through `exec_rowsJQ`
(`Main/SegExecQ.lean`) with the invariant `QG` (registers, `SpCG`, `RegWF`, the size clause `SzC`)
and the thread `SigJ σ`, for an M3 module `X : M3Ctx` (semantics on `X.ctx`, CODE bound to the
M3 records by `CodeOK3`).

**Proved here for the MEMG rows** (every action labelled as an active MEMG row `rr`): the row facts
`RowFactsSegMapJQ X.ctx (SigJ σ) QG mf` (spec: `memg_growOk_rowSpec` / `memg_growFail_rowSpec` /
`memg_size_rowSpec`; flat: `memg_growOk_flat` / `memg_grow_flat` / `memg_size_flat`; σ-keep:
`rowJKeep_sig` + `memg_codeNonHost`) and `RowQJM X.ctx (SigJ σ) QG mf` (`memg_*_rowQJM`), and at the
boundaries the size clause from SEGG (`segg_size_track`): the in-block's only space-8 message is
SEGG's production, the out-block contains SEGG's consumption, hence **`nblk_out = 64 · sN.pages.size`**.

**Named (premises of `SegGLayer`, the `HoldsXS` layer of the grow AIR, open):** the action list with
its STATE/CH permutations (`hst`, `hch`: `seg_msgs_permS` for the grow AIR), `init` duplicate-free
with times `≤ t_in`, the MEMG labelling (`memg`: which actions are MEMG rows, with the zero bytes
`A` MEMBG attributes to each successful grow, `membg_grow_link`), and the facts of the non-MEMG
actions (`base`, `baseQ`: the instruction/HOST rows of `actListM2` as in `seg_sound_σS`).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- The kinds of an active MEMG row. -/
inductive MemgKind (tr : Trace) (r : Nat) : Prop
  | growOk : mgc tr r MemG.fGrow = 1 → mgc tr r MemG.fSize = 0 → mgc tr r MemG.ok = 1 → MemgKind tr r
  | growFail : mgc tr r MemG.fGrow = 1 → mgc tr r MemG.fSize = 0 → mgc tr r MemG.ok = 0 → MemgKind tr r
  | size : mgc tr r MemG.fGrow = 0 → mgc tr r MemG.fSize = 1 → MemgKind tr r

/-- **Every active MEMG row is a successful grow, a failed grow, or a size row** (the bit
constraints and `act = f_grow + f_size`). -/
theorem memg_kind {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 32) (ha : (MemG.act.eval (tr.row pub 32 r)).toNat = 1) : MemgKind tr r := by
  have hPr := rowNat_lt tr 32 r
  have C : ∀ e ∈ MemG.constraints, e.eval (tr.row pub 32 r) = 0 := fun e he =>
    H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr e (by rw [segG_t32']; exact he)
  have bit : ∀ i, Chips.bool (v i) ∈ MemG.constraints → mgc tr r i = 0 ∨ mgc tr r i = 1 := by
    intro i hi
    have h := C _ hi
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memg_col_eval] at h
    exact bool_nat (hPr _) h
  have hg := bit MemG.fGrow (by simp [MemG.constraints])
  have hs := bit MemG.fSize (by simp [MemG.constraints])
  have hok := bit MemG.ok (by simp [MemG.constraints])
  have hact : mgc tr r MemG.fGrow + mgc tr r MemG.fSize = 1 := by
    simp only [MemG.act, Expr.eval_add', memg_col_eval, ← Lean.Grind.Semiring.natCast_add] at ha
    rw [Fp.toNat_cast_of_lt (by rw [P_val]; rcases hg with h | h <;> rcases hs with h' | h' <;> omega)] at ha
    exact ha
  rcases hg with hg | hg <;> rcases hs with hs | hs
  · omega
  · exact .size hg hs
  · rcases hok with h | h
    · exact .growFail hg hs h
    · exact .growOk hg hs h
  · omega

/-- **The named action layer of a grow segment** (the `HoldsXS` layer for `wasmBaseSegAirG`, open):
an action list with STATE/CH permutations whose MEMG actions are labelled by their rows, and the
row facts of the other actions. -/
structure SegGLayer (X : M3Ctx) (nloc ngl : Nat) (pub : List F) (tr : Trace) (σ : Nat → St)
    (sg : Nat → Nat × Nat) (mf : Nat) (ρ : Type) [DecidableEq ρ] where
  act : List ρ
  inS : ρ → List F
  outS : ρ → List F
  cons : ρ → List Msg
  prod : ρ → List Msg
  init : List Msg
  fin : List Msg
  m0 : List F
  sbf : F
  cidf : F
  /-- the STATE bus: the in-boundary and every action's out-STATE are the out-boundary and every
  action's in-STATE (`seg_msgs_permS` for the grow AIR) -/
  hst : (m0 :: act.map outS).Perm
    ([pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((0 : Nat) : F), sbf, cidf] ::
      act.map inS)
  /-- the CH bus -/
  hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons)
  hinit : init.Nodup
  hinitTp : ∀ x ∈ init, x.tp ≤ (pub.getD pubTIn 0).toNat
  /-- the MEMG actions: an active MEMG row, its messages (a successful grow's productions with the
  zero bytes `A` MEMBG hands to it), its charge, the σ thread and the gas window kept -/
  memg : ρ → Option (Nat × List Nat)
  memgRow : ∀ a ∈ act, ∀ rr A, memg a = some (rr, A) →
    rr < tr.height 32 ∧ (MemG.act.eval (tr.row pub 32 rr)).toNat = 1 ∧
    inS a = rowIn MemG.table tr pub 32 rr ∧ outS a = rowOut MemG.table tr pub 32 rr ∧
    cons a = rowCons MemG.table tr pub 32 rr ∧
    prod a = rowProd MemG.table tr pub 32 rr ++ zeroBytes A (mgc tr rr cTs) ∧
    mgc tr rr cFee + mgc tr rr MemG.lin * (mgc tr rr MemG.n0 + 65536 * mgc tr rr MemG.n1) ≤ mf ∧
    (mgc tr rr MemG.ok = 1 → A.Nodup ∧ ∀ x ∈ A, mgc tr rr MemG.old * pageSize ≤ x ∧
      x < (mgc tr rr MemG.old + (mgc tr rr MemG.n0 + 65536 * mgc tr rr MemG.n1)) * pageSize) ∧
    (mgc tr rr MemG.ok = 0 → A = []) ∧
    σ ((lvl (inS a)).toNat + 1) = σ (lvl (inS a)).toNat ∧
    sg ((lvl (inS a)).toNat + 1) = sg (lvl (inS a)).toNat
  /-- the other actions' row facts and invariant (the instruction / HOST rows, `seg_sound_σS`) -/
  base : ∀ a ∈ act, memg a = none →
    RowFactsSegMapJQ X.ctx (SigJ σ) QG mf (inS a) (outS a) (cons a) (prod a) sg
  baseQ : ∀ a ∈ act, memg a = none → RowQJM X.ctx (SigJ σ) QG mf (inS a) (cons a) (prod a)

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- **The row facts of a labelled MEMG action.** -/
theorem memg_rowFacts (X : M3Ctx) (hcode : CodeOK3 X tr) {σ : Nat → St} {sg : Nat → Nat × Nat} {mf : Nat}
    {inS outS : List F} {cons prod : List Msg} {rr : Nat} {A : List Nat}
    (hr : rr < tr.height 32) (ha : (MemG.act.eval (tr.row pub 32 rr)).toNat = 1)
    (eI : inS = rowIn MemG.table tr pub 32 rr) (eO : outS = rowOut MemG.table tr pub 32 rr)
    (eC : cons = rowCons MemG.table tr pub 32 rr)
    (eP : prod = rowProd MemG.table tr pub 32 rr ++ zeroBytes A (mgc tr rr cTs))
    (hmf : mgc tr rr cFee + mgc tr rr MemG.lin * (mgc tr rr MemG.n0 + 65536 * mgc tr rr MemG.n1) ≤ mf)
    (hA : mgc tr rr MemG.ok = 1 → A.Nodup ∧ ∀ x ∈ A, mgc tr rr MemG.old * pageSize ≤ x ∧
      x < (mgc tr rr MemG.old + (mgc tr rr MemG.n0 + 65536 * mgc tr rr MemG.n1)) * pageSize)
    (hA0 : mgc tr rr MemG.ok = 0 → A = [])
    (hσ : σ ((lvl inS).toNat + 1) = σ (lvl inS).toNat) (hsg : sg ((lvl inS).toNat + 1) = sg (lvl inS).toNat)
    (hg64 : X.ctx.g0 < 2 ^ 64) :
    RowFactsSegMapJQ X.ctx (SigJ σ) QG mf inS outS cons prod sg ∧ RowQJM X.ctx (SigJ σ) QG mf inS cons prod := by
  subst eI eO eC eP
  have hQ : ∀ s live, QG s live → SzC s live := fun _ _ h => h.2
  unfold RowFactsSegMapJQ
  rw [hsg]
  rcases memg_kind H hr ha with ⟨hg, hs, hok⟩ | ⟨hg, hs, hok⟩ | ⟨hg, hs⟩
  · have hJk := rowJKeep_sig (memg_codeNonHost H X hcode hr (Or.inl ⟨hg, hs⟩)) hσ
    obtain ⟨hAnd, hAr⟩ := hA hok
    exact ⟨⟨memg_growOk_rowSpec H X hcode hr hg hs hok hQ hJk hmf A hAnd hAr,
      memg_growOk_flat H hr hg hs hmf A hAnd⟩, memg_growOk_rowQJM H X hcode hr hg hs hok hmf A⟩
  · have hJk := rowJKeep_sig (memg_codeNonHost H X hcode hr (Or.inl ⟨hg, hs⟩)) hσ
    rw [hA0 hok]
    simp only [zeroBytes, List.map_nil, List.append_nil]
    exact ⟨⟨memg_growFail_rowSpec H X hcode hr hg hs hok hQ hJk hmf, memg_grow_flat H hr hg hs hmf⟩,
      memg_growFail_rowQJM H X hcode hr hg hs hok hmf⟩
  · have hJk := rowJKeep_sig (memg_codeNonHost H X hcode hr (Or.inr ⟨hg, hs⟩)) hσ
    have hlin := (memg_size_zero H hr hg).2
    have hok := (memg_size_zero H hr hg).1
    have hmf' : mgc tr rr cFee ≤ mf := by rw [hlin] at hmf; omega
    have hA' : A = [] := hA0 hok
    subst hA'
    simp only [zeroBytes, List.map_nil, List.append_nil]
    exact ⟨⟨memg_size_rowSpec H X hcode hr hg hs hQ hJk hmf', memg_size_flat H hr hg hs hmf'⟩,
      memg_size_rowQJM H X hcode hr hg hs hmf' hg64⟩

/-- **Segment soundness of `wasmBaseSegAirG`, cut case** (`status = 0`), from the named action layer
`L`: the segment runs `|act|` spec steps from `s0` to `sN`, `sN` is related to the out-boundary
(`Bnd`), keeps the invariant `QG` (registers, `SpCG`, `RegWF`, the size clause) against the
out-block and the σ thread, and **the public out-block count is `64 · sN.pages.size`**.  The in-side
size clause comes from SEGG: the in-block's only space-8 message is SEGG's production
`[8, 0, 0, pin, …, t_in]` with `nblk_in = 64 · pin = 64 · |s0.pages|`; the out-block contains SEGG's
consumption with `nblk_out = 64 · pout`. -/
theorem seg_sound_g (X : M3Ctx) (hcode : CodeOK3 X tr) {σ : Nat → St} {sg : Nat → Nat × Nat} {mf : Nat}
    {ρ : Type} [DecidableEq ρ] (L : SegGLayer X nloc ngl pub tr σ sg mf ρ)
    (ht : (pub.getD pubTIn 0).toNat + L.act.length + 1 + (2 ^ 30 + 2 ^ 16) < P)
    (hfee : (pub.getD pubSIn 0).toNat + (L.act.length + 1) * (mf + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.ctx.R * (S - (sg t).1) + g = (sg t).2 → X.ctx.R * (S + mf - (sg t).1) ≤ (sg t).2)
    (hg64 : X.ctx.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X.ctx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat L.m0 L.init)
    (hQ0 : (RegC (· ∈ L.init) s0 ∧ SpCG (· ∈ L.init)) ∧ RegWF s0)
    (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1))
    {pin pout : Nat} (hin : (pNin pub).toNat = 64 * pin) (hout : (pNout pub).toNat = 64 * pout)
    (hpin : 64 * pin < P) (hpout : 64 * pout < P)
    (h8 : ∀ x ∈ L.init, x.space = 8 → x = decMsg (segSzIn tr pub)) (hmi : decMsg (segSzIn tr pub) ∈ L.init)
    (hs0 : s0.pages.size = pin) (hmfin : decMsg (segSzOut tr pub) ∈ L.fin) :
    (pub.getD pubTOut 0 + 1).toNat = (pub.getD pubTIn 0).toNat + L.act.length + 1 ∧
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p L.act.length s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (L.act.length + m) s0 = run X.cfg X.p m sN) ∧
      Bnd X.ctx sg sN ((pub.getD pubTIn 0).toNat + L.act.length) (pub.getD pubSOut 0).toNat
        [pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((0 : Nat) : F), L.sbf, L.cidf] L.fin ∧
      QG sN (· ∈ L.fin) ∧ sideR sN = σ ((pub.getD pubTIn 0).toNat + L.act.length + 1) ∧
      (pNout pub).toNat = 64 * sN.pages.size := by
  -- the size clause at the start, from SEGG
  obtain ⟨e1, e2⟩ := segg_size_dec H hin hout hpin hpout
  have h8' := h8
  have hmi' := hmi
  rw [e1, ← hs0] at h8' hmi'
  have hsz0 : SzC s0 (· ∈ L.init) := szC_init h8' hmi'
  -- the rows
  have hfacts : ∀ a ∈ L.act, RowFactsSegMapJQ X.ctx (SigJ σ) QG mf (L.inS a) (L.outS a) (L.cons a) (L.prod a) sg ∧
      RowQJM X.ctx (SigJ σ) QG mf (L.inS a) (L.cons a) (L.prod a) := by
    intro a ha
    cases hm : L.memg a with
    | none => exact ⟨L.base a ha hm, L.baseQ a ha hm⟩
    | some p =>
      obtain ⟨rr, A⟩ := p
      obtain ⟨hr, hact, eI, eO, eC, eP, hmf, hA, hA0, hσ, hsg⟩ := L.memgRow a ha rr A hm
      exact memg_rowFacts H X hcode hr hact eI eO eC eP hmf hA hA0 hσ hsg hg64
  obtain ⟨hN, hcut, -⟩ := exec_rowsJQ X.ctx L.act L.inS L.outS L.cons L.prod L.init L.fin (pub.getD pubPcOut 0)
    (pub.getD pubTOut 0 + 1) (pub.getD pubSOut 0) sg 0 (by decide) (SigJ σ) QG mf (fun a ha => (hfacts a ha).1)
    (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat L.m0 L.sbf L.cidf L.hst L.hch L.hinit L.hinitTp ht hfee
    hstepgas hg64 h0 (fun a ha => (hfacts a ha).2) ⟨hQ0, hsz0⟩ hσ0
  obtain ⟨sN, h1, h2, h3, h4, h5⟩ := hcut rfl
  refine ⟨hN, sN, h1, h2, h3, h4, h5, ?_⟩
  rw [e2] at hmfin
  rw [hout, szC_fin h4.2 hmfin]

/-- **The grow segment's out-boundary view** (`seg_sound_g` + `cutView_eqLG`): the final state is
related by `BndCG` (the boundary relation with the live size message), and after relabelling the
out-block's part outside spaces 3, 7, 8 is, up to producer times, exactly `cutView X.ctx sN`. -/
theorem seg_sound_g_view (X : M3Ctx) (hcode : CodeOK3 X tr) {σ : Nat → St} {sg : Nat → Nat × Nat} {mf : Nat}
    {ρ : Type} [DecidableEq ρ] (L : SegGLayer X nloc ngl pub tr σ sg mf ρ)
    (ht : (pub.getD pubTIn 0).toNat + L.act.length + 1 + (2 ^ 30 + 2 ^ 16) < P)
    (hfee : (pub.getD pubSIn 0).toNat + (L.act.length + 1) * (mf + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.ctx.R * (S - (sg t).1) + g = (sg t).2 → X.ctx.R * (S + mf - (sg t).1) ≤ (sg t).2)
    (hg64 : X.ctx.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X.ctx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat L.m0 L.init)
    (hQ0 : (RegC (· ∈ L.init) s0 ∧ SpCG (· ∈ L.init)) ∧ RegWF s0)
    (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1))
    {pin pout : Nat} (hin : (pNin pub).toNat = 64 * pin) (hout : (pNout pub).toNat = 64 * pout)
    (hpin : 64 * pin < P) (hpout : 64 * pout < P)
    (h8 : ∀ x ∈ L.init, x.space = 8 → x = decMsg (segSzIn tr pub)) (hmi : decMsg (segSzIn tr pub) ∈ L.init)
    (hs0 : s0.pages.size = pin) (hmfin : decMsg (segSzOut tr pub) ∈ L.fin) :
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p L.act.length s0 = .cont sN ∧
      BndCG X.ctx sg sN ((pub.getD pubTIn 0).toNat + L.act.length) (pub.getD pubSOut 0).toNat
        [pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((0 : Nat) : F), L.sbf, L.cidf] L.fin ∧
      RegWF sN ∧ SzC sN (· ∈ L.fin) ∧ sideR sN = σ ((pub.getD pubTIn 0).toNat + L.act.length + 1) ∧
      (pNout pub).toNat = 64 * sN.pages.size ∧
      ∃ (σ' : Nat → Nat) (A : List Nat), IdsOK L.fin A σ' ∧
        ∀ y, (∃ x ∈ (L.fin.filter (fun x => decide (keepA A x))).map (rlMsg σ'),
          x.space ≠ 3 ∧ x.space ≠ 7 ∧ x.space ≠ 8 ∧ fieldsOf x = y) ↔ y ∈ cutView X.ctx sN := by
  obtain ⟨-, sN, h1, -, h3, ⟨⟨⟨hreg, hsp⟩, hwf⟩, hsz⟩, h5, h6⟩ :=
    seg_sound_g H X hcode L ht hfee hstepgas hg64 h0 hQ0 hσ0 hin hout hpin hpout h8 hmi hs0 hmfin
  have hB : BndCG X.ctx sg sN ((pub.getD pubTIn 0).toNat + L.act.length) (pub.getD pubSOut 0).toNat
      [pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((0 : Nat) : F), L.sbf, L.cidf] L.fin :=
    ⟨h3, hreg, hsp⟩
  obtain ⟨σ', A, hIds, -, hv⟩ := cutView_eqLG (M2Ctx.toCtx_fns_nodup X.toM2) hB
  exact ⟨sN, h1, hB, hwf, hsz, h5, h6, σ', A, hIds, hv⟩

end

#print axioms seg_sound_g_view
#print axioms memg_kind
#print axioms memg_rowFacts
#print axioms seg_sound_g

end WasmBase
