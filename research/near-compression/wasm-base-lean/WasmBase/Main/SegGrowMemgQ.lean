import WasmBase.Main.SegGrowMemg
import WasmBase.Main.SegSpaceG
/-!
# WasmBase.Main.SegGrowMemgQ — a MEMG row keeps the grow segment's invariant (E2E M6, GROW2)

The invariant a grow segment carries (`QG`): the σ-form's `(RegC ∧ SpC) ∧ RegWF` with the space
clause widened to `SpCG` (the live size message, `Main/SegSpaceG.lean`), and the size clause `SzC`
(`Main/SegGrowStep.lean`).  Here every active MEMG row keeps it (`RowQJM`, with the row's charge
`fee + lin·n ≤ mf`):

* `memg_prod_grow` / `memg_prod_fail` / `memg_prod_size`: the shapes of a MEMG row's productions
  (a stack message and the new size message at the row's time);
* `memg_rowQ_regC`, `memg_rowQ_regWF` (the row runs a non-host instruction: registers unchanged),
  `memg_rowQ_spCG` (productions in spaces 0, 8, 3);
* `memg_growOk_rowQJM_szC`, `memg_growFail_rowQJM_szC`, `memg_size_rowQJM_szC` (the step is
  `step_memGrow_ok` / `_fail` / `step_memSize`'s by determinism; the produced size message carries
  the new page count);
* **`memg_growOk_rowQJM`**, **`memg_growFail_rowQJM`**, **`memg_size_rowQJM`**: `RowQJM X.ctx J QG mf`.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- **The invariant of a grow segment**: registers, spaces (with the size message), well-formed
registers, and the size clause. -/
def QG (s : St) (live : Msg → Prop) : Prop := ((RegC live s ∧ SpCG live) ∧ RegWF s) ∧ SzC s live

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

omit H in
theorem decMsg_space0 {l : List F} (h : l.getD 0 0 = ((0 : Nat) : F)) : (decMsg l).space = 0 := by
  simp only [decMsg, h]; rfl

omit H in
theorem decMsg_sz {a b : Nat} (ha : a < P) (hb : b < P) :
    decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((a : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((b : Nat) : F)] = szMsg a b := by
  simp only [decMsg, szMsg, List.getD_cons_succ, List.getD_cons_zero, Fp.toNat_cast_of_lt ha,
    Fp.toNat_cast_of_lt hb]
  rfl

/-- The productions of a successful grow row: a stack message and `szMsg (old + n) ts`. -/
theorem memg_prod_grow {r : Nat} (hr : r < tr.height 32) (hg : mgc tr r MemG.fGrow = 1)
    (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 1) :
    ∃ m1 : Msg, m1.space = 0 ∧ rowProd MemG.table tr pub 32 r =
      [m1, szMsg (mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1)) (mgc tr r cTs)] := by
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  obtain ⟨hle, -⟩ := memg_grow_ok_dec H hr hg hs hok
  have hm : maxPagesM3 = 2048 := rfl
  rw [(memg_grow_msgs (pub := pub) hg hs).2]
  have c2 : ((mgc tr r MemG.old : Nat) : F) + ((mgc tr r MemG.ok : Nat) : F) *
      (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)) =
      ((mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) : Nat) : F) := by
    rw [hok]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
  rw [c2, decMsg_sz (by omega) (hPr _)]
  exact ⟨_, decMsg_space0 rfl, rfl⟩

omit H in
/-- The productions of a failed grow row: a stack message and `szMsg old ts`. -/
theorem memg_prod_fail {r : Nat} (hg : mgc tr r MemG.fGrow = 1)
    (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 0) :
    ∃ m1 : Msg, m1.space = 0 ∧ rowProd MemG.table tr pub 32 r = [m1, szMsg (mgc tr r MemG.old) (mgc tr r cTs)] := by
  have hPr := rowNat_lt tr 32 r
  rw [(memg_grow_msgs (pub := pub) hg hs).2]
  have c2 : ((mgc tr r MemG.old : Nat) : F) + ((mgc tr r MemG.ok : Nat) : F) *
      (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)) =
      ((mgc tr r MemG.old : Nat) : F) := by rw [hok]; grind
  rw [c2, decMsg_sz (hPr _) (hPr _)]
  exact ⟨_, decMsg_space0 rfl, rfl⟩

/-- `ok = 0` and `lin = 0` on a size row. -/
theorem memg_size_zero {r : Nat} (hr : r < tr.height 32) (hg : mgc tr r MemG.fGrow = 0) :
    mgc tr r MemG.ok = 0 ∧ mgc tr r MemG.lin = 0 := by
  have hPr := rowNat_lt tr 32 r
  constructor
  · have h := H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr (v MemG.ok * (1 - v MemG.fGrow))
      (by rw [segG_t32']; simp [MemG.table, MemG.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memg_col_eval, hg] at h
    exact cast_zero_nat (hPr _) (by grind)
  · have h := H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr (v MemG.lin * (1 - v MemG.fGrow))
      (by rw [segG_t32']; simp [MemG.table, MemG.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memg_col_eval, hg] at h
    exact cast_zero_nat (hPr _) (by grind)

/-- The productions of a size row: a stack message and `szMsg old ts`; its consumption `szMsg old tz`. -/
theorem memg_prod_size {r : Nat} (hr : r < tr.height 32) (hg : mgc tr r MemG.fGrow = 0)
    (hs : mgc tr r MemG.fSize = 1) :
    (∃ m1 : Msg, m1.space = 0 ∧ rowProd MemG.table tr pub 32 r = [m1, szMsg (mgc tr r MemG.old) (mgc tr r cTs)]) ∧
      rowCons MemG.table tr pub 32 r = [szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)] := by
  have hPr := rowNat_lt tr 32 r
  obtain ⟨hok, -⟩ := memg_size_zero H hr hg
  obtain ⟨hc, hp⟩ := memg_size_msgs (pub := pub) hg hs hok
  rw [hc, hp, decMsg_sz (hPr _) (hPr _), decMsg_sz (hPr _) (hPr _)]
  exact ⟨⟨_, decMsg_space0 rfl, rfl⟩, rfl⟩

omit H in
/-- The consumptions of a grow row are in spaces 0 and 8. -/
theorem memg_cons_grow {r : Nat} (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) :
    ∀ x ∈ rowCons MemG.table tr pub 32 r, x.space = 0 ∨ x.space = 8 := by
  have hPr := rowNat_lt tr 32 r
  rw [(memg_grow_msgs (pub := pub) hg hs).1, decMsg_sz (hPr _) (hPr _)]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact Or.inl (decMsg_space0 rfl)
  · exact Or.inr rfl

/-! ## The register and space clauses -/

theorem memg_rowQ_regC (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (ha : mgc tr r MemG.fGrow = 1 ∧ mgc tr r MemG.fSize = 0 ∨ mgc tr r MemG.fGrow = 0 ∧ mgc tr r MemG.fSize = 1)
    {cons prod : List Msg} (hc : ∀ x ∈ cons, x.space = 0 ∨ x.space = 8)
    (hp : ∀ x ∈ prod, x.space = 0 ∨ x.space = 8 ∨ x.space = 3) :
    RowQ X.ctx (fun s live => RegC live s) (rowIn MemG.table tr pub 32 r) cons prod :=
  rowQ_reg_keep (fun x hx => by rcases hc x hx with h | h <;> omega)
    (fun x hx => by rcases hp x hx with h | h | h <;> omega)
    (regKeep_of_code (memg_codeNonHost H X hcode hr ha))

theorem memg_rowQ_regWF (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (ha : mgc tr r MemG.fGrow = 1 ∧ mgc tr r MemG.fSize = 0 ∨ mgc tr r MemG.fGrow = 0 ∧ mgc tr r MemG.fSize = 1)
    {cons prod : List Msg} :
    RowQ X.ctx (fun s _ => RegWF s) (rowIn MemG.table tr pub 32 r) cons prod :=
  rowQ_regWF_keep (regKeep_of_code (memg_codeNonHost H X hcode hr ha))

omit H in
theorem memg_rowQ_spCG {X : Ctx} {inS : List F} {cons prod : List Msg}
    (hp : ∀ x ∈ prod, x.space = 0 ∨ x.space = 8 ∨ x.space = 3) :
    RowQ X (fun _ live => SpCG live) inS cons prod :=
  rowQ_spaceG fun _ _ _ _ _ _ _ _ _ _ _ _ _ x hx => by
    rcases hp x hx with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))

/-! ## The size clause -/

omit H in
theorem zeroBytes_space3 {A : List Nat} {t : Nat} : ∀ x ∈ zeroBytes A t, x.space = 3 :=
  fun _ h => zeroBytes_space h

/-- **A successful grow row keeps the size clause.** -/
theorem memg_growOk_rowQJM_szC (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 1)
    {J : Nat → St → Prop} {mf : Nat}
    (hmf : mgc tr r cFee + mgc tr r MemG.lin * (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ mf)
    (A : List Nat) :
    RowQJM X.ctx J SzC mf (rowIn MemG.table tr pub 32 r) (rowCons MemG.table tr pub 32 r)
      (rowProd MemG.table tr pub 32 r ++ zeroBytes A (mgc tr r cTs)) := by
  intro E s f tps tpl t pc S live a b s' R hgas _ hin hl hst hQ
  obtain ⟨w, hins, hfee, hwn, hstk, hwt, hnext, hL1, hH1, -, -, hcons⟩ := memg_grow_at H X hcode hr hg hs R hin hl
  obtain ⟨m1, hm1, hprod⟩ := memg_prod_grow H hr hg hs hok
  rw [hcons] at hl ⊢
  have hz : live (szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)) := hl _ (by simp)
  have hpg : mgc tr r MemG.old = s.pages.size := SzC.pages hQ hz
  obtain ⟨hle, -⟩ := memg_grow_ok_dec H hr hg hs hok
  have hm : maxPagesM3 = 2048 := rfl
  have hokc : s.pages.size + w.toNat ≤ X.ctx.cfg.maxMemoryPages := by
    rw [M3Ctx.ctx_cfg, X.mf.maxPages]; omega
  have hg' : X.ctx.R * (S + (mgc tr r cFee + mgc tr r MemG.lin * w.toNat) - a) ≤ b :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by rw [hwn]; omega)) hgas
  rw [hpg] at hz
  obtain ⟨s'', hs'', hpg'', -, -⟩ := step_memGrow_ok X.ctx R hins hfee hstk hwt hg' hokc hnext hL1 hH1 hQ hz
    [] List.nodup_nil (by simp)
  rw [hst] at hs''
  cases hs''
  have hsz : s'.pages.size = mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) := by
    rw [hpg'', Array.size_append, Array.size_replicate, hpg, hwn]
  rw [hprod, hpg]
  refine SzC.swap hQ hz (by simp) (t := mgc tr r cTs) (fun x hx h8 => ?_) (by rw [hsz, hpg]; simp)
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · rw [hm1] at h8; exact absurd h8 (by decide)
  · rw [hsz, hpg]
  · rw [zeroBytes_space3 x hx] at h8; exact absurd h8 (by decide)

/-- **A failed grow row keeps the size clause.** -/
theorem memg_growFail_rowQJM_szC (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 0)
    {J : Nat → St → Prop} {mf : Nat}
    (hmf : mgc tr r cFee + mgc tr r MemG.lin * (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ mf) :
    RowQJM X.ctx J SzC mf (rowIn MemG.table tr pub 32 r) (rowCons MemG.table tr pub 32 r)
      (rowProd MemG.table tr pub 32 r) := by
  intro E s f tps tpl t pc S live a b s' R hgas _ hin hl hst hQ
  obtain ⟨w, hins, hfee, hwn, hstk, hwt, hnext, hL1, hH1, -, -, hcons⟩ := memg_grow_at H X hcode hr hg hs R hin hl
  obtain ⟨m1, hm1, hprod⟩ := memg_prod_fail (pub := pub) hg hs hok
  rw [hcons] at hl ⊢
  have hz : live (szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)) := hl _ (by simp)
  have hpg : mgc tr r MemG.old = s.pages.size := SzC.pages hQ hz
  obtain ⟨hgt, -⟩ := memg_grow_fail_dec H hr hg hs hok
  have hfail : X.ctx.cfg.maxMemoryPages < s.pages.size + w.toNat := by
    rw [M3Ctx.ctx_cfg, X.mf.maxPages]; omega
  have hg' : X.ctx.R * (S + (mgc tr r cFee + mgc tr r MemG.lin * w.toNat) - a) ≤ b :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by rw [hwn]; omega)) hgas
  rw [hpg] at hz
  obtain ⟨s'', hs'', hpg'', -, -⟩ := step_memGrow_fail X.ctx R hins hfee hstk hwt hg' hfail hnext hL1 hH1 hQ hz
  rw [hst] at hs''
  cases hs''
  rw [hprod, hpg]
  refine SzC.swap hQ hz (by simp) (t := mgc tr r cTs) (fun x hx h8 => ?_) (by rw [hpg'']; simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · rw [hm1] at h8; exact absurd h8 (by decide)
  · rw [hpg'']

/-- **A size row keeps the size clause.** -/
theorem memg_size_rowQJM_szC (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 0) (hs : mgc tr r MemG.fSize = 1) {J : Nat → St → Prop} {mf : Nat}
    (hmf : mgc tr r cFee ≤ mf) (hg64 : X.ctx.g0 < 2 ^ 64) :
    RowQJM X.ctx J SzC mf (rowIn MemG.table tr pub 32 r) (rowCons MemG.table tr pub 32 r)
      (rowProd MemG.table tr pub 32 r) := by
  intro E s f tps tpl t pc S live a b s' R hgas _ hin hl hst hQ
  obtain ⟨hins, hfee, hnext, hL1, hH1, -, -⟩ := memg_size_at H X hcode hr hg hs R hin
  obtain ⟨⟨m1, hm1, hprod⟩, hcons⟩ := memg_prod_size H hr hg hs
  rw [hcons] at hl ⊢
  have hz : live (szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)) := hl _ (by simp)
  have hpg : mgc tr r MemG.old = s.pages.size := SzC.pages hQ hz
  have hg' : X.ctx.R * (S + mgc tr r cFee - a) ≤ b :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hgas
  rw [hpg] at hz
  obtain ⟨s'', hs'', hpg'', -, -⟩ := step_memSize X.ctx R hins hfee hg' hg64 hnext hL1 hH1 hQ hz
  rw [hst] at hs''
  cases hs''
  rw [hprod, hpg]
  refine SzC.swap hQ hz (by simp) (t := mgc tr r cTs) (fun x hx h8 => ?_) (by rw [hpg'']; simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · rw [hm1] at h8; exact absurd h8 (by decide)
  · rw [hpg'']

/-! ## The whole invariant -/

/-- **A successful grow row keeps `QG`.** -/
theorem memg_growOk_rowQJM (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 1)
    {J : Nat → St → Prop} {mf : Nat}
    (hmf : mgc tr r cFee + mgc tr r MemG.lin * (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ mf)
    (A : List Nat) :
    RowQJM X.ctx J QG mf (rowIn MemG.table tr pub 32 r) (rowCons MemG.table tr pub 32 r)
      (rowProd MemG.table tr pub 32 r ++ zeroBytes A (mgc tr r cTs)) := by
  have ha : mgc tr r MemG.fGrow = 1 ∧ mgc tr r MemG.fSize = 0 ∨ mgc tr r MemG.fGrow = 0 ∧ mgc tr r MemG.fSize = 1 :=
    Or.inl ⟨hg, hs⟩
  obtain ⟨m1, hm1, hprod⟩ := memg_prod_grow H hr hg hs hok
  have hp : ∀ x ∈ rowProd MemG.table tr pub 32 r ++ zeroBytes A (mgc tr r cTs),
      x.space = 0 ∨ x.space = 8 ∨ x.space = 3 := by
    intro x hx
    rw [hprod] at hx
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inl hm1
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (zeroBytes_space3 x hx))
  have hc := memg_cons_grow (pub := pub) hg hs
  exact rowQJM_and (rowQJM_and (rowQJM_and
    (RowQJ.toM (RowQ.toJ (memg_rowQ_regC H X hcode hr ha hc hp)))
    (RowQJ.toM (RowQ.toJ (memg_rowQ_spCG hp))))
    (RowQJ.toM (RowQ.toJ (memg_rowQ_regWF H X hcode hr ha))))
    (memg_growOk_rowQJM_szC H X hcode hr hg hs hok hmf A)

/-- **A failed grow row keeps `QG`.** -/
theorem memg_growFail_rowQJM (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 0)
    {J : Nat → St → Prop} {mf : Nat}
    (hmf : mgc tr r cFee + mgc tr r MemG.lin * (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ mf) :
    RowQJM X.ctx J QG mf (rowIn MemG.table tr pub 32 r) (rowCons MemG.table tr pub 32 r)
      (rowProd MemG.table tr pub 32 r) := by
  have ha : mgc tr r MemG.fGrow = 1 ∧ mgc tr r MemG.fSize = 0 ∨ mgc tr r MemG.fGrow = 0 ∧ mgc tr r MemG.fSize = 1 :=
    Or.inl ⟨hg, hs⟩
  obtain ⟨m1, hm1, hprod⟩ := memg_prod_fail (pub := pub) hg hs hok
  have hp : ∀ x ∈ rowProd MemG.table tr pub 32 r, x.space = 0 ∨ x.space = 8 ∨ x.space = 3 := by
    intro x hx
    rw [hprod] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hm1
    · exact Or.inr (Or.inl rfl)
  have hc := memg_cons_grow (pub := pub) hg hs
  exact rowQJM_and (rowQJM_and (rowQJM_and
    (RowQJ.toM (RowQ.toJ (memg_rowQ_regC H X hcode hr ha hc hp)))
    (RowQJ.toM (RowQ.toJ (memg_rowQ_spCG hp))))
    (RowQJ.toM (RowQ.toJ (memg_rowQ_regWF H X hcode hr ha))))
    (memg_growFail_rowQJM_szC H X hcode hr hg hs hok hmf)

/-- **A size row keeps `QG`.** -/
theorem memg_size_rowQJM (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 0) (hs : mgc tr r MemG.fSize = 1) {J : Nat → St → Prop} {mf : Nat}
    (hmf : mgc tr r cFee ≤ mf) (hg64 : X.ctx.g0 < 2 ^ 64) :
    RowQJM X.ctx J QG mf (rowIn MemG.table tr pub 32 r) (rowCons MemG.table tr pub 32 r)
      (rowProd MemG.table tr pub 32 r) := by
  have ha : mgc tr r MemG.fGrow = 1 ∧ mgc tr r MemG.fSize = 0 ∨ mgc tr r MemG.fGrow = 0 ∧ mgc tr r MemG.fSize = 1 :=
    Or.inr ⟨hg, hs⟩
  obtain ⟨⟨m1, hm1, hprod⟩, hcons⟩ := memg_prod_size H hr hg hs
  have hp : ∀ x ∈ rowProd MemG.table tr pub 32 r, x.space = 0 ∨ x.space = 8 ∨ x.space = 3 := by
    intro x hx
    rw [hprod] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hm1
    · exact Or.inr (Or.inl rfl)
  have hc : ∀ x ∈ rowCons MemG.table tr pub 32 r, x.space = 0 ∨ x.space = 8 := by
    rw [hcons]; intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; exact Or.inr rfl
  exact rowQJM_and (rowQJM_and (rowQJM_and
    (RowQJ.toM (RowQ.toJ (memg_rowQ_regC H X hcode hr ha hc hp)))
    (RowQJ.toM (RowQ.toJ (memg_rowQ_spCG hp))))
    (RowQJ.toM (RowQ.toJ (memg_rowQ_regWF H X hcode hr ha))))
    (memg_size_rowQJM_szC H X hcode hr hg hs hmf hg64)

end

#print axioms memg_growOk_rowQJM
#print axioms memg_growFail_rowQJM
#print axioms memg_size_rowQJM

end WasmBase
