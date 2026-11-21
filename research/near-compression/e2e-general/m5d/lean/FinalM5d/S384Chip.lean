import FinalM5d.HbWhole
import StateM5a.WsDecode
import FinalM5d.RsRow

/-!
# FinalM5d.S384Chip — an active `S384` row is a chip compression (lane B's contract)

`s384_comp`: in a trace satisfying `finalAirS` (the chip stub's `IF384` sends are the chip's),
under lane B's `Sha512IfContract compress` on those sends, every active `S384` row's 32 limb
triples (`S384.ifLimbs`: `hin ‖ block ‖ hout`) are the 21-bit limbs of `h ‖ blk ‖ compress h blk`
for 64-bit words `h` (8) and `blk` (16) — through lane B's `Sha512If.comp_sound`.
With `S384Rec.sha384_of_blocks`, what remains for the `S384` table is the row chain (`hin` =
IV384 / the previous `hout`) and the padding (the blocks are `pad` of the received bytes).
-/

namespace FinalM5d.S384Chip

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.BusMem FinalM5d.Whole
open StateM5a.Bus StateM5a.Sha512If StateM5a.WsDecode

variable {tr : Trace Fp} {pub : List Fp}

/-- The row's 32 limb triples, as naturals. -/
def triples (tr : Trace Fp) (r : Nat) (pub : List Fp) : List (List Nat) :=
  (List.range 32).map fun k =>
    [ev tr 1 r pub (S384.ifLimbs.getD (3 * k) 0), ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 1) 0),
     ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 2) 0)]

/-- The row's `IF384` receive number `m`. -/
def ifRcv (m : Nat) : Interaction :=
  rcv B_IF384 S384.act ([S384.T.c "cid", K m] ++
    (List.range 6).map fun k => S384.ifLimbs.getD (6 * m + k) 0)

theorem ifRcv_mem {m : Nat} (hm : m < 16) : ifRcv m ∈ S384.interactions := by
  unfold S384.interactions
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)))

theorem triples_get {r k : Nat} (hk : k < 32) :
    (triples tr r pub).getD k zeroL =
      [ev tr 1 r pub (S384.ifLimbs.getD (3 * k) 0), ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 1) 0),
       ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 2) 0)] := by
  simp [triples, List.getD_eq_getElem?_getD, hk]

/-- **An active `S384` row is a chip compression.** -/
theorem s384_comp (h : Holds finalAirS pub tr) {compress : List Nat → List Nat → List Nat}
    (hcok : CompressOK compress)
    (hC : Sha512IfContract compress ((busList finalAirS tr pub B_IF384 true).map decIf))
    {r : Nat} (hr : r < tr.height 1) (hact : ev tr 1 r pub S384.act = 1) :
    ∃ hh blk : List Nat, hh.length = 8 ∧ blk.length = 16 ∧ W64 hh ∧ W64 blk ∧
      triples tr r pub = (hh ++ blk ++ compress hh blk).map StateM5a.wlimbs := by
  apply comp_sound hcok hC (cid := ev tr 1 r pub (S384.T.c "cid")) (by simp [triples])
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  have hm' := List.mem_range.1 hm
  have hmem : ifRcv m ∈ (finalAirS.tables[1]'(by decide)).interactions := by
    rw [tab1]; exact ifRcv_mem hm'
  have ho := occ_of (by decide) hr hmem ((multNat_one rfl).2 (evalOne hact))
  have hin := (mem_iff_of_holds h B_IF384 _).2 (mem_busList.2 ho)
  refine List.mem_map.2 ⟨_, hin, ?_⟩
  rw [triples_get (by omega), triples_get (by omega)]
  simp only [decIf, Interaction.msgVal, ifRcv, rcv, List.map_cons, List.map_append, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, IfMsg.mk.injEq]
  have e6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  simp only [e6, List.map_cons, List.map_nil, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show ((Expr.const m).eval tr 1 r pub).toNat = m
    exact (ev_const (tr := tr) (t := 1) (r := r) (pub := pub) m).trans (Nat.mod_eq_of_lt (by omega))
  · simp only [tn, show 3 * (2 * m) = 6 * m + 0 by omega, show 3 * (2 * m) + 1 = 6 * m + 1 by omega,
      show 3 * (2 * m) + 2 = 6 * m + 2 by omega]; rfl
  · simp only [tn, show 3 * (2 * m + 1) = 6 * m + 3 by omega,
      show 3 * (2 * m + 1) + 1 = 6 * m + 4 by omega, show 3 * (2 * m + 1) + 2 = 6 * m + 5 by omega]; rfl

/-! ## The chain between rows -/

theorem s384_link_sub :
    ((List.range 24).map fun k => Expr.isTransition * (S384.act - S384.last) *
      (S384.T.n "hin" k - S384.T.c "hout" k)) ⊆ S384.constraints := by
  intro e he; unfold S384.constraints
  simp only [List.mem_append]; simp only [he, true_or, or_true]

theorem s384_iv_sub :
    ((List.range 24).map fun k => S384.T.c "first" * (S384.T.c "hin" k - K (S384.ivLimbs.getD k 0))) ⊆
      S384.constraints := by
  intro e he; unfold S384.constraints
  simp only [List.mem_append]; simp only [he, true_or, or_true]

theorem s384_constr (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 1) :
    ∀ e ∈ S384.constraints, e.eval tr 1 r pub = 0 := by
  have := h.constr 1 (by decide) r hr
  rw [tab1] at this; exact this

/-- Inside a message (`act = 1`, `last = 0`, a next row), the next row's `hin` is this row's
`hout`. -/
theorem s384_link (h : Holds finalAirS pub tr) {r : Nat} (hr : r + 1 < tr.height 1)
    (hact : ev tr 1 r pub S384.act = 1) (hlast : ev tr 1 r pub S384.last = 0) {k : Nat} (hk : k < 24) :
    ev tr 1 (r + 1) pub (S384.T.c "hin" k) = ev tr 1 r pub (S384.T.c "hout" k) := by
  have hc := s384_constr h (r := r) (by omega) _
    (s384_link_sub (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  have htr : ev tr 1 r pub Expr.isTransition = 1 := by
    simp only [ev, Expr.eval, Expr.evalWith, rowEnv, show ¬ (r + 1 = tr.height 1) by omega, ite_false]; rfl
  have hnl : ev tr 1 r pub (S384.act - S384.last) = 1 := by
    rw [RsRow.ev_sub, hact, hlast]
  have h1 := gated hc (by rw [FinRow.ev_hmul, htr, hnl])
  have := ev_sub_eq h1
  rw [← this]
  simp only [ev, Expr.eval, Expr.evalWith, rowEnv, S384.T, Cols.n, Cols.c, ite_true,
    Bool.false_eq_true, ite_false, Nat.mod_eq_of_lt hr]

/-- On a first block, `hin` is the SHA-384 IV. -/
theorem s384_iv (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 1)
    (hf : ev tr 1 r pub (S384.T.c "first") = 1) {k : Nat} (hk : k < 24) :
    ev tr 1 r pub (S384.T.c "hin" k) = S384.ivLimbs.getD k 0 := by
  have hc := s384_constr h hr _ (s384_iv_sub (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  have := ev_sub_eq (gated hc hf)
  rw [this, FinRow.ev_K, Nat.mod_eq_of_lt]
  have : S384.ivLimbs.getD k 0 < 2 ^ 22 := by
    have hl : ∀ j, j < 24 → S384.ivLimbs.getD j 0 < 2 ^ 22 := by decide
    exact hl k hk
  omega

theorem ifLimbs_hin : ∀ j, j < 24 → S384.ifLimbs.getD j 0 = S384.T.c "hin" j := by decide +kernel
theorem ifLimbs_hout : ∀ j, j < 24 → S384.ifLimbs.getD (72 + j) 0 = S384.T.c "hout" j := by
  decide +kernel

/-- `hin` of the next row is `hout` of this one, as limb triples. -/
theorem triples_link (h : Holds finalAirS pub tr) {r : Nat} (hr : r + 1 < tr.height 1)
    (hact : ev tr 1 r pub S384.act = 1) (hlast : ev tr 1 r pub S384.last = 0) :
    (triples tr (r + 1) pub).take 8 = (triples tr r pub).drop 24 := by
  apply List.ext_getElem
  · simp [triples]
  · intro k h1 h2
    have hk : k < 8 := by simp [triples] at h1; omega
    simp only [triples, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [ifLimbs_hin _ (by omega), ifLimbs_hin _ (by omega), ifLimbs_hin _ (by omega)]
    rw [show 3 * (24 + k) = 72 + 3 * k by omega, Nat.add_assoc 72 (3 * k) 1, Nat.add_assoc 72 (3 * k) 2]
    rw [ifLimbs_hout (3 * k) (by omega), ifLimbs_hout (3 * k + 1) (by omega),
      ifLimbs_hout (3 * k + 2) (by omega),
      s384_link h hr hact hlast (by omega), s384_link h hr hact hlast (by omega),
      s384_link h hr hact hlast (by omega)]

/-- **One step of the `S384` chain**: inside a message, the next row's compression input is this
row's compression output. -/
theorem s384_step (h : Holds finalAirS pub tr) {compress : List Nat → List Nat → List Nat}
    (hcok : CompressOK compress)
    (hC : Sha512IfContract compress ((busList finalAirS tr pub B_IF384 true).map decIf))
    {r : Nat} (hr : r + 1 < tr.height 1) (hact : ev tr 1 r pub S384.act = 1)
    (hact' : ev tr 1 (r + 1) pub S384.act = 1) (hlast : ev tr 1 r pub S384.last = 0) :
    ∃ hh blk hh' blk' : List Nat, hh.length = 8 ∧ blk.length = 16 ∧ W64 hh ∧ W64 blk ∧
      hh'.length = 8 ∧ blk'.length = 16 ∧ W64 hh' ∧ W64 blk' ∧
      triples tr r pub = (hh ++ blk ++ compress hh blk).map StateM5a.wlimbs ∧
      triples tr (r + 1) pub = (hh' ++ blk' ++ compress hh' blk').map StateM5a.wlimbs ∧
      hh' = compress hh blk := by
  obtain ⟨hh, blk, l1, l2, w1, w2, e⟩ := s384_comp h hcok hC (by omega) hact
  obtain ⟨hh', blk', l1', l2', w1', w2', e'⟩ := s384_comp h hcok hC hr hact'
  refine ⟨hh, blk, hh', blk', l1, l2, w1, w2, l1', l2', w1', w2', e, e', ?_⟩
  have hl := triples_link h hr hact hlast
  rw [e, e'] at hl
  have e1 : ((hh' ++ blk' ++ compress hh' blk').map StateM5a.wlimbs).take 8 =
      hh'.map StateM5a.wlimbs := by
    rw [List.map_append, List.map_append, List.append_assoc]
    exact List.take_left' (by simp [l1'])
  have e2 : ((hh ++ blk ++ compress hh blk).map StateM5a.wlimbs).drop 24 =
      (compress hh blk).map StateM5a.wlimbs := by
    rw [List.map_append, List.map_append]
    exact List.drop_left' (by simp [l1, l2])
  rw [e1, e2] at hl
  exact StateM5a.Sha512If.map_wlimbs_inj hl

/-! ## Words and the chain over a message -/

/-- A limb triple back to its word. -/
def unl (l : List Nat) : Nat := l.getD 0 0 + 2 ^ 21 * l.getD 1 0 + 2 ^ 42 * l.getD 2 0

theorem unl_wlimbs {x : Nat} (hx : x < 2 ^ 64) : unl (StateM5a.wlimbs x) = x := by
  simp only [unl, StateM5a.wlimbs, List.getD_cons_zero, List.getD_cons_succ]
  omega

/-- Words `a … a+n−1` of the row's 32 interface words. -/
def words (tr : Trace Fp) (r : Nat) (pub : List Fp) (a n : Nat) : List Nat :=
  (((triples tr r pub).drop a).take n).map unl

theorem words_of {r : Nat} {hh blk : List Nat} {compress : List Nat → List Nat → List Nat}
    (hcok : CompressOK compress) (l1 : hh.length = 8) (l2 : blk.length = 16) (w1 : W64 hh)
    (w2 : W64 blk) (e : triples tr r pub = (hh ++ blk ++ compress hh blk).map StateM5a.wlimbs) :
    words tr r pub 0 8 = hh ∧ words tr r pub 8 16 = blk ∧ words tr r pub 24 8 = compress hh blk := by
  have hid : ∀ l : List Nat, W64 l → (l.map StateM5a.wlimbs).map unl = l := fun l hl => by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id l]
    apply List.map_congr_left
    intro x hx'; exact unl_wlimbs (hl x hx')
  have hc8 := (hcok hh blk).1
  unfold words
  rw [e, List.map_append, List.map_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.drop_zero, List.append_assoc, List.take_left' (by simp [l1]), hid hh w1]
  · rw [List.append_assoc, List.drop_left' (by simp [l1]), List.take_left' (by simp [l2]), hid blk w2]
  · rw [List.drop_left' (by simp [l1, l2]), List.take_of_length_le (by simp [hc8]),
      hid _ (hcok hh blk).2]

theorem iv_words {r : Nat} (h : Holds finalAirS pub tr) (hr : r < tr.height 1)
    (hf : ev tr 1 r pub (S384.T.c "first") = 1) :
    words tr r pub 0 8 = NearSpecV3.E2E.Bnd.IV384 := by
  have hiv : ∀ k, k < 8 → [S384.ivLimbs.getD (3 * k) 0, S384.ivLimbs.getD (3 * k + 1) 0,
      S384.ivLimbs.getD (3 * k + 2) 0] = StateM5a.wlimbs (NearSpecV3.E2E.Bnd.IV384.getD k 0) := by
    decide
  have hw : ∀ k, k < 8 → NearSpecV3.E2E.Bnd.IV384.getD k 0 < 2 ^ 64 := by decide
  apply List.ext_getElem
  · simp [words, triples, NearSpecV3.E2E.Bnd.IV384]
  · intro k h1 h2
    have hk : k < 8 := by simp [words, triples] at h1; omega
    simp only [words, triples, List.drop_zero, List.getElem_map, List.getElem_take,
      List.getElem_range]
    rw [ifLimbs_hin _ (by omega), ifLimbs_hin _ (by omega), ifLimbs_hin _ (by omega),
      s384_iv h hr hf (by omega), s384_iv h hr hf (by omega), s384_iv h hr hf (by omega), hiv k hk,
      unl_wlimbs (hw k hk), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-- **The `S384` chain over a message**: from a first row `r0` through `n` non-last active rows,
the compression input of row `r0 + n` is the fold of the compression over the rows' blocks from
the SHA-384 IV. -/
theorem s384_chain (h : Holds finalAirS pub tr) {compress : List Nat → List Nat → List Nat}
    (hcok : CompressOK compress)
    (hC : Sha512IfContract compress ((busList finalAirS tr pub B_IF384 true).map decIf))
    {r0 : Nat} (hf : ev tr 1 r0 pub (S384.T.c "first") = 1) :
    ∀ n, r0 + n < tr.height 1 → (∀ j, j ≤ n → ev tr 1 (r0 + j) pub S384.act = 1) →
      (∀ j, j < n → ev tr 1 (r0 + j) pub S384.last = 0) →
      words tr (r0 + n) pub 0 8 =
        (List.range n).foldl (fun hh j => compress hh (words tr (r0 + j) pub 8 16))
          NearSpecV3.E2E.Bnd.IV384
  | 0, hr, _, _ => by simpa using iv_words h hr hf
  | n + 1, hr, hact, hlast => by
    have ih := s384_chain h hcok hC hf n (by omega) (fun j hj => hact j (by omega))
      (fun j hj => hlast j (by omega))
    have hact1 : ev tr 1 (r0 + n + 1) pub S384.act = 1 := by
      have := hact (n + 1) (Nat.le_refl _); rwa [← Nat.add_assoc] at this
    obtain ⟨hh, blk, hh', blk', l1, l2, w1, w2, l1', l2', w1', w2', e, e', hstep⟩ :=
      s384_step h hcok hC (r := r0 + n) (by omega) (hact n (by omega)) hact1 (hlast n (by omega))
    obtain ⟨a1, a2, -⟩ := words_of hcok l1 l2 w1 w2 e
    obtain ⟨b1, -, -⟩ := words_of hcok l1' l2' w1' w2' e'
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih, a1, a2,
      show r0 + (n + 1) = r0 + n + 1 by omega, b1, hstep]

/-! ## Non-vacuity: precheck-accepted traces give `Holds finalAirS` with the chip's sends -/

/-- `IF384` is receive-only in `finalAir`, with 8-element messages (lane B's `ifOK`). -/
theorem final_ifOK : finalAir.tables.all (fun T => StateM5a.ChipStub.ifOK T.interactions) = true := by
  decide +kernel

/-- **The deployment** (lane B's `holds_of_holdsX` for the FINAL AIR): a trace of `finalAir`
accepted by the prover's precheck — every bus but `IF384` balanced (`HoldsX … B_IF384`), the
native chip's `IF384` sends `chip` a permutation of the receives — extends (Lean tables
unchanged) to a trace satisfying `Holds finalAirS` whose stub sends are exactly `chip`. So
`s384_comp`'s contract premise is the chip's faithfulness on its own sends. -/
theorem precheck_holds_final {tr : Trace Fp}
    (hX : StateM5a.ChipStub.HoldsX finalAir pub tr B_IF384)
    (chip : List (List Fp)) (hchip : chip.Perm (busList finalAir tr pub B_IF384 false))
    (hlen : chip.length ≤ 2 ^ 22) :
    ∃ tr' : Trace Fp,
      (∀ t < finalAir.tables.length, tr'.log t = tr.log t ∧ tr'.cell t = tr.cell t) ∧
      Holds finalAirS pub tr' ∧ busList finalAirS tr' pub B_IF384 true = chip := by
  have hok : ∀ T ∈ finalAir.tables, StateM5a.ChipStub.ifOK T.interactions = true :=
    fun T hT => List.all_eq_true.1 final_ifOK T hT
  have hns : ∀ T ∈ finalAir.tables, ∀ i ∈ T.interactions, ¬ (i.bus = B_IF384 ∧ i.send = true) :=
    fun T hT i hi ⟨hb, hs⟩ => by
      have := (StateM5a.ChipStub.of_ifOK (hok T hT) hi hb).1; rw [hs] at this; exact absurd this (by decide)
  have h8 : ∀ m ∈ chip, m.length = 8 := fun m hm =>
    StateM5a.ChipStub.busList_len _ tr pub B_IF384 false
      (fun T hT i hi hb _ => (StateM5a.ChipStub.of_ifOK (hok T hT) hi hb).2) m (hchip.mem_iff.1 hm)
  obtain ⟨tr', h1, h2, h3, -⟩ :=
    StateM5a.ChipStub.holds_of_holdsX (by decide) hX hns chip hchip h8 hlen
  exact ⟨tr', h1, h2, h3⟩

end FinalM5d.S384Chip
