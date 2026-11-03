import WasmBase.Main.SegMemPath
import WasmBase.Main.SegMemFrame

/-!
# WasmBase.Main.SegMemRoot — the memory-root conjunct of segment soundness (E2E M4c, sub-lane MEM)

Stated in `SegIface`'s terms (`MemGeom`, `MembIn`, `MemRootIn`, `MemRootOut`), for `wasmBaseSegAir`:

* `mp_chain`: MPATH's root chain (`rch_chain`) in bytes: the touched blocks, in `kb` order, are
  single-leaf updates of the tree (`write_access_pd`); without a SHA-384 collision every block's old
  leaf is the starting tree's leaf at its index, and `memOut` is the root of the starting tree with
  every touched leaf replaced by its new leaf.  Consistency of repeated indices comes from MEMB
  (`mp_cons_ro`: same index ⇒ same MEMB block, distinct `blk`; read-only ⇒ new leaf = old leaf).
* **`seg_membIn`** (item 1): `MemGeom pub s0 → MemRootIn pub s0 → MembIn tr pub s0 ∨ Sha384Coll`
  (no execution; the leaf is SHA-384 of MEMB's `bi` bytes, `memb_leaf_in`).
* **`seg_memRootOut`** (item 3): with the frame (`hpg`, `hfr`, from `SegMemFrame.seg_mem_frame`) and
  the out-boundary's memory part (`hout`, `membOut_of_bnd`): `MemRootOut pub sN ∧ MemGeom pub sN`, or
  a collision; includes the no-touched-block case.
* **`seg_mem_sound`** (item 4): packaged under `seg_sound`'s execution premises.

Named premises: `MemGeom pub s0` (the public depth/`nblk` are the in-state's: the previous
segment's out-geometry, or the initial memory's), `HostPagesRely` (M6, `SegMemFrame`), `CutiNoMem`
(CUTI produces no space-3 message: its rows are the previous segment's `cutView`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
open NearSpecV3.Wasm hiding P
open NearSpecV3.E2E.Bnd (Sha384Coll sha384 sha384_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace MemRoot

open StateM5a.Merkle

/-! ## 1. MEMB rows -/

theorem memb_send_filter : Memb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
    (List.range 128).map fun i => chSend 3 (Memb.addr i) 0 [Memb.c s!"bi{i}", 0, 0, 0] (pv pubTIn) Memb.kD := by
  decide +kernel

theorem memb_recv_mem (i : Nat) (hi : i < 128) :
    chRecv 3 (Memb.addr i) 0 [Memb.c s!"bo{i}", 0, 0, 0] (Memb.c s!"tq{i}") Memb.kD ∈ Memb.table.inters := by
  show _ ∈ Memb.inters
  unfold Memb.inters
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ ?_)))))
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem mem_rowMsgs_of {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {i : Inter}
    (hi : i ∈ T.inters) (hb : i.bus = b) (hs : i.send = s) (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub t r)) ∈ rowMsgs T tr pub t r b s := by
  rw [rowMsgs_eq]
  exact List.mem_filterMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hb, hs]⟩, by simp [hc]⟩

section memb
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

theorem memb_act_of_p {r i : Nat} (hr : r < tr.height 19) (hi : i < 9) (hp : mbN tr r (1 + i) = 1) :
    mbN tr r 0 = 1 := by
  obtain ⟨ha, -, hs⟩ := memb_row H hr
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.reduceAdd] at hp) <;> omega

/-- A row with `p8 = 1` is an active padding row `9b + 8`. -/
theorem memb_pad_of_p8 {r : Nat} (hr : r < tr.height 19) (hp : mbN tr r 9 = 1) :
    mbN tr r 0 = 1 ∧ r % 9 = 8 := by
  have ha := memb_act_of_p H hr (i := 8) (by decide) hp
  refine ⟨ha, Classical.byContradiction fun hne => ?_⟩
  have := memb_onehot H hr (k := r % 9) (j := 8) (Nat.mod_lt _ (by decide)) (by decide) hne (memb_pos H r hr ha).2
  rw [show 1 + 8 = 9 from rfl, hp] at this
  exact absurd this (by decide)

/-- An active data row is followed by an active row. -/
theorem memb_fwd {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hk : r % 9 < 8) :
    r + 1 < tr.height 19 ∧ mbN tr (r + 1) 0 = 1 := by
  have hp := (memb_pos H r hr ha).2
  have hm : r % 9 < 9 := by omega
  by_cases hl : r + 1 = tr.height 19
  · exfalso
    have l1 : Expr.last.eval (tr.row pub 19 r) = 1 := by simp [Expr.eval, Trace.row, hl]
    have h := memb_C H hr (Expr.last * Memb.c "act" * (1 - Memb.p 8)) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_p_eval tr pub r (show 8 < 9 by decide), ha, l1, cast_one] at h
    have h8 : mbN tr r (1 + 8) = 1 :=
      natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    have := memb_onehot H hr (k := r % 9) (j := 8) hm (by decide) (by omega) hp
    rw [h8] at this; exact absurd this (by decide)
  · have hr1 : r + 1 < tr.height 19 := by omega
    have hmem : Expr.trans * Memb.p (r % 9) * (1 - nv (ix Memb.cols s!"p{r % 9 + 1}")) ∈ Memb.constraints := by
      unfold Memb.constraints
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))))))
      exact List.mem_map.mpr ⟨r % 9, List.mem_range.mpr hk, rfl⟩
    have h := memb_C H hr _ hmem
    rw [mb_ix_p (r % 9 + 1) (by omega)] at h
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r hm, nv,
      Expr.eval_nxt, trans_eval_one tr pub 19 r hr1, hp, cast_one] at h
    simp only [Trace.row, Nat.mod_eq_of_lt hr1, cell_cast] at h
    have hn : mbN tr (r + 1) (1 + (r % 9 + 1)) = 1 :=
      natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    exact ⟨hr1, memb_act_of_p H hr1 (i := r % 9 + 1) (by omega) hn⟩

/-- An active data row's block has an active padding row. -/
theorem memb_pad_of_data {b k : Nat} (hr : 9 * b + k < tr.height 19) (ha : mbN tr (9 * b + k) 0 = 1)
    (hk : k < 8) : 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 := by
  have key : ∀ d k, k + d = 8 → 9 * b + k < tr.height 19 → mbN tr (9 * b + k) 0 = 1 →
      9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 := by
    intro d
    induction d with
    | zero => intro k hk hr ha; rw [show k = 8 by omega] at hr ha; exact ⟨hr, ha⟩
    | succ d ih =>
      intro k hk hr ha
      obtain ⟨h1, h2⟩ := memb_fwd H hr ha (by omega)
      exact ih (k + 1) (by omega) (by omega) (by rw [show 9 * b + (k + 1) = 9 * b + k + 1 by omega]; exact h2)
  exact key (8 - k) k (by omega) hr ha

/-- The two byte interactions of an active data row, evaluated. -/
theorem memb_msg_eval {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hk : r % 9 < 8)
    {i : Nat} (hi : i < 128) :
    (Memb.kD.eval (tr.row pub 19 r)).toNat = 1 ∧
    (chSend 3 (Memb.addr i) 0 [Memb.c s!"bi{i}", 0, 0, 0] (pv pubTIn) Memb.kD).msg.map (·.eval (tr.row pub 19 r)) =
      [((3 : Nat) : F), ((1024 * mbN tr r 10 + 128 * (r % 9) + i : Nat) : F), ((0 : Nat) : F),
        ((mbN tr r (14 + i) : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), pub.getD pubTIn 0] ∧
    (chRecv 3 (Memb.addr i) 0 [Memb.c s!"bo{i}", 0, 0, 0] (Memb.c s!"tq{i}") Memb.kD).msg.map
        (·.eval (tr.row pub 19 r)) =
      [((3 : Nat) : F), ((1024 * mbN tr r 10 + 128 * (r % 9) + i : Nat) : F), ((0 : Nat) : F),
        ((mbN tr r (142 + i) : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
        (Memb.c s!"tq{i}").eval (tr.row pub 19 r)] := by
  have hp := (memb_pos H r hr ha).2
  obtain ⟨k, hkdef⟩ : ∃ k, k = r % 9 := ⟨_, rfl⟩
  rw [← hkdef] at hp hk ⊢
  have oh : ∀ j, j < 9 → mbN tr r (1 + j) = if j = k then 1 else 0 := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk; simpa using hp
    · rw [if_neg hjk]; exact memb_onehot H hr (k := k) (by omega) hj (Ne.symm hjk) hp
  have pe : ∀ j, j < 9 → (Memb.p j).eval (tr.row pub 19 r) = (((if j = k then 1 else 0 : Nat) : Nat) : F) := by
    intro j hj; rw [memb_p_eval tr pub r hj, oh j hj]
  have kD1 : (Memb.kD.eval (tr.row pub 19 r)).toNat = 1 := by
    have e8 : Memb.kD = 0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 +
        Memb.p 7 := rfl
    rw [e8]
    simp only [Expr.eval_add', Expr.eval_ofNat', pe 0 (by decide), pe 1 (by decide), pe 2 (by decide),
      pe 3 (by decide), pe 4 (by decide), pe 5 (by decide), pe 6 (by decide), pe 7 (by decide)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      h | h | h | h | h | h | h | h <;> simp [h] <;> decide
  have kk : Memb.kk.eval (tr.row pub 19 r) = ((k : Nat) : F) := by
    have e9 : Memb.kk = 0 + Expr.c 0 * Memb.p 0 + Expr.c 1 * Memb.p 1 + Expr.c 2 * Memb.p 2 +
        Expr.c 3 * Memb.p 3 + Expr.c 4 * Memb.p 4 + Expr.c 5 * Memb.p 5 + Expr.c 6 * Memb.p 6 +
        Expr.c 7 * Memb.p 7 + Expr.c 8 * Memb.p 8 := rfl
    rw [e9]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, pe 0 (by decide),
      pe 1 (by decide), pe 2 (by decide), pe 3 (by decide), pe 4 (by decide), pe 5 (by decide),
      pe 6 (by decide), pe 7 (by decide), pe 8 (by decide)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      h | h | h | h | h | h | h | h <;> simp [h] <;> decide
  have hbo : ix Memb.cols s!"bo{i}" = 142 + i := SegSha.mb_ix_bo i hi
  refine ⟨kD1, ?_, ?_⟩
  · simp only [chSend, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Memb.addr,
      Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, memb_c_eval, mb_ix.2.1, kk,
      mb_ix_bi i hi, pv, Expr.eval_pub]
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    try rfl
  · simp only [chRecv, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Memb.addr,
      Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, memb_c_eval, mb_ix.2.1, kk, hbo]
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    try rfl

theorem memb_kD_inact {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 ≠ 1) :
    (Memb.kD.eval (tr.row pub 19 r)).toNat ≠ 1 := by
  obtain ⟨h1, -, hs⟩ := memb_row H hr
  have z : ∀ j, j < 8 → (Memb.p j).eval (tr.row pub 19 r) = 0 := by
    intro j hj
    rw [memb_p_eval tr pub r (by omega)]
    have : mbN tr r (1 + j) = 0 := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.reduceAdd]) <;> omega
    rw [this]; rfl
  have e8 : Memb.kD = 0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 +
      Memb.p 7 := rfl
  rw [e8]
  simp only [Expr.eval_add', Expr.eval_ofNat', z 0 (by decide), z 1 (by decide), z 2 (by decide),
    z 3 (by decide), z 4 (by decide), z 5 (by decide), z 6 (by decide), z 7 (by decide)]
  decide

/-- `blk < 2^16` and `blk < nblk` on an active padding row (MEMB's R16 checks). -/
theorem memb_blk_lt {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 < 65536 ∧ mbN tr (9 * b + 8) 10 < (pub.getD pubNblk 0).toNat ∧
      (pub.getD pubNblk 0).toNat ≤ mbN tr (9 * b + 8) 10 + 65536 := by
  have hP := P_val
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_pos H _ hr ha).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have hc : ((Memb.p 8).eval (tr.row pub 19 (9 * b + 8))).toNat = 1 := by
    rw [memb_p_eval tr pub _ (by decide), hp8]; rfl
  have m1 : r16 (Memb.c "blk") (Memb.p 8) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]; show _ ∈ Memb.inters; unfold Memb.inters
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m2 : r16 (pv pubNblk - 1 - Memb.c "blk") (Memb.p 8) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]; show _ ∈ Memb.inters; unfold Memb.inters
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  have l1 := seg_r16_lt H (seg_hsend_r16 H) ht hr m1 hc
  have l2 := seg_r16_lt H (seg_hsend_r16 H) ht hr m2 hc
  rw [memb_c_eval, mb_ix.2.1, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at l1
  simp only [Expr.eval_sub', memb_c_eval, mb_ix.2.1, pv, Expr.eval_pub, Expr.eval_ofNat'] at l2
  simp only [Trace.row] at l2
  change mbN tr (9 * b + 8) 10 < 65536 at l1
  generalize hN : pub.getD pubNblk 0 = N at l2
  generalize hB : mbN tr (9 * b + 8) 10 = B at l1 l2
  have e : N = ((Fp.toNat (N - ((1 : Nat) : F) - ((B : Nat) : F)) + 1 + B : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]; grind
  have := congrArg Fp.toNat e
  rw [Fp.toNat_cast_of_lt (by omega)] at this
  exact ⟨l1, by omega, by omega⟩

theorem memb_bi_lt' {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) {i : Nat}
    (hi : i < 128) : mbN tr r (14 + i) < 256 := by
  have := SegSha.memb_bi_lt H hr ha hq i hi
  rwa [mb_ix_bi i hi] at this

/-- **MEMB's in-side productions.**  Every message MEMB produces is byte `bi_i` of a data row
`9b + k` of an active block, at address `1024·blk + 128·k + i`, time `t_in`. -/
theorem memb_prod_form {x : Msg} (hx : x ∈ (part Memb.table tr pub 19 busStk true).map decMsg) :
    ∃ b k i, k < 8 ∧ i < 128 ∧ 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 ∧
      x = ⟨3, 1024 * mbN tr (9 * b + 8) 10 + 128 * k + i, 0, mbN tr (9 * b + k) (14 + i), 0, 0, 0,
        (pub.getD pubTIn 0).toNat⟩ := by
  have hP := P_val
  obtain ⟨r, hr, m, hm, rfl⟩ := mem_part_dec.mp hx
  rw [rowMsgs_eq] at hm
  obtain ⟨i0, hi0, he⟩ := List.mem_filterMap.mp hm
  rw [memb_send_filter] at hi0
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi0
  have hi' := List.mem_range.mp hi
  split at he
  · rename_i hc
    cases he
    change (Memb.kD.eval (tr.row pub 19 r)).toNat = 1 at hc
    have ha : mbN tr r 0 = 1 := Classical.byContradiction fun h => memb_kD_inact H hr h hc
    have hk : r % 9 < 8 := by
      refine Classical.byContradiction fun h => ?_
      have := ((SegSha.memb_kDkP H hr ha).2 (by omega)).1
      rw [this] at hc; exact absurd hc (by decide)
    obtain ⟨-, e1, -⟩ := memb_msg_eval H hr ha hk hi'
    obtain ⟨hr8, ha8⟩ := memb_pad_of_data H (b := r / 9) (k := r % 9) (by rw [Nat.div_add_mod]; exact hr)
      (by rw [Nat.div_add_mod]; exact ha) hk
    have hbc := memb_blk_const H hr8 ha8 (r % 9) (by omega)
    rw [Nat.div_add_mod] at hbc
    have hbl := (memb_blk_lt H hr8 ha8).1
    have hbi := memb_bi_lt' H hr ha hk hi'
    refine ⟨r / 9, r % 9, i, hk, hi', hr8, ha8, ?_⟩
    simp only [Nat.div_add_mod]
    rw [e1, ← hbc]
    simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ]
    rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
      Fp.toNat_cast_of_lt (by omega)]
  · cases he

/-- **MEMB's out-side consumptions.**  For every data row `9b + k` of an active block and every
`i < 128`, MEMB consumes `bo_i` at address `1024·blk + 128·k + i` (some producer time). -/
theorem memb_cons_mem {b k i : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hk : k < 8) (hi : i < 128) :
    ∃ tp, (⟨3, 1024 * mbN tr (9 * b + 8) 10 + 128 * k + i, 0, mbN tr (9 * b + k) (142 + i), 0, 0, 0, tp⟩ : Msg) ∈
      (part Memb.table tr pub 19 busStk false).map decMsg := by
  have hP := P_val
  have hr : 9 * b + k < tr.height 19 := by omega
  have ha : mbN tr (9 * b + k) 0 = 1 := (memb_pos H _ hr8 ha8).1 _ (by omega)
  have hm : (9 * b + k) % 9 = k := by omega
  obtain ⟨hc, -, e2⟩ := memb_msg_eval H hr ha (by omega) hi
  have hbc := memb_blk_const H hr8 ha8 k (by omega)
  have hbl := (memb_blk_lt H hr8 ha8).1
  have hbo : mbN tr (9 * b + k) (142 + i) < P := rowNat_lt _ _ _ _
  refine ⟨((Memb.c s!"tq{i}").eval (tr.row pub 19 (9 * b + k))).toNat,
    mem_part_dec.mpr ⟨9 * b + k, hr, _, mem_rowMsgs_of (memb_recv_mem i hi) rfl rfl hc, ?_⟩⟩
  rw [e2, hm, hbc]
  simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ]
  rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
    Fp.toNat_cast_of_lt hbo]

/-- **An active padding row's leaf message reaches an MPATH bottom row** (LEAF bus, send ⇒ receive). -/
theorem memb_leaf_send {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1) :
    ∃ r0, r0 < tr.height 20 ∧ mc tr r0 0 = 1 ∧ mc tr r0 1 = 1 ∧
      [mc tr r0 5, mc tr r0 4] ++ mdig tr r0 12 ++ mdig tr r0 30 =
        [bc tr (9 * b + 8) 10, bc tr (9 * b + 8) 11] ++ bdig tr (9 * b + 8) 486 ++ bdig tr (9 * b + 8) 534 := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_pos H _ hr8 ha8).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have hi : (⟨busLeaf, true, Memb.p 8, [Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++
      (names "hoO" 18).map Memb.c⟩ : Inter) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]
    have : (⟨busLeaf, true, Memb.p 8, [Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++
        (names "hoO" 18).map Memb.c⟩ : Inter) ∈ Memb.table.inters.filter (fun i => i.bus = 15) := by
      rw [memb_leaf]; exact List.mem_cons_self
    exact (List.mem_filter.mp this).1
  have hc : ((Memb.p 8).eval (tr.row pub 19 (9 * b + 8))).toNat = 1 := by
    rw [memb_p_eval tr pub _ (by decide), hp8]; rfl
  have hocc := occ_of_inter ht hr8 hi hc
  have hmsg : ([Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++ (names "hoO" 18).map Memb.c).map
      (·.eval (tr.row pub 19 (9 * b + 8))) =
      [bc tr (9 * b + 8) 10, bc tr (9 * b + 8) 11] ++ bdig tr (9 * b + 8) 486 ++ bdig tr (9 * b + 8) 534 := by
    obtain ⟨-, ib, iro⟩ := mb_ix
    simp only [List.map_append, List.map_cons, List.map_nil, Memb.c, ib, iro]
    rw [bdig_eval tr pub _ 486 "hoI" (fun l hl => (mb_ix_ho l hl).1),
      bdig_eval tr pub _ 534 "hoO" (fun l hl => (mb_ix_ho l hl).2)]
    rfl
  simp only at hocc
  rw [hmsg] at hocc
  have hbit : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = 15 → o.2.1 = true → o.2.2.2 ≤ 1 := by
    intro o ho hb hs
    rcases leaf_occ H ho hb with ⟨r, hr, rfl⟩ | ⟨r, -, rfl⟩
    · show (bc tr r 9).toNat ≤ 1
      rcases memb_p_bit H hr (i := 8) (by decide) with h | h <;> rw [h] <;> decide
    · simp at hs
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 15 hbit hocc rfl rfl rfl
  rcases leaf_occ H ho' hb' with ⟨r', -, rfl⟩ | ⟨r0, hr0, rfl⟩
  · simp at hs'
  · simp only at hm' hc'
    have hb1 : mc tr r0 1 = 1 := by
      rcases (mp_bool H hr0).2.1 with h | h
      · rw [h] at hc'; exact absurd rfl hc'
      · exact h
    have ha1 : mc tr r0 0 = 1 := by
      rcases (mp_bool H hr0).1 with h | h
      · have := ((mp_local H hr0).2.2.2 h).1; rw [hb1] at this; exact absurd this (by decide)
      · exact h
    exact ⟨r0, hr0, ha1, hb1, hm'⟩

/-- **An MPATH bottom row's leaf message comes from an active padding row `9b + 8`.** -/
theorem mp_leaf {r0 : Nat} (hr0 : r0 < tr.height 20) (hb : mc tr r0 1 = 1) :
    ∃ b, 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 ∧
      mc tr r0 5 = bc tr (9 * b + 8) 10 ∧ mc tr r0 4 = bc tr (9 * b + 8) 11 ∧
      mdig tr r0 12 = bdig tr (9 * b + 8) 486 ∧ mdig tr r0 30 = bdig tr (9 * b + 8) 534 := by
  obtain ⟨r', hr', hp8, he⟩ := leaf_link H hr0 hb
  have hp8' : mbN tr r' 9 = 1 := by
    have : bc tr r' 9 = ((mbN tr r' 9 : Nat) : F) := cell_cast tr 19 r' 9
    rw [this] at hp8
    exact natEq (R := 1) (by rw [hp8]; rfl) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
  obtain ⟨ha, hm⟩ := memb_pad_of_p8 H hr' hp8'
  have e : r' = 9 * (r' / 9) + 8 := by omega
  refine ⟨r' / 9, by rw [← e]; exact hr', by rw [← e]; exact ha, ?_⟩
  rw [← e]
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
  obtain ⟨a, b, c⟩ := he
  obtain ⟨c1, c2⟩ := List.append_inj c (by simp [bdig, mdig])
  exact ⟨a.symm, b.symm, c1.symm, c2.symm⟩

/-- A read-only block's leaf message has new = old (MEMB: `p8·ro·(hoO − hoI) = 0`). -/
theorem memb_ro_leaf {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hro : bc tr (9 * b + 8) 11 = 1) :
    bdig tr (9 * b + 8) 534 = bdig tr (9 * b + 8) 486 := by
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_pos H _ hr8 ha8).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  unfold bdig
  apply List.map_congr_left; intro l hl
  have hl' := List.mem_range.mp hl
  have hmem : Memb.p 8 * Memb.c "ro" * (Memb.c s!"hoO{l}" - Memb.c s!"hoI{l}") ∈ Memb.constraints := by
    unfold Memb.constraints
    exact List.mem_append_right _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
  have h := memb_C H hr8 _ hmem
  simp only [Expr.eval_mul', Expr.eval_sub', memb_p_eval tr pub _ (show 8 < 9 by decide), hp8, memb_c_eval,
    mb_ix.2.2, (mb_ix_ho l hl').1, (mb_ix_ho l hl').2] at h
  have e : ∀ i, bc tr (9 * b + 8) i = ((mbN tr (9 * b + 8) i : Nat) : F) := fun i => cell_cast tr 19 _ i
  rw [e] at hro
  rw [hro, e, e] at *
  rw [cast_one] at h
  grind

end memb

/-! ## 2. The root chain as a sequence of leaf updates -/

theorem top_exists (tr : Trace) : ∀ n j, j < topCount tr n → ∃ r, r < n ∧ mc tr r 2 = 1 ∧ topCount tr r = j := by
  intro n
  induction n with
  | zero => intro j h; simp [topCount] at h
  | succ n ih =>
    intro j h
    rw [topCount_succ] at h
    by_cases ht : mc tr n 2 = 1
    · rw [if_pos ht] at h
      by_cases hj : j < topCount tr n
      · obtain ⟨r, a, b, c⟩ := ih j hj; exact ⟨r, by omega, b, c⟩
      · exact ⟨n, by omega, ht, by omega⟩
    · rw [if_neg ht] at h
      obtain ⟨r, a, b, c⟩ := ih j (by omega); exact ⟨r, by omega, b, c⟩

theorem top_lt (tr : Trace) {r n : Nat} (hr : r < n) (ht : mc tr r 2 = 1) : topCount tr r < topCount tr n := by
  have := topCount_mono tr (show r + 1 ≤ n by omega)
  rw [topCount_succ, if_pos ht] at this; omega

open Classical in
/-- The leaf list after the updates of the blocks `r0` with `Q r0`: a touched index carries the
block's new leaf, an untouched one `L0`'s. -/
noncomputable def Tset (tr : Trace) (D : Nat) (L0 : List ArenaCore.Bytes) (Q : Nat → Prop) :
    List ArenaCore.Bytes :=
  (List.range (2 ^ D)).map fun i =>
    if h : ∃ r0, Q r0 ∧ natOf D (mpBits tr r0) = i then bytesOf (mdig tr (Classical.choose h) 30) else L0.getD i []

theorem Tset_length (tr : Trace) (D : Nat) (L0 : List ArenaCore.Bytes) (Q : Nat → Prop) :
    (Tset tr D L0 Q).length = 2 ^ D := by simp [Tset]

theorem Tset_pos {tr : Trace} {D : Nat} {L0 : List ArenaCore.Bytes} {Q : Nat → Prop} {i r0 : Nat}
    (hi : i < 2 ^ D) (hq : Q r0) (hb : natOf D (mpBits tr r0) = i)
    (hc : ∀ r0', Q r0' → natOf D (mpBits tr r0') = i → bytesOf (mdig tr r0' 30) = bytesOf (mdig tr r0 30)) :
    (Tset tr D L0 Q)[i]? = some (bytesOf (mdig tr r0 30)) := by
  have h : ∃ r0, Q r0 ∧ natOf D (mpBits tr r0) = i := ⟨r0, hq, hb⟩
  simp only [Tset, List.getElem?_map, List.getElem?_range hi, Option.map_some, dif_pos h]
  exact congrArg some (hc _ (Classical.choose_spec h).1 (Classical.choose_spec h).2)

theorem Tset_neg {tr : Trace} {D : Nat} {L0 : List ArenaCore.Bytes} {Q : Nat → Prop} {i : Nat}
    (hL : L0.length = 2 ^ D) (hno : ∀ r0, Q r0 → natOf D (mpBits tr r0) ≠ i) :
    (Tset tr D L0 Q)[i]? = L0[i]? := by
  by_cases hi : i < 2 ^ D
  · have h : ¬ ∃ r0, Q r0 ∧ natOf D (mpBits tr r0) = i := fun ⟨r0, a, b⟩ => hno r0 a b
    simp only [Tset, List.getElem?_map, List.getElem?_range hi, Option.map_some, dif_neg h]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  · rw [List.getElem?_eq_none (by rw [Tset_length]; omega), List.getElem?_eq_none (by omega)]

section chain
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **The root chain, in bytes.**  If `L0` (2^D 48-byte leaves) has root `m0 = memIn`, the touched
blocks are consistent (the same index has the same old and new leaf) and read-only blocks keep
their leaf, then without a SHA-384 collision every block's old leaf is `L0`'s leaf at its index, and
`memOut` is the root of `L0` with every touched leaf replaced by its new leaf. -/
theorem mp_chain {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {D : Nat} (hD : (pub.getD pubDepth 0).toNat = D) (hD1 : 1 ≤ D) (hn : ¬ Sha384Coll)
    {L0 : List ArenaCore.Bytes} (hL0 : L0.length = 2 ^ D) (hL48 : ∀ y ∈ L0, D48 y) {m0 : ArenaCore.Bytes}
    (hr0 : root StateM5a.StateView.nodeH D L0 = some m0) (hm0 : Canon (pubDig pub pubMemIn) m0)
    (hcons : ∀ r0 r r0' r', MpBlock tr r0 r → MpBlock tr r0' r' →
      natOf D (mpBits tr r0) = natOf D (mpBits tr r0') →
      bytesOf (mdig tr r0 12) = bytesOf (mdig tr r0' 12) ∧ bytesOf (mdig tr r0 30) = bytesOf (mdig tr r0' 30))
    (hro : ∀ r0 r, MpBlock tr r0 r → mc tr r0 4 = 1 → bytesOf (mdig tr r0 30) = bytesOf (mdig tr r0 12)) :
    (∀ r0 r, MpBlock tr r0 r → L0[natOf D (mpBits tr r0)]? = some (bytesOf (mdig tr r0 12))) ∧
    ∃ mf, Canon (pubDig pub pubMemOut) mf ∧
      root StateM5a.StateView.nodeH D (Tset tr D L0 fun r0 => ∃ r, MpBlock tr r0 r) = some mf := by
  have BB := fun {r0 r : Nat} (hB : MpBlock tr r0 r) => mp_block_bytes H hC hB hD hD1
  have old48 : ∀ r0 r, MpBlock tr r0 r → D48 (bytesOf (mdig tr r0 12)) :=
    fun r0 r hB => (BB hB).2.2.1.d48
  have new48 : ∀ r0 r, MpBlock tr r0 r → D48 (bytesOf (mdig tr r0 30)) := by
    intro r0 r hB
    rcases (BB hB).2.2.2.2.2.2.2.2.2 with h | h
    · exact ((BB hB).2.2.2.2.1 h).1.d48
    · rw [hro r0 r hB h]; exact old48 r0 r hB
  let nb := topCount tr (tr.height 20)
  let Qj : Nat → Nat → Prop := fun j r0 => ∃ r, MpBlock tr r0 r ∧ topCount tr r < j
  have T48 : ∀ j, ∀ y ∈ Tset tr D L0 (Qj j), D48 y := by
    intro j y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    split
    · rename_i h
      obtain ⟨r, hB, -⟩ := (Classical.choose_spec h).1
      exact new48 _ r hB
    · have hi' : i < L0.length := by have := List.mem_range.mp hi; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      exact hL48 _ (List.getElem_mem _)
  have hcQ : ∀ j i r0, (∃ r, MpBlock tr r0 r) → ∀ r0', Qj j r0' → natOf D (mpBits tr r0') = i →
      natOf D (mpBits tr r0) = i → bytesOf (mdig tr r0' 30) = bytesOf (mdig tr r0 30) := by
    rintro j i r0 ⟨r, hB⟩ r0' ⟨r', hB', -⟩ e1 e2
    exact (hcons r0' r' r0 r hB' hB (e1.trans e2.symm)).2
  -- the invariant
  have inv : ∀ j, j ≤ nb →
      (∀ r0 r, MpBlock tr r0 r → topCount tr r < j → L0[natOf D (mpBits tr r0)]? = some (bytesOf (mdig tr r0 12))) ∧
      ∃ mj, root StateM5a.StateView.nodeH D (Tset tr D L0 (Qj j)) = some mj ∧
        (∀ r, r < tr.height 20 → mc tr r 2 = 1 → topCount tr r = j → Canon (mdig tr r 114) mj) ∧
        (j = nb → Canon (pubDig pub pubMemOut) mj) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hT : Tset tr D L0 (Qj 0) = L0 := by
        apply List.ext_getElem?; intro i
        exact Tset_neg hL0 (fun r0 ⟨r, _, h⟩ _ => by omega)
      refine ⟨fun r0 r _ h => by omega, m0, by rw [hT]; exact hr0, fun r hr ht h0 => ?_, fun h0 => ?_⟩
      · rw [(rch_chain H).1 r hr ht h0]; exact hm0
      · rw [((rch_chain H).2.2.2 h0.symm).1]; exact hm0
    | succ j ih =>
      intro hj
      obtain ⟨IA, mj, hrt, hcan, -⟩ := ih (by omega)
      obtain ⟨r, hr, ht, hrj⟩ := top_exists tr (tr.height 20) j (by omega)
      obtain ⟨r0, hB⟩ := mp_block_of_top H hr ht
      obtain ⟨hnD, hL, hco, hri, hrtN, hrtR, -, -, -, hro01⟩ := BB hB
      have hβ : natOf D (mpBits tr r0) < 2 ^ D := natOf_lt _ _
      have e1 : mj = pathRoot StateM5a.StateView.nodeH (bytesOf (mdig tr r0 12)) (bpath (mpL tr r0 D)) := by
        rw [← (hcan r hr ht hrj).bytes, hri.bytes]
      obtain ⟨hget, hset⟩ := write_access_pd StateM5a.StateView.nodeH D48 nodeH_d48 (nodeH_inj hn) D
        (Tset tr D L0 (Qj j)) (natOf D (mpBits tr r0)) (bytesOf (mdig tr r0 12)) (bpath (mpL tr r0 D))
        (T48 j) (old48 r0 r hB) (bpath_d48 hL) (Tset_length _ _ _ _) hβ
        (by rw [bpath_length]; simp [mpL]) (by rw [bpath_mpL]; exact sidesOk_natOf _ _ _) (by rw [hrt, e1])
      -- the only block with `topCount = j` is `r0`'s
      have only : ∀ r0' r', MpBlock tr r0' r' → topCount tr r' = j → r0' = r0 := by
        intro r0' r' hB' hj'
        have := top_unique H hB'.2.1 hr hB'.2.2.2.2.1 ht (by omega)
        subst this
        exact mp_block_unique H hB' hB
      have hT : Tset tr D L0 (Qj (j + 1)) =
          (Tset tr D L0 (Qj j)).set (natOf D (mpBits tr r0)) (bytesOf (mdig tr r0 30)) := by
        apply List.ext_getElem?; intro k
        rw [List.getElem?_set]
        by_cases hk : natOf D (mpBits tr r0) = k
        · subst hk
          rw [if_pos rfl, if_pos (by rw [Tset_length]; exact hβ)]
          exact Tset_pos hβ ⟨r, hB, by omega⟩ rfl (hcQ (j + 1) _ r0 ⟨r, hB⟩ · · · rfl)
        · rw [if_neg hk]
          by_cases hex : ∃ r0', Qj j r0' ∧ natOf D (mpBits tr r0') = k
          · obtain ⟨r0', hq, hb⟩ := hex
            have hk' : k < 2 ^ D := by rw [← hb]; exact natOf_lt _ _
            have hBr : ∃ r, MpBlock tr r0' r := hq.elim fun r' h => ⟨r', h.1⟩
            rw [Tset_pos hk' hq hb (hcQ j k r0' hBr · · · hb),
              Tset_pos hk' (show Qj (j + 1) r0' from hq.elim fun r' h => ⟨r', h.1, by omega⟩) hb
                (hcQ (j + 1) k r0' hBr · · · hb)]
          · rw [Tset_neg hL0 (fun r0' hq hb => hex ⟨r0', hq, hb⟩), Tset_neg hL0 ?_]
            intro r0' ⟨r', hB', hlt⟩ hb
            by_cases e : topCount tr r' = j
            · rw [only r0' r' hB' e] at hb; exact hk hb
            · exact hex ⟨r0', ⟨r', hB', by omega⟩, hb⟩
      have hnew : Canon (mdig tr r 132)
          (pathRoot StateM5a.StateView.nodeH (bytesOf (mdig tr r0 30)) (bpath (mpL tr r0 D))) := by
        rcases hro01 with h | h
        · exact (hrtN h).2
        · rw [hrtR h, hro r0 r hB h]; exact hri
      refine ⟨fun r0' r' hB' hlt => ?_, _, by rw [hT]; exact hset _, fun r'' hr'' ht'' hj'' => ?_, fun hnb => ?_⟩
      · by_cases e : topCount tr r' = j
        · have := only r0' r' hB' e; subst this
          by_cases hex : ∃ r0'', Qj j r0'' ∧ natOf D (mpBits tr r0'') = natOf D (mpBits tr r0')
          · obtain ⟨r0'', ⟨r''', hB'', hlt''⟩, hb⟩ := hex
            rw [← hb, IA r0'' r''' hB'' hlt'', (hcons r0'' r''' r0' r' hB'' hB' hb).1]
          · rw [← Tset_neg hL0 (fun r0'' hq hb => hex ⟨r0'', hq, hb⟩)]; exact hget
        · exact IA r0' r' hB' (by omega)
      · rw [(rch_chain H).2.1 r r'' hr hr'' ht ht'' (by omega)]; exact hnew
      · rw [((rch_chain H).2.2.1 r hr ht (by omega)).1]; exact hnew
  obtain ⟨IA, mf, hrt, -, hout⟩ := inv nb (Nat.le_refl _)
  have hQ : Qj nb = fun r0 => ∃ r, MpBlock tr r0 r := by
    funext r0
    apply propext
    exact ⟨fun ⟨r, h, _⟩ => ⟨r, h⟩, fun ⟨r, h⟩ => ⟨r, h, top_lt tr h.2.1 h.2.2.2.2.1⟩⟩
  refine ⟨fun r0 r hB => IA r0 r hB (top_lt tr hB.2.1 hB.2.2.2.2.1), mf, hout rfl, ?_⟩
  rw [← hQ]; exact hrt

end chain

/-! ## 3. Leaves and blocks of the spec memory -/

theorem memLeaves_get (s : St) (i : Nat) :
    (WasmView.memLeaves s)[i]? = if i < WasmView.nblkOf s then some (sha384 (WasmView.blkBytes s i))
      else if i < 2 ^ WasmView.memDepth s then some WasmView.zleaf else none := by
  have := WasmView.nblk_le s
  unfold WasmView.memLeaves
  by_cases h : i < WasmView.nblkOf s
  · rw [if_pos h, List.getElem?_append_left (by simpa using h)]
    simp [List.getElem?_map, List.getElem?_range h]
  · rw [if_neg h, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
    simp only [List.length_map, List.length_range]
    by_cases h2 : i < 2 ^ WasmView.memDepth s
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

theorem blkBytes_get (s : St) (b : Nat) {j : Nat} (hj : j < 1024) :
    (WasmView.blkBytes s b)[j]? = some (readByte s (1024 * b + j)) := by
  simp [WasmView.blkBytes, List.getElem?_map, List.getElem?_range hj]

theorem membBytes_get (tr : Trace) (b : Nat) (pre : String) {j : Nat} (hj : j < 1024) :
    (SegSha.membBytes tr b pre)[j]? =
      some (UInt8.ofNat (mbN tr (9 * b + j / 128) (ix Memb.cols s!"{pre}{j % 128}"))) := by
  simp [SegSha.membBytes, List.getElem?_map, List.getElem?_range hj]

theorem memDepth_le (s : St) (h : WasmView.nblkOf s ≤ 2 ^ 17) : WasmView.memDepth s ≤ 17 := by
  unfold WasmView.memDepth
  have hm : max (WasmView.nblkOf s) 2 - 1 ≠ 0 := by omega
  have hle : max (WasmView.nblkOf s) 2 ≤ 2 ^ 17 := by
    rcases Nat.le_total (WasmView.nblkOf s) 2 with h' | h'
    · rw [Nat.max_eq_right h']; decide
    · rw [Nat.max_eq_left h']; exact h
  have := (Nat.log2_lt hm (k := 17)).2 (by omega)
  omega

theorem memDepth_pos (s : St) : 1 ≤ WasmView.memDepth s := by unfold WasmView.memDepth; omega

section link
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- An active MEMB block is an MPATH block with the same leaf message. -/
theorem memb_mp {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1) :
    ∃ r0 r, MpBlock tr r0 r ∧ mc tr r0 5 = bc tr (9 * b + 8) 10 ∧ mc tr r0 4 = bc tr (9 * b + 8) 11 ∧
      mdig tr r0 12 = bdig tr (9 * b + 8) 486 ∧ mdig tr r0 30 = bdig tr (9 * b + 8) 534 := by
  obtain ⟨r0, hr0, ha, hb, he⟩ := memb_leaf_send H hr8 ha8
  obtain ⟨r, hB⟩ := mp_block_of_bot H hr0 ha hb
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
  obtain ⟨a, b', c⟩ := he
  obtain ⟨c1, c2⟩ := List.append_inj c (by simp [bdig, mdig])
  exact ⟨r0, r, hB, a, b', c1, c2⟩

/-- The depth of a memory with a touched block is at most 17 (`nblk ≤ blk + 2^16`, `blk < 2^16`). -/
theorem depth_le_of_block {s0 : St} (hG : MemGeom pub s0) {b : Nat} (hr8 : 9 * b + 8 < tr.height 19)
    (ha8 : mbN tr (9 * b + 8) 0 = 1) : WasmView.memDepth s0 ≤ 17 := by
  obtain ⟨l1, -, l3⟩ := memb_blk_lt H hr8 ha8
  exact memDepth_le s0 (by rw [← hG.2]; omega)

/-- An MPATH block's index is its MEMB block's `blk`. -/
theorem natOf_blk {r0 r b D : Nat} {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hB : MpBlock tr r0 r)
    (hD : (pub.getD pubDepth 0).toNat = D) (hD1 : 1 ≤ D) (hD17 : D ≤ 17)
    (he : mc tr r0 5 = bc tr (9 * b + 8) 10) : natOf D (mpBits tr r0) = mbN tr (9 * b + 8) 10 := by
  have hP := P_val
  have e := (mp_block_bytes H hC hB hD hD1).2.2.2.2.2.2.1
  rw [e, show bc tr (9 * b + 8) 10 = ((mbN tr (9 * b + 8) 10 : Nat) : F) from cell_cast tr 19 _ 10] at he
  have := natOf_lt D (mpBits tr r0)
  have h2 : 2 ^ D ≤ 2 ^ 17 := Nat.pow_le_pow_right (by decide) hD17
  exact natEq he (by omega) (rowNat_lt _ _ _ _)

/-- Same index ⇒ same MEMB block ⇒ same leaves; read-only ⇒ new leaf = old leaf. -/
theorem mp_cons_ro {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {D : Nat} (hD : (pub.getD pubDepth 0).toNat = D) (hD1 : 1 ≤ D) :
    (∀ r0 r r0' r', MpBlock tr r0 r → MpBlock tr r0' r' → natOf D (mpBits tr r0) = natOf D (mpBits tr r0') →
      bytesOf (mdig tr r0 12) = bytesOf (mdig tr r0' 12) ∧ bytesOf (mdig tr r0 30) = bytesOf (mdig tr r0' 30)) ∧
    (∀ r0 r, MpBlock tr r0 r → mc tr r0 4 = 1 → bytesOf (mdig tr r0 30) = bytesOf (mdig tr r0 12)) := by
  have hP := P_val
  have lk : ∀ r0 r, MpBlock tr r0 r → ∃ b, 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 ∧
      mc tr r0 5 = bc tr (9 * b + 8) 10 ∧ mc tr r0 4 = bc tr (9 * b + 8) 11 ∧
      mdig tr r0 12 = bdig tr (9 * b + 8) 486 ∧ mdig tr r0 30 = bdig tr (9 * b + 8) 534 :=
    fun r0 r hB => mp_leaf H (by have := hB.1; have := hB.2.1; omega) hB.2.2.2.1
  refine ⟨fun r0 r r0' r' hB hB' hn => ?_, fun r0 r hB h1 => ?_⟩
  · obtain ⟨b, hr8, ha8, e5, -, e12, e30⟩ := lk r0 r hB
    obtain ⟨b', hr8', ha8', e5', -, e12', e30'⟩ := lk r0' r' hB'
    have m5 := (mp_block_bytes H hC hB hD hD1).2.2.2.2.2.2.1
    have m5' := (mp_block_bytes H hC hB' hD hD1).2.2.2.2.2.2.1
    have hbb : b = b' := by
      refine Classical.byContradiction fun hne => memb_blk_distinct_of_holds H hne hr8 hr8' ha8 ha8' ?_
      have h := e5.symm.trans (m5.trans ((congrArg (fun n : Nat => (n : F)) hn).trans (m5'.symm.trans e5')))
      rw [show bc tr (9 * b + 8) 10 = ((mbN tr (9 * b + 8) 10 : Nat) : F) from cell_cast tr 19 _ 10,
        show bc tr (9 * b' + 8) 10 = ((mbN tr (9 * b' + 8) 10 : Nat) : F) from cell_cast tr 19 _ 10] at h
      exact natEq h (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)
    subst hbb
    rw [e12, e30, e12', e30']; exact ⟨rfl, rfl⟩
  · obtain ⟨b, hr8, ha8, -, e4, e12, e30⟩ := lk r0 r hB
    rw [e12, e30, memb_ro_leaf H hr8 ha8 (by rw [← e4, h1])]

end link

/-! ## 4. The in-side: MEMB's bytes are the in-state's -/

theorem root_memLeaves (s : St) :
    root StateM5a.StateView.nodeH (WasmView.memDepth s) (WasmView.memLeaves s) = some (WasmView.memRootOf s) := by
  obtain ⟨x, hx⟩ := StateM5a.StateView.root_some _ _ (WasmView.memLeaves_length s)
  rw [hx]; simp [WasmView.memRootOf, hx]

theorem uint8_toNat_ofNat {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by simp; omega

section inside
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- The root chain started at the in-state's tree. -/
theorem chain_s0 {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0) (hn : ¬ Sha384Coll) :
    (∀ r0 r, MpBlock tr r0 r → (WasmView.memLeaves s0)[natOf (WasmView.memDepth s0) (mpBits tr r0)]? =
      some (bytesOf (mdig tr r0 12))) ∧
    ∃ mf, Canon (pubDig pub pubMemOut) mf ∧
      root StateM5a.StateView.nodeH (WasmView.memDepth s0)
        (Tset tr (WasmView.memDepth s0) (WasmView.memLeaves s0) fun r0 => ∃ r, MpBlock tr r0 r) = some mf :=
  have hc := mp_cons_ro H hC hG.1 (memDepth_pos s0)
  mp_chain H hC hG.1 (memDepth_pos s0) hn (WasmView.memLeaves_length s0) (WasmView.memLeaves_mem s0)
    (root_memLeaves s0) hR hc.1 hc.2

/-- The bytes of a touched block `b`: the leaf `hoI` is SHA-384 of MEMB's `bi` bytes. -/
theorem leaf_in_bytes {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1) :
    bytesOf (bdig tr (9 * b + 8) 486) = sha384 (SegSha.membBytes tr b "bi") := by
  obtain ⟨-, d, hl, hw, e, eb⟩ := SegSha.memb_leaf_in H hC hr8 ha8
  exact (show Canon (bdig tr (9 * b + 8) 486) _ from ⟨d, hl, hw, e, eb⟩).bytes

/-- **Item 1: the in-root binds MEMB's in-side bytes.**  With the public geometry the in-state's
(`MemGeom`) and the public in-root its memory root (`MemRootIn`), every byte MEMB produces is the
in-state's byte at an in-bounds address (`MembIn`), or SHA-384 has a collision.  Each touched block's
leaf and MPATH path recompute the in-root; walking the root chain (`mp_chain`), the first update of
an index sees the in-state's leaf there (Merkle path binding, `write_access_pd`). -/
theorem seg_membIn {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0) : MembIn tr pub s0 ∨ Sha384Coll := by
  by_cases hn : Sha384Coll
  · exact .inr hn
  refine .inl fun x hx => ?_
  obtain ⟨b, k, i, hk, hi, hr8, ha8, rfl⟩ := memb_prod_form H hx
  have hD17 := depth_le_of_block H hG hr8 ha8
  obtain ⟨r0, r, hB, e5, -, e12, -⟩ := memb_mp H hr8 ha8
  have hblk := natOf_blk H hC hB hG.1 (memDepth_pos s0) hD17 e5
  have hlt := (memb_blk_lt H hr8 ha8).2.1
  rw [hG.2] at hlt
  have A := (chain_s0 H hC hG hR hn).1 r0 r hB
  rw [hblk, memLeaves_get, if_pos hlt, e12, leaf_in_bytes H hC hr8 ha8] at A
  have hEq := sha384_inj hn (Option.some.inj A)
  have hj : 128 * k + i < 1024 := by omega
  have B := congrArg (·[128 * k + i]?) hEq

  rw [blkBytes_get _ _ hj, membBytes_get _ _ _ hj, show (128 * k + i) / 128 = k by omega,
    show (128 * k + i) % 128 = i by omega, mb_ix_bi i hi] at B
  have hrk : 9 * b + k < tr.height 19 := by omega
  have hak : mbN tr (9 * b + k) 0 = 1 := (memb_pos H _ hr8 ha8).1 _ (by omega)
  have hbi := memb_bi_lt' H hrk hak (by omega) hi
  have hrd : (readByte s0 (1024 * mbN tr (9 * b + 8) 10 + (128 * k + i))).toNat = mbN tr (9 * b + k) (14 + i) := by
    rw [Option.some.inj B]; exact uint8_toNat_ofNat hbi
  rw [← Nat.add_assoc] at hrd
  refine ⟨?_, ?_⟩
  · show 1024 * mbN tr (9 * b + 8) 10 + 128 * k + i < memBytes s0
    simp only [memBytes, pageSize, WasmView.nblkOf] at hlt ⊢
    omega
  · simp only [encB, hrd]

end inside

/-! ## 5. The out-side: the out-root is the out-state's memory root -/

theorem membBytes_length (tr : Trace) (b : Nat) (pre : String) : (SegSha.membBytes tr b pre).length = 1024 := by
  simp [SegSha.membBytes]

theorem blkBytes_length (s : St) (b : Nat) : (WasmView.blkBytes s b).length = 1024 := by
  simp [WasmView.blkBytes]

theorem nblk_depth_eq {s s' : St} (h : s'.pages.size = s.pages.size) :
    WasmView.nblkOf s' = WasmView.nblkOf s ∧ WasmView.memDepth s' = WasmView.memDepth s := by
  simp [WasmView.nblkOf, WasmView.memDepth, h]

section outside
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- A read-only block's out bytes are its in bytes (`ro·(bo − bi) = 0`). -/
theorem memb_ro_bytes {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hro : mbN tr (9 * b + 8) 11 = 1) : SegSha.membBytes tr b "bo" = SegSha.membBytes tr b "bi" := by
  unfold SegSha.membBytes
  apply List.map_congr_left; intro j hj
  have hj' := List.mem_range.mp hj
  have hk : j / 128 < 8 := by omega
  have hi : j % 128 < 128 := Nat.mod_lt _ (by decide)
  have hr : 9 * b + j / 128 < tr.height 19 := by omega
  have ro1 : mbN tr (9 * b + j / 128) 11 = 1 := (SegSha.memb_ro_const H hr8 ha8 (j / 128) (by omega)).trans hro
  have hmem : Memb.c "ro" * (Memb.c s!"bo{j % 128}" - Memb.c s!"bi{j % 128}") ∈ Memb.constraints := by
    unfold Memb.constraints
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ ?_)))))
    exact List.mem_map.mpr ⟨j % 128, List.mem_range.mpr hi, rfl⟩
  have h := memb_C H hr _ hmem
  simp only [Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.2.2, ro1, cast_one] at h
  have h' : ((mbN tr (9 * b + j / 128) (ix Memb.cols s!"bo{j % 128}") : Nat) : F) =
      ((mbN tr (9 * b + j / 128) (ix Memb.cols s!"bi{j % 128}") : Nat) : F) := by grind
  rw [natEq h' (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)]

/-- **Item 3: the out-root is the out-state's memory root.**  From the in-side facts (`MemGeom`,
`MemRootIn` at `s0`), the memory frame of the segment (`hpg`: same page count; `hfr`: every address
without a MEMB production keeps its byte — `seg_mem_frame`), and the out-boundary's memory part
(`hout`: MEMB's consumed bytes are `sN`'s bytes — from `BndC` at the out cut, `membOut_of_bnd`):
the public out-root is `memRootOf sN` and the geometry is `sN`'s, or SHA-384 has a collision.  The
new root uses the same siblings with the new leaves (`mp_chain`); untouched blocks are unchanged.
This covers the no-touched-block case (`memOut = memIn`). -/
theorem seg_memRootOut {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {s0 sN : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0) (hpg : sN.pages.size = s0.pages.size)
    (hfr : ∀ a, (∀ x ∈ (part Memb.table tr pub 19 busStk true).map decMsg, x.slot ≠ a) →
      readByte sN a = readByte s0 a)
    (hout : ∀ a v tp, (⟨3, a, 0, v, 0, 0, 0, tp⟩ : Msg) ∈ (part Memb.table tr pub 19 busStk false).map decMsg →
      (readByte sN a).toNat = v) :
    (MemRootOut pub sN ∧ MemGeom pub sN) ∨ Sha384Coll := by
  by_cases hn : Sha384Coll
  · exact .inr hn
  obtain ⟨hnb, hdp⟩ := nblk_depth_eq hpg
  have hGN : MemGeom pub sN := ⟨by rw [hdp]; exact hG.1, by rw [hnb]; exact hG.2⟩
  obtain ⟨-, mf, hcan, hrt⟩ := chain_s0 H hC hG hR hn
  have hc := mp_cons_ro H hC hG.1 (memDepth_pos s0)
  have cc : ∀ r i, bc tr r i = ((mbN tr r i : Nat) : F) := fun r i => cell_cast tr 19 r i
  have hT : Tset tr (WasmView.memDepth s0) (WasmView.memLeaves s0) (fun r0 => ∃ r, MpBlock tr r0 r) =
      WasmView.memLeaves sN := by
    apply List.ext_getElem?; intro i
    rw [memLeaves_get sN i, hnb, hdp]
    by_cases ht : ∃ r0, (∃ r, MpBlock tr r0 r) ∧ natOf (WasmView.memDepth s0) (mpBits tr r0) = i
    · obtain ⟨r0, ⟨r, hB⟩, hb⟩ := ht
      have hi : i < 2 ^ WasmView.memDepth s0 := by rw [← hb]; exact natOf_lt _ _
      rw [Tset_pos hi ⟨r, hB⟩ hb (fun r0' ⟨r', hB'⟩ hb' => (hc.1 r0' r' r0 r hB' hB (hb'.trans hb.symm)).2)]
      obtain ⟨b, hr8, ha8, e5, e4, -, e30⟩ := mp_leaf H (by have := hB.1; have := hB.2.1; omega) hB.2.2.2.1
      have hD17 := depth_le_of_block H hG hr8 ha8
      rw [natOf_blk H hC hB hG.1 (memDepth_pos s0) hD17 e5] at hb
      subst hb
      have hlt := (memb_blk_lt H hr8 ha8).2.1
      rw [hG.2] at hlt
      rw [if_pos hlt, e30]
      -- the out bytes of the block are `sN`'s
      have hbo : ∀ q, q < 8 → ∀ i', i' < 128 →
          mbN tr (9 * b + q) (142 + i') = (readByte sN (1024 * mbN tr (9 * b + 8) 10 + 128 * q + i')).toNat := by
        intro q hq i' hi'
        obtain ⟨tp, hm⟩ := memb_cons_mem H hr8 ha8 hq hi'
        exact (hout _ _ _ hm).symm
      have hbytes : SegSha.membBytes tr b "bo" = WasmView.blkBytes sN (mbN tr (9 * b + 8) 10) := by
        apply List.ext_getElem?; intro j
        by_cases hj : j < 1024
        · rw [membBytes_get _ _ _ hj, blkBytes_get _ _ hj, SegSha.mb_ix_bo _ (Nat.mod_lt _ (by decide)),
            hbo (j / 128) (by omega) (j % 128) (Nat.mod_lt _ (by decide)), UInt8.ofNat_toNat]
          congr 2; omega
        · rw [List.getElem?_eq_none (by rw [membBytes_length]; omega),
            List.getElem?_eq_none (by rw [blkBytes_length]; omega)]
      congr 1
      rw [← hbytes]
      have hro01 := (mp_block_bytes H hC hB hG.1 (memDepth_pos s0)).2.2.2.2.2.2.2.2.2
      rcases hro01 with h0 | h1
      · rw [h0, cc] at e4
        have hro : mbN tr (9 * b + 8) 11 = 0 := natEq (R := 0) e4.symm (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
        obtain ⟨d, hl, hw, e, eb⟩ := SegSha.memb_leaf_out H hC hr8 ha8 hro (fun q hq i' hi' => by
          rw [hbo q hq i' hi']; exact UInt8.toNat_lt _)
        exact (show Canon (bdig tr (9 * b + 8) 534) _ from ⟨d, hl, hw, e, eb⟩).bytes
      · have e4' := e4; rw [h1] at e4'
        rw [memb_ro_leaf H hr8 ha8 e4'.symm, leaf_in_bytes H hC hr8 ha8]
        rw [cc] at e4'
        have hro : mbN tr (9 * b + 8) 11 = 1 := natEq (R := 1) e4'.symm (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
        rw [memb_ro_bytes H hr8 ha8 hro]
    · rw [Tset_neg (WasmView.memLeaves_length s0) (fun r0 hq hb => ht ⟨r0, hq, hb⟩), memLeaves_get s0 i]
      by_cases hlt : i < WasmView.nblkOf s0
      · rw [if_pos hlt, if_pos hlt]
        congr 2
        apply List.ext_getElem?; intro j
        by_cases hj : j < 1024
        · rw [blkBytes_get _ _ hj, blkBytes_get _ _ hj]
          congr 1
          refine (hfr _ fun x hx he => ?_).symm
          obtain ⟨b, k, i', hk, hi', hr8, ha8, rfl⟩ := memb_prod_form H hx
          obtain ⟨r0, r, hB, e5, -⟩ := memb_mp H hr8 ha8
          have hD17 := depth_le_of_block H hG hr8 ha8
          have hblk := natOf_blk H hC hB hG.1 (memDepth_pos s0) hD17 e5
          simp only at he
          exact ht ⟨r0, ⟨r, hB⟩, by rw [hblk]; omega⟩
        · rw [List.getElem?_eq_none (by rw [blkBytes_length]; omega),
            List.getElem?_eq_none (by rw [blkBytes_length]; omega)]
      · rw [if_neg hlt, if_neg hlt]
  have hroot := root_memLeaves sN
  rw [← hT, hdp, hrt] at hroot
  exact .inl ⟨by rw [MemRootOut, ← Option.some.inj hroot]; exact hcan, hGN⟩

end outside

/-! ## 6. Packaged: the memory-root conjunct of a cut segment -/

/-- CUTI produces no memory (space-3) message (named premise: CUTI's rows are the previous
segment's `cutView`, which has no space-3 entry). -/
def CutiNoMem (tr : Trace) (pub : List F) : Prop :=
  ∀ x ∈ (part Cut.In.table tr pub 30 busStk true).map decMsg, x.space ≠ 3

/-- An address without a MEMB production has no space-3 message in `initS` (SEGB's is space 7). -/
theorem initS_free {tr : Trace} {pub : List F} (hcu : CutiNoMem tr pub) {a : Nat}
    (hm : ∀ x ∈ (part Memb.table tr pub 19 busStk true).map decMsg, x.slot ≠ a) :
    ∀ x ∈ initS tr pub, x.space = 3 → x.slot ≠ a := by
  intro x hx h3
  simp only [initS, List.mem_append] at hx
  rcases hx with hx | hx | hx
  · exact absurd h3 (hcu x hx)
  · exact hm x hx
  · obtain ⟨r, -, m, hm', rfl⟩ := mem_part_dec.mp hx
    have := rowMsgs_space segb_send_space (by rw [P_val]; decide) hm'
    rw [this] at h3; exact absurd h3 (by decide)

/-- **The out-boundary's memory part**: MEMB's consumed bytes are bytes of the out-state. -/
theorem membOut_of_bnd {X : Ctx} {sg : Nat → Nat × Nat} {sN : St} {t S : Nat} {m : List F}
    {tr : Trace} {pub : List F} (h : Bnd X sg sN t S m (finS tr pub)) :
    ∀ a v tp, (⟨3, a, 0, v, 0, 0, 0, tp⟩ : Msg) ∈ (part Memb.table tr pub 19 busStk false).map decMsg →
      (readByte sN a).toNat = v := by
  intro a v tp hx
  obtain ⟨k, pc, sb, cid, -, E, f, tps, tpl, -, -, -, R⟩ := h
  have hl : (⟨3, a, 0, v, 0, 0, 0, tp⟩ : Msg) ∈ finS tr pub :=
    List.mem_append_right _ (List.mem_append_left _ hx)
  have hE := R.env_msg (x := encB a v tp) hl (by simp) (by simp [Env.lsp]; omega)
  exact (heap_read R.heap hE).1

/-- **`seg_mem_sound`: the memory-root conjunct of a cut segment.**  Under `seg_sound`'s execution
premises, the chip contract, `HostPagesRely` (M6), `CutiNoMem`, the in-boundary relation and the
public geometry/in-root of `s0`: MEMB's in-side bytes are `s0`'s (`MembIn`, item 1 — no execution
needed, so it can feed the memory part of `h0`), and for the out-state `sN` of the segment related
to the out-boundary, the public out-root is `sN`'s memory root and the geometry is `sN`'s — or
SHA-384 has a collision. -/
theorem seg_mem_sound (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hpr : HostPagesRely X.toCtx tr pub) (hcu : CutiNoMem tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0)
    (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub) (initS tr pub)) :
    (MembIn tr pub s0 ∨ Sha384Coll) ∧
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      ∀ {tN SN : Nat} {mN : List F}, Bnd X.toCtx sg sN tN SN mN (finS tr pub) →
      (MemRootOut pub sN ∧ MemGeom pub sN) ∨ Sha384Coll := by
  refine ⟨seg_membIn H hC hG hR, fun sN hseg tN SN mN hN => ?_⟩
  obtain ⟨hpg, hfr⟩ := seg_mem_frame X H hcode hfunc hb hg hkeep hhold hpr hst0 hlen htin hfeeN hstepgas hg64
    hinit h0 sN hseg
  exact seg_memRootOut H hC hG hR hpg (fun a ha => hfr a (initS_free hcu ha)) (membOut_of_bnd hN)

end MemRoot

#print axioms MemRoot.mp_chain
#print axioms MemRoot.seg_membIn
#print axioms MemRoot.seg_memRootOut
#print axioms MemRoot.seg_mem_sound

end WasmBase
