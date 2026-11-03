import WasmBase.Main.SegMembS
import WasmBase.Main.SegMemRoot

/-!
# WasmBase.Main.SegMemMembS — MEMB-side lemmas of `SegMemRoot` from `HoldsXS` (E2E M4c, MEM)

Copies of `Main/SegMemRoot.lean`'s MEMB-only row lemmas (`memb_prod_form`, `memb_cons_mem`,
`memb_blk_lt`, `memb_ro_leaf`, `memb_ro_bytes`, `leaf_in_bytes`, …) with `HoldsX (wasmBaseSegAir …)`
replaced by `HoldsXS` and `ChipIf` by `ChipIfS` (`foo` ↦ `fooS`), so that they serve the multiproof
AIR (`HoldsX.toSMP`).  MEMB uses neither table 20 nor the buses 15/16/17.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
open NearSpecV3.Wasm hiding P
open NearSpecV3.E2E.Bnd (Sha384Coll sha384 sha384_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace MemRoot

section membS
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

theorem memb_act_of_pS {r i : Nat} (hr : r < tr.height 19) (hi : i < 9) (hp : mbN tr r (1 + i) = 1) :
    mbN tr r 0 = 1 := by
  obtain ⟨ha, -, hs⟩ := memb_rowS H hr
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.reduceAdd] at hp) <;> omega

/-- A row with `p8 = 1` is an active padding row `9b + 8`. -/
theorem memb_pad_of_p8S {r : Nat} (hr : r < tr.height 19) (hp : mbN tr r 9 = 1) :
    mbN tr r 0 = 1 ∧ r % 9 = 8 := by
  have ha := memb_act_of_pS H hr (i := 8) (by decide) hp
  refine ⟨ha, Classical.byContradiction fun hne => ?_⟩
  have := memb_onehotS H hr (k := r % 9) (j := 8) (Nat.mod_lt _ (by decide)) (by decide) hne (memb_posS H r hr ha).2
  rw [show 1 + 8 = 9 from rfl, hp] at this
  exact absurd this (by decide)

/-- An active data row is followed by an active row. -/
theorem memb_fwdS {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hk : r % 9 < 8) :
    r + 1 < tr.height 19 ∧ mbN tr (r + 1) 0 = 1 := by
  have hp := (memb_posS H r hr ha).2
  have hm : r % 9 < 9 := by omega
  by_cases hl : r + 1 = tr.height 19
  · exfalso
    have l1 : Expr.last.eval (tr.row pub 19 r) = 1 := by simp [Expr.eval, Trace.row, hl]
    have h := memb_CS H hr (Expr.last * Memb.c "act" * (1 - Memb.p 8)) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_p_eval tr pub r (show 8 < 9 by decide), ha, l1, cast_one] at h
    have h8 : mbN tr r (1 + 8) = 1 :=
      natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    have := memb_onehotS H hr (k := r % 9) (j := 8) hm (by decide) (by omega) hp
    rw [h8] at this; exact absurd this (by decide)
  · have hr1 : r + 1 < tr.height 19 := by omega
    have hmem : Expr.trans * Memb.p (r % 9) * (1 - nv (ix Memb.cols s!"p{r % 9 + 1}")) ∈ Memb.constraints := by
      unfold Memb.constraints
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))))))
      exact List.mem_map.mpr ⟨r % 9, List.mem_range.mpr hk, rfl⟩
    have h := memb_CS H hr _ hmem
    rw [mb_ix_p (r % 9 + 1) (by omega)] at h
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r hm, nv,
      Expr.eval_nxt, trans_eval_one tr pub 19 r hr1, hp, cast_one] at h
    simp only [Trace.row, Nat.mod_eq_of_lt hr1, cell_cast] at h
    have hn : mbN tr (r + 1) (1 + (r % 9 + 1)) = 1 :=
      natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    exact ⟨hr1, memb_act_of_pS H hr1 (i := r % 9 + 1) (by omega) hn⟩

/-- An active data row's block has an active padding row. -/
theorem memb_pad_of_dataS {b k : Nat} (hr : 9 * b + k < tr.height 19) (ha : mbN tr (9 * b + k) 0 = 1)
    (hk : k < 8) : 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 := by
  have key : ∀ d k, k + d = 8 → 9 * b + k < tr.height 19 → mbN tr (9 * b + k) 0 = 1 →
      9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 := by
    intro d
    induction d with
    | zero => intro k hk hr ha; rw [show k = 8 by omega] at hr ha; exact ⟨hr, ha⟩
    | succ d ih =>
      intro k hk hr ha
      obtain ⟨h1, h2⟩ := memb_fwdS H hr ha (by omega)
      exact ih (k + 1) (by omega) (by omega) (by rw [show 9 * b + (k + 1) = 9 * b + k + 1 by omega]; exact h2)
  exact key (8 - k) k (by omega) hr ha

/-- The two byte interactions of an active data row, evaluated. -/
theorem memb_msg_evalS {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hk : r % 9 < 8)
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
  have hp := (memb_posS H r hr ha).2
  obtain ⟨k, hkdef⟩ : ∃ k, k = r % 9 := ⟨_, rfl⟩
  rw [← hkdef] at hp hk ⊢
  have oh : ∀ j, j < 9 → mbN tr r (1 + j) = if j = k then 1 else 0 := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk; simpa using hp
    · rw [if_neg hjk]; exact memb_onehotS H hr (k := k) (by omega) hj (Ne.symm hjk) hp
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

theorem memb_kD_inactS {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 ≠ 1) :
    (Memb.kD.eval (tr.row pub 19 r)).toNat ≠ 1 := by
  obtain ⟨h1, -, hs⟩ := memb_rowS H hr
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
theorem memb_blk_ltS {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 < 65536 ∧ mbN tr (9 * b + 8) 10 < (pub.getD pubNblk 0).toNat ∧
      (pub.getD pubNblk 0).toNat ≤ mbN tr (9 * b + 8) 10 + 65536 := by
  have hP := P_val
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_posS H _ hr ha).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have hc : ((Memb.p 8).eval (tr.row pub 19 (9 * b + 8))).toNat = 1 := by
    rw [memb_p_eval tr pub _ (by decide), hp8]; rfl
  have m1 : r16 (Memb.c "blk") (Memb.p 8) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]; show _ ∈ Memb.inters; unfold Memb.inters
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m2 : r16 (pv pubNblk - 1 - Memb.c "blk") (Memb.p 8) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]; show _ ∈ Memb.inters; unfold Memb.inters
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  have l1 := seg_r16_ltS H (seg_hsend_r16S H) ht hr m1 hc
  have l2 := seg_r16_ltS H (seg_hsend_r16S H) ht hr m2 hc
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

theorem memb_bi_lt'S {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) {i : Nat}
    (hi : i < 128) : mbN tr r (14 + i) < 256 := by
  have := SegSha.memb_bi_ltS H hr ha hq i hi
  rwa [mb_ix_bi i hi] at this

/-- **MEMB's in-side productions.**  Every message MEMB produces is byte `bi_i` of a data row
`9b + k` of an active block, at address `1024·blk + 128·k + i`, time `t_in`. -/
theorem memb_prod_formS {x : Msg} (hx : x ∈ (part Memb.table tr pub 19 busStk true).map decMsg) :
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
    have ha : mbN tr r 0 = 1 := Classical.byContradiction fun h => memb_kD_inactS H hr h hc
    have hk : r % 9 < 8 := by
      refine Classical.byContradiction fun h => ?_
      have := ((SegSha.memb_kDkPS H hr ha).2 (by omega)).1
      rw [this] at hc; exact absurd hc (by decide)
    obtain ⟨-, e1, -⟩ := memb_msg_evalS H hr ha hk hi'
    obtain ⟨hr8, ha8⟩ := memb_pad_of_dataS H (b := r / 9) (k := r % 9) (by rw [Nat.div_add_mod]; exact hr)
      (by rw [Nat.div_add_mod]; exact ha) hk
    have hbc := memb_blk_constS H hr8 ha8 (r % 9) (by omega)
    rw [Nat.div_add_mod] at hbc
    have hbl := (memb_blk_ltS H hr8 ha8).1
    have hbi := memb_bi_lt'S H hr ha hk hi'
    refine ⟨r / 9, r % 9, i, hk, hi', hr8, ha8, ?_⟩
    simp only [Nat.div_add_mod]
    rw [e1, ← hbc]
    simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ]
    rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
      Fp.toNat_cast_of_lt (by omega)]
  · cases he

/-- **MEMB's out-side consumptions.**  For every data row `9b + k` of an active block and every
`i < 128`, MEMB consumes `bo_i` at address `1024·blk + 128·k + i` (some producer time). -/
theorem memb_cons_memS {b k i : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hk : k < 8) (hi : i < 128) :
    ∃ tp, (⟨3, 1024 * mbN tr (9 * b + 8) 10 + 128 * k + i, 0, mbN tr (9 * b + k) (142 + i), 0, 0, 0, tp⟩ : Msg) ∈
      (part Memb.table tr pub 19 busStk false).map decMsg := by
  have hP := P_val
  have hr : 9 * b + k < tr.height 19 := by omega
  have ha : mbN tr (9 * b + k) 0 = 1 := (memb_posS H _ hr8 ha8).1 _ (by omega)
  have hm : (9 * b + k) % 9 = k := by omega
  obtain ⟨hc, -, e2⟩ := memb_msg_evalS H hr ha (by omega) hi
  have hbc := memb_blk_constS H hr8 ha8 k (by omega)
  have hbl := (memb_blk_ltS H hr8 ha8).1
  have hbo : mbN tr (9 * b + k) (142 + i) < P := rowNat_lt _ _ _ _
  refine ⟨((Memb.c s!"tq{i}").eval (tr.row pub 19 (9 * b + k))).toNat,
    mem_part_dec.mpr ⟨9 * b + k, hr, _, mem_rowMsgs_of (memb_recv_mem i hi) rfl rfl hc, ?_⟩⟩
  rw [e2, hm, hbc]
  simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ]
  rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
    Fp.toNat_cast_of_lt hbo]


/-- A read-only block's leaf message has new = old (MEMB: `p8·ro·(hoO − hoI) = 0`). -/
theorem memb_ro_leafS {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hro : bc tr (9 * b + 8) 11 = 1) :
    bdig tr (9 * b + 8) 534 = bdig tr (9 * b + 8) 486 := by
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_posS H _ hr8 ha8).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  unfold bdig
  apply List.map_congr_left; intro l hl
  have hl' := List.mem_range.mp hl
  have hmem : Memb.p 8 * Memb.c "ro" * (Memb.c s!"hoO{l}" - Memb.c s!"hoI{l}") ∈ Memb.constraints := by
    unfold Memb.constraints
    exact List.mem_append_right _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
  have h := memb_CS H hr8 _ hmem
  simp only [Expr.eval_mul', Expr.eval_sub', memb_p_eval tr pub _ (show 8 < 9 by decide), hp8, memb_c_eval,
    mb_ix.2.2, (mb_ix_ho l hl').1, (mb_ix_ho l hl').2] at h
  have e : ∀ i, bc tr (9 * b + 8) i = ((mbN tr (9 * b + 8) i : Nat) : F) := fun i => cell_cast tr 19 _ i
  rw [e] at hro
  rw [hro, e, e] at *
  rw [cast_one] at h
  grind


/-- A read-only block's out bytes are its in bytes (`ro·(bo − bi) = 0`). -/
theorem memb_ro_bytesS {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hro : mbN tr (9 * b + 8) 11 = 1) : SegSha.membBytes tr b "bo" = SegSha.membBytes tr b "bi" := by
  unfold SegSha.membBytes
  apply List.map_congr_left; intro j hj
  have hj' := List.mem_range.mp hj
  have hk : j / 128 < 8 := by omega
  have hi : j % 128 < 128 := Nat.mod_lt _ (by decide)
  have hr : 9 * b + j / 128 < tr.height 19 := by omega
  have ro1 : mbN tr (9 * b + j / 128) 11 = 1 := (SegSha.memb_ro_constS H hr8 ha8 (j / 128) (by omega)).trans hro
  have hmem : Memb.c "ro" * (Memb.c s!"bo{j % 128}" - Memb.c s!"bi{j % 128}") ∈ Memb.constraints := by
    unfold Memb.constraints
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ ?_)))))
    exact List.mem_map.mpr ⟨j % 128, List.mem_range.mpr hi, rfl⟩
  have h := memb_CS H hr _ hmem
  simp only [Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.2.2, ro1, cast_one] at h
  have h' : ((mbN tr (9 * b + j / 128) (ix Memb.cols s!"bo{j % 128}") : Nat) : F) =
      ((mbN tr (9 * b + j / 128) (ix Memb.cols s!"bi{j % 128}") : Nat) : F) := by grind
  rw [natEq h' (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)]


/-- The bytes of a touched block `b`: the leaf `hoI` is SHA-384 of MEMB's `bi` bytes. -/
theorem leaf_in_bytesS {chip : List IfMsg} (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip)
    {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1) :
    bytesOf (bdig tr (9 * b + 8) 486) = sha384 (SegSha.membBytes tr b "bi") := by
  obtain ⟨-, d, hl, hw, e, eb⟩ := SegSha.memb_leaf_inS H hC hr8 ha8
  exact (show Canon (bdig tr (9 * b + 8) 486) _ from ⟨d, hl, hw, e, eb⟩).bytes


end membS

end MemRoot

#print axioms MemRoot.memb_act_of_pS
#print axioms MemRoot.memb_pad_of_p8S
#print axioms MemRoot.memb_fwdS
#print axioms MemRoot.memb_pad_of_dataS
#print axioms MemRoot.memb_msg_evalS
#print axioms MemRoot.memb_kD_inactS
#print axioms MemRoot.memb_blk_ltS
#print axioms MemRoot.memb_bi_lt'S
#print axioms MemRoot.memb_prod_formS
#print axioms MemRoot.memb_cons_memS
#print axioms MemRoot.memb_ro_leafS
#print axioms MemRoot.memb_ro_bytesS
#print axioms MemRoot.leaf_in_bytesS

end WasmBase
