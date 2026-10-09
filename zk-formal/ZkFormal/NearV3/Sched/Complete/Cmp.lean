import ZkFormal.NearV3.Sched.Complete.Trace
import ZkFormal.NearV3.Sched.Gen.Cmp

/-!
# ZkFormal.NearV3.Sched.Complete.Cmp — completeness of the comparator `scpV3` (M4)

For any list of comparisons `(x, y, b)` with `x, y < 2^29` and `b = [y ≤ x]` (`CmpOk`) that fits
the table (`|cmps| ≤ 2^22`), the honest trace `Gen.Cmp.trace cmps`:

* has log height in `[1, maxLog]`;
* satisfies every constraint on every row (generated rows and padding rows `x = y = 0, b = 1`);
* has boolean multiplicity bits;
* receives on `SCMP` exactly the messages `Gen.Cmp.expected cmps` (multiplicity one each, as
  field elements) and sends nothing (`cmp_complete`).
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Cmp

/-- An honest comparison: operands `< 2^29`, `b = [y ≤ x]`. -/
def CmpOk (q : Nat × Nat × Nat) : Prop :=
  q.1 < 2 ^ 29 ∧ q.2.1 < 2 ^ 29 ∧ q.2.2 = if q.2.1 ≤ q.1 then 1 else 0

/-- The decomposed difference of a comparator row. -/
def dOf (x y b : Nat) : Nat := if b = 1 then x - y else y - x - 1

/-- Cells of a generated comparator row. -/
def cmpCell (x y b c : Nat) : Nat :=
  if c = colAct then 1 else if c = colX then x else if c = colY then y else if c = colB then b
  else if 4 ≤ c ∧ c < 4 + Sched.Cmp.nbits then bit (dOf x y b) (c - 4) else 0

def padCell (c : Nat) : Nat := if c = colB then 1 else 0

theorem row_eq (x y b : Nat) : Gen.Cmp.row x y b =
    (List.range Sched.Cmp.nbits).foldl (fun a i => a.set! (4 + i) (bit (dOf x y b) i))
      (((((zrow width).set! colAct 1).set! colX x).set! colY y).set! colB b) := by
  unfold Gen.Cmp.row
  simp only [Id.run, colD, dOf, List.forIn_pure_yield_eq_foldl]
  rfl

theorem gd_row (x y b c : Nat) : gd (Gen.Cmp.row x y b) c = cmpCell x y b c := by
  rw [row_eq, gd_range_set _ _ _ _ (by simp [size_zrow, width, Sched.Cmp.nbits])]
  simp only [gd_set, gd_zrow, size_set, size_zrow, cmpCell, colAct, colX, colY, colB, width]
  by_cases h0 : c = 0
  · subst h0; simp [Sched.Cmp.nbits]
  by_cases h1 : c = 1
  · subst h1; simp [Sched.Cmp.nbits]
  by_cases h2 : c = 2
  · subst h2; simp [Sched.Cmp.nbits]
  by_cases h3 : c = 3
  · subst h3; simp [Sched.Cmp.nbits]
  simp [h0, h1, h2, h3]

theorem gd_pad (c : Nat) : gd Gen.Cmp.padRow c = padCell c := by
  simp only [Gen.Cmp.padRow, gd_set, gd_zrow, size_zrow, padCell, colB, width]
  by_cases h : c = 3 <;> simp [h]

theorem rows_size (cmps : List (Nat × Nat × Nat)) : (Gen.Cmp.rows cmps).size = cmps.length := by
  simp [Gen.Cmp.rows]

theorem rows_get (cmps : List (Nat × Nat × Nat)) {r : Nat} (hr : r < cmps.length) :
    natRow (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) r =
      Gen.Cmp.row cmps[r].1 cmps[r].2.1 cmps[r].2.2 := by
  rw [natRow_lt _ _ (by rw [rows_size]; exact hr)]
  simp [Gen.Cmp.rows]

theorem cell_lt_rows (cmps : List (Nat × Nat × Nat)) {r : Nat} (hr : r < cmps.length) (c : Nat) :
    natCell (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) r c =
      cmpCell cmps[r].1 cmps[r].2.1 cmps[r].2.2 c := by
  unfold natCell; rw [rows_get cmps hr, gd_row]

theorem cell_ge_rows (cmps : List (Nat × Nat × Nat)) {r : Nat} (hr : cmps.length ≤ r) (c : Nat) :
    natCell (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) r c = padCell c := by
  unfold natCell; rw [natRow_ge _ _ (by rw [rows_size]; exact hr), gd_pad]

theorem bit_le (x i : Nat) : bit x i ≤ 1 := bt_le x i

theorem dOf_lt {q : Nat × Nat × Nat} (h : CmpOk q) : dOf q.1 q.2.1 q.2.2 < 2 ^ Sched.Cmp.nbits := by
  obtain ⟨hx, hy, hb⟩ := h
  unfold dOf Sched.Cmp.nbits
  rw [hb]
  split <;> split <;> omega

theorem cmpCell_lt {q : Nat × Nat × Nat} (h : CmpOk q) (c : Nat) : cmpCell q.1 q.2.1 q.2.2 c < 2 ^ 29 := by
  obtain ⟨hx, hy, hb⟩ := h
  have := bit_le (dOf q.1 q.2.1 q.2.2) (c - 4)
  unfold cmpCell
  repeat' split
  all_goals first | omega | (rw [hb]; split <;> decide)

theorem small (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, CmpOk q) :
    HSmall (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) := by
  intro r c
  by_cases hr : r < cmps.length
  · rw [cell_lt_rows cmps hr]
    exact Nat.lt_trans (cmpCell_lt (hok _ (List.getElem_mem hr)) c) (by decide)
  · rw [cell_ge_rows cmps (by omega)]
    unfold padCell; split <;> decide

/-! ## Constraints -/

/-- A row given by a cell function `f` (current row only). -/
theorem zev_boolC {Z : ZEnv} {x : Nat} (h : Z.cur x ≤ 1) : zev Z (ZkFormal.Chacha.Table.boolC x) = 0 := by
  simp only [ZkFormal.Chacha.Table.boolC, zev_mul, zev_sub, zev_c, zev_k]
  rcases (show Z.cur x = 0 ∨ Z.cur x = 1 by omega) with e | e <;> rw [e] <;> decide

theorem zev_dE_of {Z : ZEnv} (f : Nat → Nat) (hZ : ∀ c, Z.cur c = f c) :
    zev Z dE = (Chacha.nbits (fun b => f (colD b)) Sched.Cmp.nbits : Int) := by
  unfold dE ZkFormal.Chacha.Rng.Table.num
  exact zev_sum_pow _ (fun b => .col (colD b) false) _ Sched.Cmp.nbits (fun b _ => by
    show (if false = true then _ else ((Z.cur (colD b) : Nat) : Int)) = _
    rw [hZ]; rfl)

theorem constraints_row {Z : ZEnv} (x y b : Nat) (hok : CmpOk (x, y, b))
    (hZ : ∀ c, Z.cur c = cmpCell x y b c) : ∀ e ∈ constraints, zev Z e = 0 := by
  obtain ⟨hx, hy, hb⟩ := hok
  have hbit : Z.cur colB ≤ 1 := by
    have e3 : cmpCell x y b colB = b := by simp [cmpCell, colAct, colX, colY, colB]
    simp only at hb
    rw [hZ, e3, hb]; split <;> omega
  intro e he
  simp only [constraints, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at he
  rcases he with ((he | he) | ⟨j, hj, rfl⟩) | he
  · subst he; exact zev_boolC (by rw [hZ]; simp [cmpCell, colAct])
  · subst he; exact zev_boolC hbit
  · apply zev_boolC
    rw [hZ]
    unfold cmpCell colD colAct colX colY colB
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by unfold Sched.Cmp.nbits at hj ⊢; omega)]
    exact bit_le _ _
  · subst he
    rw [mainC]
    simp only [zev_sub, zev_add, zev_mul, zev_c, zev_k]
    rw [zev_dE_of _ hZ]
    have hn : Chacha.nbits (fun i => cmpCell x y b (colD i)) Sched.Cmp.nbits = dOf x y b := by
      rw [nbits_congr (g := bt (dOf x y b)) (fun i hi => by
        unfold cmpCell colD colAct colX colY colB
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by unfold Sched.Cmp.nbits at hi ⊢; omega), show 4 + i - 4 = i by omega]; rfl),
        nbits_bt, Nat.mod_eq_of_lt (dOf_lt (q := (x, y, b)) ⟨hx, hy, hb⟩)]
    rw [hn]
    simp only [hZ, cmpCell, colAct, colX, colY, colB]
    simp only at hb
    simp only [show (1 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 0 from by decide,
      show (2 : Nat) ≠ 1 from by decide, show (3 : Nat) ≠ 0 from by decide,
      show (3 : Nat) ≠ 1 from by decide, show (3 : Nat) ≠ 2 from by decide, if_false, if_true]
    unfold dOf
    rw [hb]
    by_cases hyx : y ≤ x
    · simp only [if_pos hyx, if_true]; push_cast; omega
    · simp only [if_neg hyx, show (0 : Nat) ≠ 1 from by decide, if_false]; push_cast; omega

theorem constraints_pad {Z : ZEnv} (hZ : ∀ c, Z.cur c = padCell c) : ∀ e ∈ constraints, zev Z e = 0 := by
  intro e he
  have hc : ∀ c, Z.cur c ≤ 1 := fun c => by rw [hZ]; unfold padCell; split <;> decide
  simp only [constraints, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at he
  rcases he with ((he | he) | ⟨j, hj, rfl⟩) | he
  · subst he; exact zev_boolC (hc _)
  · subst he; exact zev_boolC (hc _)
  · exact zev_boolC (hc _)
  · subst he
    rw [mainC]
    simp only [zev_sub, zev_add, zev_mul, zev_c, zev_k]
    rw [zev_dE_of _ hZ, nbits_congr (g := fun _ => 0) (fun i hi => by
      unfold padCell colD colB; rw [if_neg (by omega)])]
    have h0 : ∀ m, Chacha.nbits (fun _ => 0) m = 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => simp [ZkFormal.Chacha.nbits, ih]
    rw [h0]
    simp [hZ, padCell, colX, colY, colB]

/-! ## The honest trace -/

section
variable (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, CmpOk q)
include hok

theorem cmp_constraints (t : Nat) (pub : List Fp) (r : Nat)
    (hr : r < (Gen.Cmp.trace cmps).height t) :
    ∀ e ∈ constraints, e.eval (Gen.Cmp.trace cmps) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  have hE := (mk_env _ 0 _ (small cmps hok) t hr pub).1
  by_cases hin : r < cmps.length
  · have hq := hok _ (List.getElem_mem hin)
    exact constraints_row _ _ _ hq (fun c => by have h := hE c; rw [cell_lt_rows cmps hin] at h; exact h) e he
  · exact constraints_pad (fun c => by have h := hE c; rw [cell_ge_rows cmps (by omega)] at h; exact h) e he

end

theorem act_cell (cmps : List (Nat × Nat × Nat)) (r : Nat) :
    natCell (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) r colAct =
      if r < cmps.length then 1 else 0 := by
  by_cases hin : r < cmps.length
  · rw [cell_lt_rows cmps hin, if_pos hin]; rfl
  · rw [cell_ge_rows cmps (by omega), if_neg hin]; rfl

theorem cmp_bits (cmps : List (Nat × Nat × Nat)) (busCmp t r : Nat) (pub : List Fp)
    (hr : r < (Gen.Cmp.trace cmps).height t) :
    ∀ i ∈ interactions busCmp, ∀ b ∈ i.mult,
      b.eval (Gen.Cmp.trace cmps) t r pub = 0 ∨ b.eval (Gen.Cmp.trace cmps) t r pub = 1 := by
  intro i hi b hb
  simp only [interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  show (Gen.Cmp.trace cmps).cell t r colAct = 0 ∨ (Gen.Cmp.trace cmps).cell t r colAct = 1
  rw [Gen.Cmp.trace, mk_cell _ _ _ t hr, act_cell]
  exact ofNat_bit (by split <;> omega)

/-! ## Traffic -/

theorem flatMap_single {α β : Type} (f : α → β) : ∀ l : List α, l.flatMap (fun x => [f x]) = l.map f
  | [] => rfl
  | x :: l => by rw [List.flatMap_cons, flatMap_single f l]; rfl

theorem range_map_getD {α β : Type} (l : List α) (d : α) (g : α → β) :
    (List.range l.length).map (fun r => g (l.getD r d)) = l.map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]; rfl

/-- The expected messages as field elements. -/
def fmsgs (l : List (List Nat)) : List (List Fp) := l.map (·.map Fp.ofNat)

/-- The message of a comparison, as field elements. -/
def cmpMsg (q : Nat × Nat × Nat) : List Fp := [Fp.ofNat q.1, Fp.ofNat q.2.1, Fp.ofNat q.2.2]

theorem fmsgs_expected (cmps : List (Nat × Nat × Nat)) :
    fmsgs (Gen.Cmp.expected cmps) = cmps.map cmpMsg := by
  unfold fmsgs Gen.Cmp.expected
  rw [List.map_map]
  exact List.map_congr_left (fun q _ => by obtain ⟨x, y, b⟩ := q; rfl)

theorem count_map_eq_sum {α β : Type} [DecidableEq β] [BEq β] [LawfulBEq β] (f : α → β) (m : β) :
    ∀ l : List α, (l.map f).count m = (l.map fun x => if f x = m then 1 else 0).sum
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.count_cons, count_map_eq_sum f m l, List.map_cons, List.sum_cons]
    by_cases h : f x = m
    · simp [h]; omega
    · simp [h]

theorem sum_range_trunc (g : Nat → Nat) {len : Nat} (hz : ∀ r, len ≤ r → g r = 0) :
    ∀ H, len ≤ H → ((List.range H).map g).sum = ((List.range len).map g).sum
  | 0, h => by rw [show len = 0 by omega]
  | H + 1, h => by
    by_cases e : len = H + 1
    · rw [e]
    · rw [List.range_succ, List.map_append, List.sum_append, sum_range_trunc g hz H (by omega),
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hz H (by omega)]
      omega

theorem cmp_row_count (cmps : List (Nat × Nat × Nat)) (busCmp t r : Nat) (pub : List Fp) (m : List Fp)
    (hr : r < (Gen.Cmp.trace cmps).height t) (send : Bool) :
    ((interactions busCmp).map fun i =>
      if i.bus = busCmp ∧ i.send = send ∧ i.msgVal (Gen.Cmp.trace cmps) t r pub = m then
        i.multNat (Gen.Cmp.trace cmps) t r pub else 0).sum =
      if send = false ∧ r < cmps.length ∧ cmpMsg (cmps.getD r (0, 0, 0)) = m then 1 else 0 := by
  have hcell := fun c => mk_cell (Gen.Cmp.rows cmps) 0 (fun _ => Gen.Cmp.padRow) t hr c
  simp only [interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hmult : Interaction.multNat { bus := busCmp, mult := [ZkFormal.Chacha.Table.E.c colAct], send := false, msg := msg } (Gen.Cmp.trace cmps) t r pub = if r < cmps.length then 1 else 0 := by
    simp only [Interaction.multNat, Interaction.multNat.go]
    show (if (Gen.Cmp.trace cmps).cell t r colAct = 1 then 2 ^ 0 else 0) + 0 = _
    rw [Gen.Cmp.trace, hcell, act_cell]
    split <;> rfl
  rw [hmult]
  by_cases hin : r < cmps.length
  · have hv : Interaction.msgVal { bus := busCmp, mult := [ZkFormal.Chacha.Table.E.c colAct], send := false, msg := msg } (Gen.Cmp.trace cmps) t r pub = cmpMsg (cmps.getD r (0, 0, 0)) := by
      simp only [Interaction.msgVal, msg, List.map_cons, List.map_nil]
      show [(Gen.Cmp.trace cmps).cell t r colX, (Gen.Cmp.trace cmps).cell t r colY,
        (Gen.Cmp.trace cmps).cell t r colB] = _
      rw [Gen.Cmp.trace, hcell, hcell, hcell, cell_lt_rows cmps hin, cell_lt_rows cmps hin,
        cell_lt_rows cmps hin, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some]
      rfl
    rw [hv, if_pos hin]
    by_cases hs : send = false
    · subst hs
      by_cases e : cmpMsg (cmps.getD r (0, 0, 0)) = m
      · simp only [e, hin, true_and, and_self, if_true]
      · simp only [e, hin, true_and, and_false, if_false]
    · have h' : ¬ (false = send) := fun h => hs h.symm
      simp [h', hs]
  · rw [if_neg hin]; simp [hin]

theorem cmp_count (cmps : List (Nat × Nat × Nat)) (busCmp t : Nat) (pub : List Fp) (m : List Fp)
    (send : Bool) :
    tableBusCount (interactions busCmp) (Gen.Cmp.trace cmps) t pub busCmp send m =
      if send = false then (fmsgs (Gen.Cmp.expected cmps)).count m else 0 := by
  rw [busCount_sum]
  have hle : cmps.length ≤ (Gen.Cmp.trace cmps).height t := by
    have := mk_rows_le (Gen.Cmp.rows cmps) 0 (fun _ => Gen.Cmp.padRow) t
    rw [rows_size, Nat.add_zero] at this; exact this
  rw [List.map_congr_left (fun r hr => cmp_row_count cmps busCmp t r pub m (List.mem_range.1 hr) send)]
  by_cases hs : send = false
  · subst hs
    rw [if_pos rfl, sum_range_trunc (fun r => if false = false ∧ r < cmps.length ∧
        cmpMsg (cmps.getD r (0, 0, 0)) = m then 1 else 0) (len := cmps.length)
        (fun r hr => if_neg (fun h => absurd h.2.1 (by omega))) _ hle]
    rw [fmsgs_expected, count_map_eq_sum, ← range_map_getD cmps (0, 0, 0)]
    apply congrArg
    apply List.map_congr_left
    intro r hr
    have := List.mem_range.1 hr
    by_cases e : cmpMsg (cmps.getD r (0, 0, 0)) = m
    · simp only [e, this, true_and, and_self, if_true]
    · simp only [e, this, true_and, and_false, if_false]
  · rw [if_neg hs]
    rw [List.map_congr_left (g := fun _ => 0) (fun r _ => by rw [if_neg (fun h => hs h.1)])]
    exact sum_map_zero _

/-- **Completeness of the comparator `scpV3`.** -/
theorem cmp_complete (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, CmpOk q)
    (hrows : cmps.length ≤ 2 ^ Cmp.maxLog) (busCmp : Nat) :
    (∀ t, 1 ≤ (Gen.Cmp.trace cmps).log t ∧ (Gen.Cmp.trace cmps).log t ≤ Cmp.maxLog) ∧
    (∀ t pub r, r < (Gen.Cmp.trace cmps).height t → ∀ e ∈ Cmp.constraints,
       e.eval (Gen.Cmp.trace cmps) t r pub = 0) ∧
    (∀ t pub r, r < (Gen.Cmp.trace cmps).height t → ∀ i ∈ Cmp.interactions busCmp, ∀ b ∈ i.mult,
       b.eval (Gen.Cmp.trace cmps) t r pub = 0 ∨ b.eval (Gen.Cmp.trace cmps) t r pub = 1) ∧
    (∀ t pub m,
       tableBusCount (Cmp.interactions busCmp) (Gen.Cmp.trace cmps) t pub busCmp false m =
         (fmsgs (Gen.Cmp.expected cmps)).count m ∧
       tableBusCount (Cmp.interactions busCmp) (Gen.Cmp.trace cmps) t pub busCmp true m = 0) :=
  ⟨fun t => mk_log_bounds _ 0 _ (by decide) (by rw [rows_size]; exact hrows) t,
   fun t pub r hr => cmp_constraints cmps hok t pub r hr,
   fun t pub r hr => cmp_bits cmps busCmp t r pub hr,
   fun t pub m => ⟨by rw [cmp_count]; rfl, by rw [cmp_count]; rfl⟩⟩

end ZkFormal.NearV3.Sched.Complete
