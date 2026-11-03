import WasmBase.Bus
/-!
# WasmBase.Main.BusCount — counting bus occurrences by table row (E2E M4b)

`busNat A tr pub b s m` (the summed count of message `m` on bus `b`, direction `s`) is a sum over the
tables and their rows.  Two counting facts the multiproof argument (`Main/SegMP.lean`) needs and
`WasmBase.Bus` does not state:

* `two_le_busNat`: two **different rows** of one table carrying `m` with count 1 through the same
  interaction contribute 2;
* `busNat_le_row`: if every row other than `(t0, r0)` contributes nothing, the sum is row
  `(t0, r0)`'s contribution `rowCnt`, which `rowCnt_le_filter` bounds by the interactions of that
  table on bus `b`, direction `s`.
-/
namespace WasmBase
open ZkFormal.Algebra

/-- The summed count of `m` on bus `b`, direction `s`, in a list of occurrences. -/
def cntM (b : Nat) (s : Bool) (m : List F) (l : List Occ) : Nat :=
  ((l.filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).map (·.2.2.2)).sum

theorem cntM_nil (b : Nat) (s : Bool) (m : List F) : cntM b s m [] = 0 := rfl

theorem cntM_append (b : Nat) (s : Bool) (m : List F) (l₁ l₂ : List Occ) :
    cntM b s m (l₁ ++ l₂) = cntM b s m l₁ + cntM b s m l₂ := by
  simp [cntM, List.filter_append, List.map_append, List.sum_append]

theorem cntM_flatMap {β : Type} (b : Nat) (s : Bool) (m : List F) (l : List β) (g : β → List Occ) :
    cntM b s m (l.flatMap g) = (l.map fun x => cntM b s m (g x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, cntM_append, ih]; simp

theorem busNat_eq_cntM (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    busNat A tr pub b s m = cntM b s m (occs A tr pub) := rfl

/-- The occurrences of row `r` of table `T` (index `t`). -/
def rowOccsT (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : List Occ :=
  T.inters.map fun i => (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)

/-- Row `r` of table `t`'s contribution to `busNat … b s m`. -/
def rowCnt (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (m : List F) (t r : Nat)
    (ht : t < A.tables.length) : Nat :=
  cntM b s m (rowOccsT (A.tables[t]'ht) tr pub t r)

theorem busNat_rows (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    busNat A tr pub b s m = (A.tables.zipIdx.map fun (Tt : Table × Nat) =>
      ((List.range (tr.height Tt.2)).map fun r => cntM b s m (rowOccsT Tt.1 tr pub Tt.2 r)).sum).sum := by
  rw [busNat_eq_cntM, occs, cntM_flatMap]
  congr 1; apply List.map_congr_left; intro Tt _
  rw [cntM_flatMap]; rfl

/-! ## Sums over lists -/

theorem le_sum_map {α : Type} (l : List α) (F : α → Nat) {a : α} (ha : a ∈ l) : F a ≤ (l.map F).sum :=
  le_sum_of_mem_nat (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem two_le_sum_map {α : Type} (l : List α) (hn : l.Nodup) (F : α → Nat) {a c : α} (ha : a ∈ l)
    (hc : c ∈ l) (hac : a ≠ c) : F a + F c ≤ (l.map F).sum := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    obtain ⟨hx, hn'⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hc with rfl | hc'
      · exact absurd rfl hac
      · have := le_sum_map l F hc'; omega
    · rcases List.mem_cons.mp hc with rfl | hc'
      · have := le_sum_map l F ha'; omega
      · have := ih hn' ha' hc'; omega

theorem sum_map_le_point {α : Type} (l : List α) (hn : l.Nodup) (F : α → Nat) (x0 : α)
    (h : ∀ x ∈ l, x ≠ x0 → F x = 0) : (l.map F).sum ≤ F x0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hx, hn'⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.sum_cons]
    by_cases e : x = x0
    · subst e
      have : (l.map F).sum = 0 := sum_eq_zero_of_all fun a ha => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        exact h y (List.mem_cons_of_mem _ hy) (fun e => hx (e ▸ hy))
      omega
    · rw [h x List.mem_cons_self e]
      have := ih hn' (fun y hy => h y (List.mem_cons_of_mem _ hy)); omega

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ l : List α, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    refine List.nodup_cons.mpr ⟨fun hx => h.1 (List.mem_map.mpr ⟨x, hx, rfl⟩), nodup_of_map f l h.2⟩

theorem zipIdx_nodup {α : Type} (l : List α) : l.zipIdx.Nodup := by
  apply nodup_of_map Prod.snd
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

theorem mem_zipIdx_tables {A : Air} {T : Table} {t : Nat} (h : (T, t) ∈ A.tables.zipIdx) :
    ∃ ht : t < A.tables.length, A.tables[t]'ht = T := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only at h
  have ht : t < A.tables.length := by
    rcases h' : A.tables[t]? with _ | T'
    · simp [h'] at h
    · exact (List.getElem?_eq_some_iff.mp h').1
  refine ⟨ht, ?_⟩
  have := List.getElem?_eq_getElem ht
  rw [h] at this; exact (Option.some.inj this).symm

theorem mem_zipIdx_of {A : Air} {t : Nat} (ht : t < A.tables.length) :
    (A.tables[t]'ht, t) ∈ A.tables.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]; simp [List.getElem?_eq_getElem ht]

/-! ## Two rows, one row -/

/-- An occurrence of interaction `i` of row `r` with message `m` and count 1 contributes 1. -/
theorem one_le_rowCnt {A : Air} {tr : Trace} {pub : List F} {t : Nat} (ht : t < A.tables.length) {r : Nat}
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) {m : List F}
    (hm : i.msg.map (·.eval (tr.row pub t r)) = m) (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    1 ≤ rowCnt A tr pub i.bus i.send m t r ht := by
  unfold rowCnt cntM rowOccsT
  rw [← hc]
  apply le_sum_of_mem_nat
  refine List.mem_map.mpr ⟨(i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat),
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨i, hi, rfl⟩, by simp [hm]⟩, rfl⟩

/-- **Two rows.**  Different rows `r ≠ r'` of table `t` carrying `m` with count 1 through the same
interaction `i`: `busNat … i.bus i.send m ≥ 2`. -/
theorem two_le_busNat {A : Air} {tr : Trace} {pub : List F} {t : Nat} (ht : t < A.tables.length)
    {r r' : Nat} (hr : r < tr.height t) (hr' : r' < tr.height t) (hne : r ≠ r')
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) {m : List F}
    (hm : i.msg.map (·.eval (tr.row pub t r)) = m) (hc : (i.count.eval (tr.row pub t r)).toNat = 1)
    (hm' : i.msg.map (·.eval (tr.row pub t r')) = m) (hc' : (i.count.eval (tr.row pub t r')).toNat = 1) :
    2 ≤ busNat A tr pub i.bus i.send m := by
  rw [busNat_rows]
  have h1 := one_le_rowCnt ht hi hm hc
  have h2 := one_le_rowCnt ht hi hm' hc'
  have hrow := two_le_sum_map (List.range (tr.height t)) List.nodup_range
    (fun r => cntM i.bus i.send m (rowOccsT (A.tables[t]'ht) tr pub t r))
    (List.mem_range.mpr hr) (List.mem_range.mpr hr') hne
  have htab := le_sum_map A.tables.zipIdx (fun (Tt : Table × Nat) =>
      ((List.range (tr.height Tt.2)).map fun r => cntM i.bus i.send m (rowOccsT Tt.1 tr pub Tt.2 r)).sum)
    (mem_zipIdx_of ht)
  unfold rowCnt at h1 h2
  simp only at hrow htab
  omega

/-- **One row.**  If every row other than `(t0, r0)` contributes nothing to `busNat … b s m`, the sum
is at most row `(t0, r0)`'s contribution. -/
theorem busNat_le_row {A : Air} {tr : Trace} {pub : List F} {b : Nat} {s : Bool} {m : List F}
    {t0 : Nat} (ht0 : t0 < A.tables.length) (r0 : Nat)
    (h : ∀ t (ht : t < A.tables.length) r, r < tr.height t → (t ≠ t0 ∨ r ≠ r0) → rowCnt A tr pub b s m t r ht = 0) :
    busNat A tr pub b s m ≤ rowCnt A tr pub b s m t0 r0 ht0 := by
  rw [busNat_rows]
  have hpt := sum_map_le_point A.tables.zipIdx (zipIdx_nodup _) (fun (Tt : Table × Nat) =>
      ((List.range (tr.height Tt.2)).map fun r => cntM b s m (rowOccsT Tt.1 tr pub Tt.2 r)).sum)
    (A.tables[t0]'ht0, t0) (by
      rintro ⟨T, t⟩ hx hne
      obtain ⟨ht, rfl⟩ := mem_zipIdx_tables hx
      have htt : t ≠ t0 := fun e => hne (by subst e; rfl)
      apply sum_eq_zero_of_all
      intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact h t ht r (List.mem_range.mp hr) (Or.inl htt))
  refine Nat.le_trans hpt ?_
  simp only
  by_cases h0 : r0 < tr.height t0
  · have := sum_map_le_point (List.range (tr.height t0)) List.nodup_range
      (fun r => cntM b s m (rowOccsT (A.tables[t0]'ht0) tr pub t0 r)) r0 (fun r hr hne =>
        h t0 ht0 r (List.mem_range.mp hr) (Or.inr hne))
    exact this
  · have : ((List.range (tr.height t0)).map fun r => cntM b s m (rowOccsT (A.tables[t0]'ht0) tr pub t0 r)).sum = 0 :=
      sum_eq_zero_of_all fun a ha => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
        exact h t0 ht0 r (List.mem_range.mp hr) (Or.inr (by intro e; subst e; exact h0 (List.mem_range.mp hr)))
    omega

/-- A row's contribution only involves the table's interactions on bus `b`, direction `s`. -/
theorem rowCnt_filter {A : Air} {tr : Trace} {pub : List F} {b : Nat} {s : Bool} {m : List F} {t : Nat}
    (ht : t < A.tables.length) (r : Nat) :
    rowCnt A tr pub b s m t r ht =
      cntM b s m (((A.tables[t]'ht).inters.filter fun i => i.bus = b ∧ i.send = s).map fun i =>
        (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)) := by
  unfold rowCnt rowOccsT cntM
  rw [List.filter_map, List.filter_map, List.filter_filter]
  congr 3
  apply List.filter_congr
  intro i _
  simp only [Function.comp_apply]
  by_cases h1 : i.bus = b <;> by_cases h2 : i.send = s <;> simp [h1, h2]


/-- A table without interactions on bus `b`, direction `s`, contributes nothing. -/
theorem rowCnt_zero_of_none {A : Air} {tr : Trace} {pub : List F} {b : Nat} {s : Bool} {m : List F} {t : Nat}
    (ht : t < A.tables.length) (r : Nat) (hnone : ∀ i ∈ (A.tables[t]'ht).inters, ¬ (i.bus = b ∧ i.send = s)) :
    rowCnt A tr pub b s m t r ht = 0 := by
  rw [rowCnt_filter, List.filter_eq_nil_iff.mpr (by intro i hi; simpa using hnone i hi)]
  rfl

theorem cntM_cons (b : Nat) (s : Bool) (m : List F) (o : Occ) (l : List Occ) :
    cntM b s m (o :: l) = (if o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m then o.2.2.2 else 0) + cntM b s m l := by
  unfold cntM
  by_cases h : o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m
  · rw [List.filter_cons_of_pos (by simpa using h)]; simp [h]
  · rw [List.filter_cons_of_neg (by simpa using h)]; simp [h]

/-- A row's contribution through the table's interactions on bus `b` only. -/
theorem rowCnt_filter_bus {A : Air} {tr : Trace} {pub : List F} {b : Nat} {s : Bool} {m : List F} {t : Nat}
    (ht : t < A.tables.length) (r : Nat) :
    rowCnt A tr pub b s m t r ht =
      cntM b s m (((A.tables[t]'ht).inters.filter fun i => i.bus = b).map fun i =>
        (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)) := by
  unfold rowCnt rowOccsT cntM
  rw [List.filter_map, List.filter_map, List.filter_filter]
  congr 3
  apply List.filter_congr
  intro i _
  simp only [Function.comp_apply]
  by_cases h1 : i.bus = b <;> simp [h1]

/-- An occurrence `(b, s, m, 1)` of row `r` contributes 1. -/
theorem one_le_rowCnt' {A : Air} {tr : Trace} {pub : List F} {t : Nat} (ht : t < A.tables.length) {r b : Nat}
    {s : Bool} {m : List F} (h : (b, s, m, 1) ∈ rowOccsT (A.tables[t]'ht) tr pub t r) :
    1 ≤ rowCnt A tr pub b s m t r ht := by
  unfold rowCnt cntM
  exact le_sum_of_mem_nat (List.mem_map.mpr ⟨(b, s, m, 1), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩)

/-- **Two rows** (occurrence form): `(b, s, m, 1)` in two different rows of table `t`. -/
theorem two_le_busNat' {A : Air} {tr : Trace} {pub : List F} {t : Nat} (ht : t < A.tables.length)
    {r r' : Nat} (hr : r < tr.height t) (hr' : r' < tr.height t) (hne : r ≠ r') {b : Nat} {s : Bool} {m : List F}
    (h : (b, s, m, 1) ∈ rowOccsT (A.tables[t]'ht) tr pub t r)
    (h' : (b, s, m, 1) ∈ rowOccsT (A.tables[t]'ht) tr pub t r') :
    2 ≤ busNat A tr pub b s m := by
  rw [busNat_rows]
  have h1 := one_le_rowCnt' ht h
  have h2 := one_le_rowCnt' ht h'
  have hrow := two_le_sum_map (List.range (tr.height t)) List.nodup_range
    (fun r => cntM b s m (rowOccsT (A.tables[t]'ht) tr pub t r))
    (List.mem_range.mpr hr) (List.mem_range.mpr hr') hne
  have htab := le_sum_map A.tables.zipIdx (fun (Tt : Table × Nat) =>
      ((List.range (tr.height Tt.2)).map fun r => cntM b s m (rowOccsT Tt.1 tr pub Tt.2 r)).sum)
    (mem_zipIdx_of ht)
  unfold rowCnt at h1 h2
  simp only at hrow htab
  omega

theorem mem_rowOccsT_of_filter {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {o : Occ}
    (h : o ∈ (T.inters.filter fun i => i.bus = b).map fun i =>
      ((i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) : Occ)) :
    o ∈ rowOccsT T tr pub t r := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩

theorem mem_occs_of_rowOccsT {A : Air} {tr : Trace} {pub : List F} {t : Nat} (ht : t < A.tables.length) {r : Nat}
    (hr : r < tr.height t) {o : Occ} (h : o ∈ rowOccsT (A.tables[t]'ht) tr pub t r) : o ∈ occs A tr pub := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact mem_occs.mpr ⟨t, ht, r, hr, i, hi, rfl⟩

end WasmBase
