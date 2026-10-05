import ZkFormal.Stark.Statements

/-!
# ZkFormal.Stark.NpBounds — `NpBoundsStmt`

On admissible headers the `np-udr-stark-v1` schedule has at most
`schedBound A prm` slots and at most `oracleBound prm` oracles, and every
oracle tree has depth at most `maxLogLde`.
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind ZkFormal.Air

/-! ## Generic list lemmas -/

theorem foldr_max_le {l : List Nat} {M b : Nat} (hb : b ≤ M) (h : ∀ x ∈ l, x ≤ M) :
    l.foldr max b ≤ M := by
  induction l with
  | nil => exact hb
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (by simp), ih fun x hx => h x (by simp [hx])⟩

theorem le_foldr_max {l : List Nat} {b x : Nat} (hx : x ∈ l) : x ≤ l.foldr max b := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (k : Nat)
    (h : ∀ x ∈ l, (f x).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a (by simp)
    have h2 := ih fun x hx => h x (by simp [hx])
    omega

theorem log2_mono {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · subst ha; simp [Nat.log2_zero]
  · apply Nat.le_of_not_lt
    intro hlt
    have h1 : 2 ^ (b.log2 + 1) ≤ 2 ^ a.log2 := Nat.pow_le_pow_right (by decide) hlt
    have h2 := Nat.log2_self_le ha
    have h3 := @Nat.lt_log2_self b
    omega

theorem sum_filter_le {α : Type} (l : List α) (p : α → Bool) (g : α → Nat) :
    ((l.filter p).map g).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    split <;> simp <;> omega

theorem sum_zip_fst_le {α β : Type} (G : α → Nat) :
    ∀ (l : List α) (m : List β), ((l.zip m).map fun p => G p.1).sum ≤ (l.map G).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, _ :: m => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have := sum_zip_fst_le G l m
    omega

/-! ## Layout bounds -/

section
variable (A : Air) (prm : Params) (hdr : List Nat)

theorem lde_le_of_headerOk (h : headerOk A prm hdr = true) :
    ∀ L ∈ layout A prm hdr, L.lde ≤ prm.maxLogLde := by
  intro L hL
  simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := h
  simp only [layout, List.mem_map] at hL
  obtain ⟨⟨T, l⟩, hmem, rfl⟩ := hL
  exact (hall (T, l) hmem).1.2

theorem queryLog_le (h : headerOk A prm hdr = true) : queryLog A prm hdr ≤ prm.maxLogLde := by
  unfold queryLog
  apply foldr_max_le (Nat.zero_le _)
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨L, hL, rfl⟩ := hx
  exact lde_le_of_headerOk A prm hdr h L hL

theorem finalLayer_le_queryLog : finalLayer A prm hdr ≤ queryLog A prm hdr := by
  unfold finalLayer; omega

/-- DEEP-function count of a layout entry. -/
def colsOf (L : TLayout) : Nat := 2 * L.width + 2 * L.aux + L.quot

theorem layout_cols_le : ((layout A prm hdr).map colsOf).sum ≤ totalCols A prm := by
  unfold layout totalCols
  rw [List.map_map]
  exact sum_zip_fst_le (fun T : Air.Table =>
    2 * T.width + 2 * T.auxCount prm.auxGroup + T.quotCount prm.auxGroup) A.tables hdr

theorem classCount_le (m : Nat) : classCount (layout A prm hdr) m ≤ totalCols A prm := by
  unfold classCount
  exact Nat.le_trans (sum_filter_le _ _ colsOf) (layout_cols_le A prm hdr)

theorem batchRounds_le : batchRounds (layout A prm hdr) ≤ batchBound A prm := by
  unfold batchRounds batchBound
  simp only
  have hc : ((layout A prm hdr).map fun L => classCount (layout A prm hdr) L.lde).foldr max 2
      ≤ totalCols A prm + 2 := by
    apply foldr_max_le (by omega)
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨L, _, rfl⟩ := hx
    have := classCount_le A prm hdr L.lde
    omega
  have := log2_mono (a := 2 * ((layout A prm hdr).map fun L =>
    classCount (layout A prm hdr) L.lde).foldr max 2 - 1) (b := 2 * (totalCols A prm + 2)) (by omega)
  omega

/-! ## Schedule length -/

theorem friSchedule_length_le :
    (friSchedule A prm hdr).length ≤ 4 * finalLayer A prm hdr + 3 := by
  unfold friSchedule
  simp only [List.length_append, List.length_cons, List.length_nil]
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add (length_flatMap_le _ _ 4 ?_) (?_ : _ ≤ 2))
    (Nat.le_refl _)) ?_
  · intro i _
    simp only [List.length_append]
    cases rollInAt A prm hdr i <;> cases (friCommits A prm hdr).lookup i <;> simp
  · cases rollInAt A prm hdr (finalLayer A prm hdr) <;> simp
  · simp [List.length_range]; omega

theorem schedule_length_le (h : headerOk A prm hdr = true) :
    (schedule A prm hdr).length ≤ schedBound A prm := by
  unfold schedule schedBound
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h1 := length_flatMap_le (List.range (batchRounds (layout A prm hdr) - 1))
    (fun _ => [Slot.msg [], Slot.chal false]) 2 (by intro _ _; simp)
  rw [List.length_range] at h1
  have h2 := friSchedule_length_le A prm hdr
  have h3 := batchRounds_le A prm hdr
  have h4 := finalLayer_le_queryLog A prm hdr
  have h5 := queryLog_le A prm hdr h
  have : (batchRounds (layout A prm hdr) - 1) * 2 ≤ 2 * batchBound A prm := by omega
  have : 4 * finalLayer A prm hdr ≤ 4 * prm.maxLogLde := by omega
  omega

/-! ## Oracles -/

theorem schedOracles_append (a b : List Slot) :
    schedOracles (a ++ b) = schedOracles a ++ schedOracles b := by
  unfold schedOracles; exact List.flatMap_append

theorem schedOracles_schedule :
    schedOracles (schedule A prm hdr) =
      [(layout A prm hdr).map fun L => (L.lde, L.width),
       (layout A prm hdr).map fun L => (L.lde, 8 * L.aux),
       (layout A prm hdr).map fun L => (L.lde, 8 * L.quot)] ++
      schedOracles (friSchedule A prm hdr) := by
  unfold schedule
  rw [schedOracles_append, schedOracles_append]
  have hb : ∀ n, schedOracles
      (List.flatMap (fun _ => [Slot.msg [], Slot.chal false]) (List.range n)) = [] := by
    intro n; unfold schedOracles; rw [List.flatMap_assoc]; simp
  rw [hb, List.append_nil]
  rfl

/-- The FRI oracles: one per committed layer. -/
def friOracleAt (i : Nat) : List (List (Nat × Nat)) :=
  match (friCommits A prm hdr).lookup i with
  | some a => [[(queryLog A prm hdr - i - a, 8 * 2 ^ a)]]
  | none => []

theorem schedOracles_fri :
    schedOracles (friSchedule A prm hdr) =
      (List.range (finalLayer A prm hdr)).flatMap (friOracleAt A prm hdr) := by
  unfold friSchedule
  rw [schedOracles_append, schedOracles_append]
  have h1 : schedOracles (if rollInAt A prm hdr (finalLayer A prm hdr) = true
      then [Slot.msg [], Slot.chal false] else []) = [] := by
    cases rollInAt A prm hdr (finalLayer A prm hdr) <;> rfl
  rw [h1]
  have h2 : schedOracles [Slot.msg [.elems 2]] = [] := rfl
  rw [h2, List.append_nil, List.append_nil]
  unfold schedOracles
  rw [List.flatMap_assoc]
  congr 1
  funext i
  unfold friOracleAt
  cases rollInAt A prm hdr i <;> cases (friCommits A prm hdr).lookup i <;> rfl

theorem oracles_length_le (h : headerOk A prm hdr = true) :
    (schedOracles (schedule A prm hdr)).length ≤ oracleBound prm := by
  rw [schedOracles_schedule, schedOracles_fri]
  have := length_flatMap_le (List.range (finalLayer A prm hdr)) (friOracleAt A prm hdr) 1 (by
    intro i _; unfold friOracleAt; cases (friCommits A prm hdr).lookup i <;> simp)
  rw [List.length_range] at this
  have h4 := finalLayer_le_queryLog A prm hdr
  have h5 := queryLog_le A prm hdr h
  simp only [List.length_append, List.length_cons, List.length_nil, oracleBound]
  omega

theorem treeLog_le_of {o : List (Nat × Nat)} {M : Nat} (h : ∀ p ∈ o, p.1 ≤ M) : treeLog o ≤ M := by
  unfold treeLog
  apply foldr_max_le (Nat.zero_le _)
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact h p hp

theorem oracles_depth_le (h : headerOk A prm hdr = true) :
    ∀ o ∈ schedOracles (schedule A prm hdr), treeLog o ≤ prm.maxLogLde := by
  have hq := queryLog_le A prm hdr h
  have hl : ∀ L ∈ layout A prm hdr, L.lde ≤ queryLog A prm hdr := fun L hL =>
    le_foldr_max (List.mem_map.mpr ⟨L, hL, rfl⟩)
  intro o ho
  apply treeLog_le_of
  rw [schedOracles_schedule, schedOracles_fri] at ho
  simp only [List.cons_append, List.mem_cons, List.nil_append, List.mem_flatMap] at ho
  rcases ho with rfl | rfl | rfl | ⟨i, _, hi⟩
  · intro p hp; simp only [List.mem_map] at hp; obtain ⟨L, hL, rfl⟩ := hp
    exact Nat.le_trans (hl L hL) hq
  · intro p hp; simp only [List.mem_map] at hp; obtain ⟨L, hL, rfl⟩ := hp
    exact Nat.le_trans (hl L hL) hq
  · intro p hp; simp only [List.mem_map] at hp; obtain ⟨L, hL, rfl⟩ := hp
    exact Nat.le_trans (hl L hL) hq
  · unfold friOracleAt at hi
    cases hc : (friCommits A prm hdr).lookup i with
    | none => rw [hc] at hi; cases hi
    | some a =>
      rw [hc] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simp only
      omega

end

/-- **`NpBoundsStmt`**. -/
theorem np_bounds : NpBoundsStmt := by
  intro F K _ _ _ _ _ A prm
  exact ⟨fun hdr h => schedule_length_le A prm hdr (verifier_headerOk h).1,
    fun hdr h => oracles_length_le A prm hdr (verifier_headerOk h).1,
    fun hdr h => oracles_depth_le A prm hdr (verifier_headerOk h).1⟩

end ZkFormal.Stark
