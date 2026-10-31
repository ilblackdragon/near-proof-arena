import NearSpecV3.Wasm.FuelGeneral
/-!
# Every function `prepare` accepts passes the fuel certificate (`fuelCertified_true`)

`Wasm/FuelCert.lean` defines a decidable certificate check (`certOK` on the certificate
`buildCert` builds). Until 2026-10-31 the successor checker ran it before every VM call and reported
`out of domain (e.wasm-α): w.fuel_certificate` when a prepared function failed it. This module
proves that the check never fails:

* `certOK_of_static`: a function body that is well nested, whose nesting is `openAt` (`NestOK`),
  whose gas table charges every group before it runs (`WC`, O-W4), and whose free-instruction count
  is at most `2 · max_blocks_per_function + 1` (O-W3) passes `certOK`. These are the facts `FnOK`
  collects, at the canonical nesting `openAt` that `FuelGeneral.prepare_fnOK` uses.
* `prepCertOK_of_prepare`, `fuelCertified_true`: so every module `prepare` accepts passes, and
  `fuelCertified cfg code = true` for every `code`, for every configuration with
  `0 < regular_op_cost ≤ linear_op_base_cost` (PV86: 822,756 ≤ 26,328,192).

The certificate's parts are matched with the static facts one by one: `free` is the suffix count of
free instructions, `rest` is `req` (the costly instructions a non-charge point still owes its group),
the label stack is `labelsOf (openAt ·)`, and liveness is sound (every position the builder marks
live is `Live`) and closed under the successors `moveOK` checks (a fixpoint, reached within
`code.size + 1` passes).
-/
namespace NearSpecV3.Wasm.FuelCertOK
open NearSpecV3.Wasm

/-! ## Generic array facts -/

theorem bang_eq {α : Type} [Inhabited α] {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) :
    a[i]! = x := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, h]; rfl

theorem getD_of_some {α : Type} {a : Array α} {i : Nat} {x d : α} (h : a[i]? = some x) :
    a.getD i d = x := by
  rw [Array.getD_eq_getD_getElem?, h]; rfl

theorem getD_ge {α : Type} {a : Array α} {i : Nat} {d : α} (h : a.size ≤ i) : a.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

theorem lt_of_getD_true {a : Array Bool} {i : Nat} (h : a.getD i false = true) : i < a.size := by
  rcases Nat.lt_or_ge i a.size with hi | hi
  · exact hi
  · rw [getD_ge hi] at h; cases h

theorem getD_set_true (a : Array Bool) (q j : Nat) :
    (a.setIfInBounds q true).getD j false = (a.getD j false || (q = j ∧ q < a.size)) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : q = j
  · subst h1
    by_cases h2 : q < a.size
    · simp [h2]
    · simp [h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
  · simp [h1]

/-! ## `fillBack`: the `free` and `rest` passes -/

theorem fillBack_size (f : Nat → Array Nat → Nat) : ∀ (k : Nat) (a : Array Nat),
    (fillBack f k a).size = a.size
  | 0, _ => rfl
  | k + 1, a => by rw [fillBack, fillBack_size f k]; simp

theorem fillBack_spec (f : Nat → Array Nat → Nat) (n : Nat) (v : Nat → Nat)
    (hf : ∀ (j : Nat) (a : Array Nat), j < n → a[j + 1]? = some (v (j + 1)) → f j a = v j) :
    ∀ (k : Nat) (a : Array Nat), k ≤ n → a.size = n + 1 →
      (∀ j, k ≤ j → j ≤ n → a[j]? = some (v j)) → ∀ j, j ≤ n → (fillBack f k a)[j]? = some (v j)
  | 0, a, _, _, ha => fun j hj => by simpa [fillBack] using ha j (Nat.zero_le _) hj
  | k + 1, a, hk, hs, ha => by
    rw [fillBack]
    have hfk : f k a = v k := hf k a (by omega) (ha (k + 1) (Nat.le_refl _) hk)
    apply fillBack_spec f n v hf k _ (by omega) (by simp [hs])
    intro j h1 h2
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hjk : k = j
    · subst hjk
      have : k < a.size := by omega
      simp [this, hfk]
    · simp only [hjk, if_false]
      exact ha j (by omega) h2

/-- Free instructions at or after `j`. -/
def freeSuf (code : Array Instr) (j : Nat) : Nat := ((code.toList.drop j).map freeBit).sum

theorem freeSuf_succ (code : Array Instr) (j : Nat) (hj : j < code.size) :
    freeSuf code j = freeSuf code (j + 1) + freeBit code[j] := by
  unfold freeSuf
  rw [List.drop_eq_getElem_cons (by simpa using hj)]
  simp [Nat.add_comm]

theorem freeSuf_size (code : Array Instr) : freeSuf code code.size = 0 := by
  unfold freeSuf
  rw [List.drop_eq_nil_of_le (by simp)]
  rfl

theorem freeSuf_le (code : Array Instr) : ∀ j, j ≤ code.size → freeSuf code j ≤ freeSuf code 0
  | 0, _ => Nat.le_refl _
  | j + 1, h => by
    have := freeSuf_succ code j (by omega)
    have := freeSuf_le code j (by omega)
    omega

theorem freeSuf_zero (code : Array Instr) : freeSuf code 0 = freeCount code := by
  rw [FuelNest.freeCount_eq]
  simp only [freeSuf, List.drop_zero]
  rfl

theorem buildFree_get (code : Array Instr) (j : Nat) (hj : j ≤ code.size) :
    (buildFree code)[j]? = some (freeSuf code j) := by
  unfold buildFree
  apply fillBack_spec _ code.size (freeSuf code) _ code.size _ (Nat.le_refl _) (by simp)
  · intro i h1 h2
    have : i = code.size := by omega
    subst this
    simp [freeSuf_size]
  · exact hj
  · intro i a hi ha
    rw [bang_eq ha, bang_eq (Array.getElem?_eq_getElem hi), freeSuf_succ code i hi]

theorem buildFree_size (code : Array Instr) : (buildFree code).size = code.size + 1 := by
  simp [buildFree, fillBack_size]

theorem buildRest_get (pf : PFunc) (j : Nat) (hj : j ≤ pf.code.size) :
    (buildRest pf.code pf.gas)[j]? = some (req pf j) := by
  unfold buildRest
  apply fillBack_spec _ pf.code.size (req pf) _ pf.code.size _ (Nat.le_refl _) (by simp)
  · intro i h1 h2
    have : i = pf.code.size := by omega
    subst this
    simp [FuelGas.req_ge pf _ (Nat.le_refl _)]
  · exact hj
  · intro i a hi ha
    rw [FuelGas.req_lt pf i hi]
    have hc : pf.code[i]? = some pf.code[i] := Array.getElem?_eq_getElem hi
    rw [bang_eq ha, bang_eq hc]
    simp only [hc]
    cases pf.gas[i]? with
    | none => rfl
    | some o => cases o <;> rfl

theorem buildRest_size (pf : PFunc) : (buildRest pf.code pf.gas).size = pf.code.size + 1 := by
  simp [buildRest, fillBack_size]

/-! ## Labels: `buildLbl` is `labelsOf ∘ openAt` -/

/-- `lblFrom` without the accumulator. -/
def lblList (pf : PFunc) : Nat → List Instr → List (Nat × Bool) → List (List (Nat × Bool))
  | _, [], L => [L]
  | i, ins :: rest, L => L :: lblList pf (i + 1) rest (lblStep pf L i ins)

theorem lblFrom_toList (pf : PFunc) : ∀ (i : Nat) (l : List Instr) (L : List (Nat × Bool))
    (acc : Array (List (Nat × Bool))), (lblFrom pf i l L acc).toList = acc.toList ++ lblList pf i l L
  | _, [], L, acc => by simp [lblFrom, lblList]
  | i, ins :: rest, L, acc => by
    rw [lblFrom, lblFrom_toList pf (i + 1) rest, lblList]
    simp

theorem lblStep_labels (pf : PFunc) (os : List Nat) (i : Nat) (ins : Instr)
    (hc : pf.code[i]? = some ins) :
    lblStep pf (labelsOf pf os) i ins = labelsOf pf (openStep os i ins) := by
  cases ins
  case block => simp [lblStep, openStep, labelsOf, labOf, labTarget, endAt, hc, isLoopI]
  case loop => simp [lblStep, openStep, labelsOf, labOf, labTarget, hc, isLoopI]
  case if_ => simp [lblStep, openStep, labelsOf, labOf, labTarget, endAt, hc, isLoopI]
  case end_ =>
    cases os with
    | nil => rfl
    | cons o r =>
      cases r with
      | nil => rfl
      | cons o' r' => rfl
  all_goals rfl

theorem lblList_get (pf : PFunc) : ∀ (d i : Nat), i + d = pf.code.size → ∀ k, k ≤ d →
    (lblList pf i (pf.code.toList.drop i) (labelsOf pf (openAt pf.code i)))[k]? =
      some (labelsOf pf (openAt pf.code (i + k)))
  | 0, i, hd, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    rw [show pf.code.toList.drop i = [] by simp; omega]
    rfl
  | d + 1, i, hd, k, hk => by
    have hi : i < pf.code.size := by omega
    have hc : pf.code[i]? = some pf.code[i] := Array.getElem?_eq_getElem hi
    rw [List.drop_eq_getElem_cons (by simpa using hi), lblList]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.getElem?_cons_succ]
      rw [lblStep_labels pf _ i _ (by simpa using hc), ← FuelNest.openAt_succ_some (by simpa using hc),
        show i + (k + 1) = (i + 1) + k by omega]
      try simp only [Array.getElem_toList]
      exact lblList_get pf d (i + 1) (by omega) k (by omega)

theorem buildLbl_get (pf : PFunc) (k : Nat) (hk : k ≤ pf.code.size) :
    (buildLbl pf).getD k [] = labelsOf pf (openAt pf.code k) := by
  have h := lblList_get pf pf.code.size 0 (by omega) k hk
  simp only [Nat.zero_add, List.drop_zero] at h
  have h0 : labelsOf pf (openAt pf.code 0) = [(pf.code.size, false)] := rfl
  rw [h0] at h
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, buildLbl, lblFrom_toList]
  simp [h]

/-! ## Liveness: sizes, monotonicity, marking -/

theorem markAll_size : ∀ (a : Array Bool) (qs : List Nat), (markAll a qs).size = a.size
  | _, [] => rfl
  | a, q :: qs => by
    simp only [markAll, List.foldl_cons]
    have := markAll_size (a.setIfInBounds q true) qs
    simp only [markAll] at this
    rw [this]; simp

theorem markAll_getD : ∀ (a : Array Bool) (qs : List Nat) (j : Nat),
    (markAll a qs).getD j false = (a.getD j false || (j ∈ qs ∧ j < a.size))
  | a, [], j => by simp [markAll]
  | a, q :: qs, j => by
    have ih := markAll_getD (a.setIfInBounds q true) qs j
    simp only [markAll, List.foldl_cons] at ih ⊢
    rw [ih, getD_set_true, Array.size_setIfInBounds]
    by_cases h1 : a.getD j false = true
    · simp [h1]
    · by_cases h2 : q = j
      · subst h2; by_cases h3 : q < a.size <;> simp [h3]
      · simp [h1, h2, Ne.symm h2]

/-- One position's work in `liveRound`. -/
def rstep (pf : PFunc) (lbl : Array (List (Nat × Bool))) (a : Array Bool) (i : Nat) : Array Bool :=
  if a.getD i false then
    match pf.code[i]? with
    | some ins => markAll a (succsAt pf (lbl.getD i []) i ins)
    | none => a
  else a

theorem liveRound_eq (pf : PFunc) (lbl : Array (List (Nat × Bool))) (a : Array Bool) :
    liveRound pf lbl a = (List.range pf.code.size).foldl (rstep pf lbl) a := rfl

theorem rstep_size (pf : PFunc) (lbl) (a : Array Bool) (i : Nat) : (rstep pf lbl a i).size = a.size := by
  unfold rstep; split
  · split
    · exact markAll_size _ _
    · rfl
  · rfl

theorem rstep_mono (pf : PFunc) (lbl) (a : Array Bool) (i j : Nat) (h : a.getD j false = true) :
    (rstep pf lbl a i).getD j false = true := by
  unfold rstep; split
  · split
    · rw [markAll_getD, h]; rfl
    · exact h
  · exact h

theorem fold_size (pf : PFunc) (lbl) : ∀ (L : List Nat) (a : Array Bool),
    (L.foldl (rstep pf lbl) a).size = a.size
  | [], _ => rfl
  | x :: xs, a => by rw [List.foldl_cons, fold_size pf lbl xs, rstep_size]

theorem fold_mono (pf : PFunc) (lbl) : ∀ (L : List Nat) (a : Array Bool) (j : Nat),
    a.getD j false = true → (L.foldl (rstep pf lbl) a).getD j false = true
  | [], _, _, h => h
  | x :: xs, a, j, h => by rw [List.foldl_cons]; exact fold_mono pf lbl xs _ j (rstep_mono pf lbl a x j h)

theorem fold_mark (pf : PFunc) (lbl) {i : Nat} {ins : Instr} {q : Nat}
    (hc : pf.code[i]? = some ins) (hq : q ∈ succsAt pf (lbl.getD i []) i ins) :
    ∀ (L : List Nat) (a : Array Bool), i ∈ L → a.getD i false = true → q < a.size →
      (L.foldl (rstep pf lbl) a).getD q false = true
  | [], _, hi, _, _ => by cases hi
  | x :: xs, a, hi, ha, hqa => by
    rw [List.foldl_cons]
    by_cases hx : x = i
    · subst hx
      apply fold_mono
      simp only [rstep, ha, if_true, hc]
      rw [markAll_getD]
      simp only [hq, hqa, and_self, decide_true, Bool.or_true]
    · have hi' : i ∈ xs := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hx
        · exact h
      exact fold_mark pf lbl hc hq xs _ hi' (rstep_mono pf lbl a x i ha) (by rw [rstep_size]; exact hqa)

theorem fold_inv (pf : PFunc) (lbl) (P : Nat → Prop)
    (hP : ∀ i ins q, P i → pf.code[i]? = some ins → q ∈ succsAt pf (lbl.getD i []) i ins → P q) :
    ∀ (L : List Nat) (a : Array Bool), (∀ j, a.getD j false = true → P j) →
      ∀ j, (L.foldl (rstep pf lbl) a).getD j false = true → P j
  | [], _, ha => ha
  | x :: xs, a, ha => by
    rw [List.foldl_cons]
    apply fold_inv pf lbl P hP xs
    intro j hj
    unfold rstep at hj
    by_cases hx : a.getD x false = true
    · rw [if_pos hx] at hj
      cases hc : pf.code[x]? with
      | none => rw [hc] at hj; exact ha j hj
      | some ins =>
        rw [hc] at hj
        simp only at hj
        rw [markAll_getD] at hj
        rcases Bool.or_eq_true_iff.mp hj with h | h
        · exact ha j h
        · simp only [decide_eq_true_eq] at h
          exact hP x ins j (ha x hx) hc h.1
    · rw [if_neg hx] at hj; exact ha j hj

/-! ## Liveness: the fixpoint is reached -/

def cnt (a : Array Bool) : Nat := a.toList.count true

theorem count_le_of_le : ∀ (l1 l2 : List Bool), l1.length = l2.length →
    (∀ j : Nat, l1[j]? = some true → l2[j]? = some true) → l1.count true ≤ l2.count true
  | [], [], _, _ => Nat.le_refl _
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hl, h => by
    have ih := count_le_of_le xs ys (by simpa using hl) (fun j hj => by simpa using h (j + 1) (by simpa using hj))
    have h0 := h 0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    cases x <;> cases y <;> simp_all [List.count_cons] <;> omega

theorem count_lt_of_le : ∀ (l1 l2 : List Bool), l1.length = l2.length →
    (∀ j : Nat, l1[j]? = some true → l2[j]? = some true) → l1 ≠ l2 → l1.count true < l2.count true
  | [], [], _, _, hne => absurd rfl hne
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, hl, h, hne => by
    have hl' : xs.length = ys.length := by simpa using hl
    have ht : ∀ j : Nat, xs[j]? = some true → ys[j]? = some true :=
      fun j hj => by simpa using h (j + 1) (by simpa using hj)
    have h0 := h 0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    by_cases hxy : x = y
    · subst hxy
      have hne' : xs ≠ ys := fun e => hne (by rw [e])
      have := count_lt_of_le xs ys hl' ht hne'
      cases x <;> simp [List.count_cons] <;> omega
    · have := count_le_of_le xs ys hl' ht
      cases x <;> cases y <;> simp_all [List.count_cons] <;> omega

theorem cnt_lt (a b : Array Bool) (hs : a.size = b.size)
    (h : ∀ j, a.getD j false = true → b.getD j false = true) (hne : b ≠ a) : cnt a < cnt b := by
  unfold cnt
  apply count_lt_of_le _ _ (by simpa using hs)
  · intro j hj
    have hj' : a.getD j false = true := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hj]; rfl
    have := h j hj'
    have hlt := lt_of_getD_true this
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hlt]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt] at this
    simpa using this
  · intro e
    apply hne
    exact (Array.toList_inj.mp e).symm

theorem cnt_le (a : Array Bool) : cnt a ≤ a.size := by
  unfold cnt
  have := List.count_le_length (a := true) (l := a.toList)
  simpa using this

theorem liveIter_size (pf : PFunc) (lbl) : ∀ (k : Nat) (a : Array Bool), (liveIter pf lbl k a).size = a.size
  | 0, _ => rfl
  | k + 1, a => by
    simp only [liveIter]
    split
    · rfl
    · rw [liveIter_size pf lbl k, liveRound_eq, fold_size]

theorem liveIter_fix (pf : PFunc) (lbl) : ∀ (k : Nat) (a : Array Bool), a.size < cnt a + k →
    liveRound pf lbl (liveIter pf lbl k a) = liveIter pf lbl k a
  | 0, a, h => absurd h (by have := cnt_le a; omega)
  | k + 1, a, h => by
    simp only [liveIter]
    by_cases hb : liveRound pf lbl a = a
    · rw [if_pos hb]; exact hb
    · rw [if_neg hb]
      apply liveIter_fix pf lbl k
      have hs : (liveRound pf lbl a).size = a.size := by rw [liveRound_eq, fold_size]
      have := cnt_lt a (liveRound pf lbl a) hs.symm
        (fun j hj => by rw [liveRound_eq]; exact fold_mono pf lbl _ a j hj) hb
      omega

theorem liveIter_mono (pf : PFunc) (lbl) : ∀ (k : Nat) (a : Array Bool) (j : Nat),
    a.getD j false = true → (liveIter pf lbl k a).getD j false = true
  | 0, _, _, h => h
  | k + 1, a, j, h => by
    simp only [liveIter]
    split
    · exact h
    · exact liveIter_mono pf lbl k _ j (by rw [liveRound_eq]; exact fold_mono pf lbl _ a j h)

theorem liveIter_inv (pf : PFunc) (lbl) (P : Nat → Prop)
    (hP : ∀ i ins q, P i → pf.code[i]? = some ins → q ∈ succsAt pf (lbl.getD i []) i ins → P q) :
    ∀ (k : Nat) (a : Array Bool), (∀ j, a.getD j false = true → P j) →
      ∀ j, (liveIter pf lbl k a).getD j false = true → P j
  | 0, _, ha => ha
  | k + 1, a, ha => by
    simp only [liveIter]
    split
    · exact ha
    · exact liveIter_inv pf lbl P hP k _ (by rw [liveRound_eq]; exact fold_inv pf lbl P hP _ a ha)

def live0 (n : Nat) : Array Bool := (Array.replicate n false).setIfInBounds 0 true

theorem live0_getD (n j : Nat) : (live0 n).getD j false = true ↔ j = 0 ∧ 0 < n := by
  unfold live0
  rw [getD_set_true]
  simp only [Array.size_replicate, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exfalso
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
      split at h <;> simp at h
    · exact ⟨h1.symm, h2⟩
  · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1.symm, h2⟩

theorem buildLive_size (pf : PFunc) (lbl) : (buildLive pf lbl).size = pf.code.size := by
  simp [buildLive, liveIter_size]

/-- A position the builder marks live is a code position. -/
theorem buildLive_lt (pf : PFunc) (lbl) (j : Nat) (h : (buildLive pf lbl).getD j false = true) :
    j < pf.code.size := by
  have := lt_of_getD_true h
  rwa [buildLive_size] at this

theorem buildLive_fix (pf : PFunc) (lbl) :
    liveRound pf lbl (buildLive pf lbl) = buildLive pf lbl := by
  unfold buildLive
  apply liveIter_fix
  have : (live0 pf.code.size).size = pf.code.size := by simp [live0]
  unfold live0 at this
  omega

theorem buildLive_closed (pf : PFunc) (lbl) {i : Nat} {ins : Instr} {q : Nat}
    (hl : (buildLive pf lbl).getD i false = true) (hc : pf.code[i]? = some ins)
    (hq : q ∈ succsAt pf (lbl.getD i []) i ins) (hqn : q < pf.code.size) :
    (buildLive pf lbl).getD q false = true := by
  rw [← buildLive_fix, liveRound_eq]
  apply fold_mark pf lbl hc hq _ _ _ hl (by rw [buildLive_size]; exact hqn)
  exact List.mem_range.mpr (FuelGas.lt_of_get pf.code i ins hc)

theorem buildLive_inv (pf : PFunc) (lbl) (P : Nat → Prop) (h0 : 0 < pf.code.size → P 0)
    (hP : ∀ i ins q, P i → pf.code[i]? = some ins → q ∈ succsAt pf (lbl.getD i []) i ins → P q)
    (j : Nat) (h : (buildLive pf lbl).getD j false = true) : P j := by
  apply liveIter_inv pf lbl P hP _ _ _ j h
  intro j hj
  obtain ⟨rfl, hn⟩ := (live0_getD _ _).mp hj
  exact h0 hn

theorem buildLive_zero (pf : PFunc) (lbl) (hn : 0 < pf.code.size) :
    (buildLive pf lbl).getD 0 false = true :=
  liveIter_mono pf lbl _ _ 0 ((live0_getD _ _).mpr ⟨rfl, hn⟩)

/-! ## The last instruction is the function's own `end` -/

theorem nestScan_tail {i : Instr} {t : List Instr} {st : List Bool} (h : nestScan (i :: t) st = true)
    (ht : t ≠ []) : nestScan t (FuelNest.bStep st i) = true := by
  cases i <;> simp only [nestScan, FuelNest.bStep] at h ⊢ <;> try exact h
  · match st, h with
    | true :: _, h => exact h
    | false :: _, h => simp at h
    | [], h => simp at h
  · match st, h with
    | [], h => exact absurd (List.isEmpty_iff.mp h) ht
    | _ :: _, h => exact h

theorem nestScan_last : ∀ (l : List Instr) (st : List Bool), nestScan l st = true →
    l.getLast? = some .end_ ∧ l.dropLast.foldl FuelNest.bStep st = []
  | [], _, h => by simp [nestScan] at h
  | [i], st, h => by
    cases i <;> simp only [nestScan] at h <;> (try simp [nestScan] at h)
    · match st, h with
      | true :: _, h => simp [nestScan] at h
      | false :: _, h => simp at h
      | [], h => simp at h
    · match st, h with
      | [], _ => exact ⟨rfl, rfl⟩
      | _ :: _, h => simp [nestScan] at h
  | i :: j :: rest, st, h => by
    obtain ⟨h1, h2⟩ := nestScan_last (j :: rest) _ (nestScan_tail h (by simp))
    refine ⟨by simpa using h1, ?_⟩
    rw [List.dropLast_cons_of_ne_nil (by simp), List.foldl_cons]
    exact h2

theorem last_end (code : Array Instr) (hw : WellNested code) :
    0 < code.size ∧ code[code.size - 1]? = some .end_ ∧ openAt code (code.size - 1) = [] := by
  obtain ⟨h1, h2⟩ := nestScan_last code.toList [] hw
  have hpos : 0 < code.size := by
    rcases Nat.eq_zero_or_pos code.size with h | h
    · have : code.toList = [] := by simpa using h
      rw [this] at h1; cases h1
    · exact h
  refine ⟨hpos, ?_, ?_⟩
  · rw [List.getLast?_eq_getElem?] at h1
    simpa using h1
  · have hb : FuelNest.bAt code (code.size - 1) = [] := by
      unfold FuelNest.bAt
      rw [show code.toList.take (code.size - 1) = code.toList.dropLast by
        rw [List.dropLast_eq_take]; simp]
      exact h2
    have := (FuelNest.invS_all hw (code.size - 1)).stack.length
    rw [hb] at this
    exact List.eq_nil_of_length_eq_zero this.symm

/-! ## Successor targets are `Succ` edges inside the code -/

section edges
variable {pf : PFunc}

theorem labelsOf_get (os : List Nat) (l : Nat) (hl : l < os.length) :
    (labelsOf pf os)[l]? = some (labOf pf os[l]) := by
  unfold labelsOf
  rw [List.getElem?_append_left (by simpa using hl)]
  simp [hl]

theorem brT_spec {os : List Nat} {l q : Nat} (h : q ∈ brT (labelsOf pf os) l) :
    ∃ (hl : l < os.length), q = labTarget pf os[l] := by
  unfold brT at h
  rw [FuelGen.labelsOf_length] at h
  split at h
  · rename_i hlt
    have hl : l < os.length := by omega
    rw [labelsOf_get os l hl] at h
    simp only [labOf, List.mem_singleton] at h
    exact ⟨hl, h⟩
  · cases h

theorem brT_succ (hn : NestOK pf (openAt pf.code)) {i l q : Nat}
    (h : q ∈ brT (labelsOf pf (openAt pf.code i)) l) :
    brTarget pf (openAt pf.code) i l = some q := by
  obtain ⟨hl, rfl⟩ := brT_spec h
  simp [brTarget, List.getElem?_eq_getElem hl]

/-- Every jump `jumpsAt` lists is a static jump edge. -/
theorem jumps_edge (hn : NestOK pf (openAt pf.code)) {i q : Nat} {ins : Instr}
    (hc : pf.code[i]? = some ins) (hq : q ∈ jumpsAt pf (labelsOf pf (openAt pf.code i)) i ins) :
    Succ pf (openAt pf.code) i q true := by
  cases ins <;> simp only [jumpsAt] at hq <;> try (simp at hq; done)
  case if_ bt =>
    obtain ⟨he, -, -, -, -⟩ := hn.opener i _ hc rfl
    obtain ⟨hel, -⟩ := hn.if_ i bt hc
    rw [he, hel] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    by_cases h : elseAt pf i = endAt pf i
    · simp only [h, ne_eq, not_true_eq_false, if_false]
      exact Succ.ifEnd i bt hc h
    · simp only [h, ne_eq, not_false_eq_true, if_true]
      exact Succ.ifElse i bt hc h
  case else_ =>
    obtain ⟨o, rest, bt, henc, ho, -, -, -⟩ := hn.else_ i hc
    rw [henc, FuelGen.labelsOf_cons] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    have : labOf pf o = (endAt pf o + 1, false) := by simp [labOf, labTarget, ho, isLoopI]
    rw [this]
    exact Succ.else_ i o rest hc henc
  case br l => exact Succ.br i l q hc (brT_succ hn hq)
  case brIf l => exact Succ.brIf i l q hc (brT_succ hn hq)
  case brTable ls d =>
    obtain ⟨l, hl, hq⟩ := List.mem_flatMap.mp hq
    refine Succ.brTable i ls d l q hc ?_ (brT_succ hn hq)
    rcases List.mem_append.mp hl with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

/-- Every successor `succsAt` lists is a static control edge. -/
theorem succs_edge (hn : NestOK pf (openAt pf.code)) {i q : Nat} {ins : Instr}
    (hc : pf.code[i]? = some ins) (hq : q ∈ succsAt pf (labelsOf pf (openAt pf.code i)) i ins) :
    ∃ j, Succ pf (openAt pf.code) i q j := by
  unfold succsAt at hq
  have hq0 := List.mem_append.mp hq
  clear hq
  rcases hq0 with hq | hq
  · split at hq
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
      obtain ⟨hft, hend⟩ := hcond
      rw [List.mem_singleton] at hq
      subst hq
      refine ⟨false, Succ.fall i ins hc hft fun he => ?_⟩
      subst he
      rcases hend with h | h
      · simp [isEndI] at h
      · intro hnil
        rw [hnil] at h
        simp [labelsOf] at h
    · cases hq
  · exact ⟨true, jumps_edge hn hc hq⟩

theorem labTarget_lt (hw : WellNested pf.code) (hn : NestOK pf (openAt pf.code)) {o : Nat}
    (ho : pf.code[o]?.map isOpener = some true) : labTarget pf o < pf.code.size := by
  obtain ⟨hpos, hlast, hnil⟩ := last_end pf.code hw
  cases hco : pf.code[o]? with
  | none => rw [hco] at ho; cases ho
  | some io =>
    rw [hco] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    obtain ⟨-, hoe, hce, -, henc⟩ := hn.opener o io hco ho
    have hel := FuelGas.lt_of_get pf.code _ _ hce
    have hne : endAt pf o ≠ pf.code.size - 1 := by
      intro h; rw [h, hnil] at henc; cases henc
    cases io <;> simp only [isOpener] at ho <;> simp [labTarget, hco] <;> omega

/-- Every successor `succsAt` lists is a code position. -/
theorem succs_lt (hw : WellNested pf.code) (hn : NestOK pf (openAt pf.code)) {i q : Nat} {ins : Instr}
    (hc : pf.code[i]? = some ins) (hq : q ∈ succsAt pf (labelsOf pf (openAt pf.code i)) i ins) :
    q < pf.code.size := by
  obtain ⟨hpos, hlast, hnil⟩ := last_end pf.code hw
  have hi := FuelGas.lt_of_get pf.code i ins hc
  unfold succsAt at hq
  have hq0 := List.mem_append.mp hq
  clear hq
  rcases hq0 with hq | hq
  · split at hq
    · rename_i hcond
      rw [List.mem_singleton] at hq
      subst hq
      refine Nat.lt_of_not_le fun hge => ?_
      have hi' : i = pf.code.size - 1 := by omega
      subst hi'
      rw [hlast] at hc
      cases hc
      simp [isEndI, hnil, labelsOf] at hcond
    · cases hq
  · have hbr : ∀ l, q ∈ brT (labelsOf pf (openAt pf.code i)) l → q < pf.code.size := by
      intro l h
      obtain ⟨hl, rfl⟩ := brT_spec h
      have hd : (openAt pf.code i).drop l = (openAt pf.code i)[l] :: (openAt pf.code i).drop (l + 1) :=
        List.drop_eq_getElem_cons hl
      obtain ⟨-, -, ho⟩ := FuelGen.nest_drop hn l i _ _ hi hd
      exact labTarget_lt hw hn ho
    cases ins <;> simp only [jumpsAt] at hq <;> try (simp at hq; done)
    case if_ bt =>
      obtain ⟨he, hlt, hce, -, -⟩ := hn.opener i _ hc rfl
      obtain ⟨hel, hif⟩ := hn.if_ i bt hc
      rw [he, hel] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      have := labTarget_lt hw hn (o := i) (by simp [hc, isOpener])
      simp only [labTarget, hc] at this
      by_cases h : elseAt pf i = endAt pf i
      · simp only [h, ne_eq, not_true_eq_false, if_false]; exact this
      · simp only [h, ne_eq, not_false_eq_true, if_true]
        rcases hif with h' | ⟨_, h2, _⟩
        · exact absurd h' h
        · omega
    case else_ =>
      obtain ⟨o, rest, bt, henc, ho, -, -, -⟩ := hn.else_ i hc
      rw [henc, FuelGen.labelsOf_cons] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact labTarget_lt hw hn (o := o) (by simp [ho, isOpener])
    case br => exact hbr _ hq
    case brIf => exact hbr _ hq
    case brTable =>
      obtain ⟨l, _, hq⟩ := List.mem_flatMap.mp hq
      exact hbr l hq

end edges

/-! ## The certificate check passes -/

section main
variable {cfg : NearCfg} {pf : PFunc}

theorem cert_lb (k : Nat) (hk : k ≤ pf.code.size) :
    (buildCert cfg pf).lb k = labelsOf pf (openAt pf.code k) := buildLbl_get pf k hk

theorem cert_r (k : Nat) : (buildCert cfg pf).r k = req pf k := by
  show (buildRest pf.code pf.gas).getD k 0 = req pf k
  rcases Nat.lt_or_ge pf.code.size k with h | h
  · rw [getD_ge (by rw [buildRest_size]; omega), FuelGas.req_ge pf k (by omega)]
  · exact getD_of_some (buildRest_get pf k h)

theorem cert_fr (k : Nat) (hk : k ≤ pf.code.size) : (buildCert cfg pf).fr k = freeSuf pf.code k :=
  getD_of_some (buildFree_get pf.code k hk)

theorem cert_lv_def (k : Nat) : (buildCert cfg pf).lv k = (buildLive pf (buildLbl pf)).getD k false := rfl

theorem cert_lbl_getD (k : Nat) : (buildLbl pf).getD k [] = (buildCert cfg pf).lb k := rfl

/-- The builder's liveness is sound: a live position is `Live`. -/
theorem cert_live (hn : NestOK pf (openAt pf.code)) (k : Nat) (h : (buildCert cfg pf).lv k = true) :
    Live pf (openAt pf.code) k := by
  rw [cert_lv_def] at h
  refine buildLive_inv pf _ (fun k => Live pf (openAt pf.code) k) (fun _ => Live.entry) ?_ k h
  intro i ins q hi hc hq
  have hilt := FuelGas.lt_of_get pf.code i ins hc
  rw [buildLbl_get pf i (by omega)] at hq
  obtain ⟨j, hs⟩ := succs_edge hn hc hq
  exact Live.step i q j hi hs

theorem labelsOf_drop (os : List Nat) (l : Nat) (hl : l ≤ os.length) :
    (labelsOf pf os).drop l = labelsOf pf (os.drop l) := by
  unfold labelsOf
  rw [List.drop_append_of_le_length (by simpa using hl), List.map_drop]

theorem labOf_if {o : Nat} {bt : BT} (ho : pf.code[o]? = some (.if_ bt)) :
    labOf pf o = (endAt pf o + 1, false) := by simp [labOf, labTarget, ho, isLoopI]

/-- The builder's liveness is closed under the successors `moveOK` checks. -/
theorem cert_closed (hw : WellNested pf.code) (hn : NestOK pf (openAt pf.code)) {i q : Nat}
    {ins : Instr} (hl : (buildCert cfg pf).lv i = true) (hc : pf.code[i]? = some ins)
    (hq : q ∈ succsAt pf (labelsOf pf (openAt pf.code i)) i ins) : (buildCert cfg pf).lv q = true := by
  have hi := FuelGas.lt_of_get pf.code i ins hc
  rw [cert_lv_def] at hl ⊢
  apply buildLive_closed pf _ hl hc _ (succs_lt hw hn hc hq)
  rw [buildLbl_get pf i (by omega)]; exact hq

theorem fall_mem {os : List Nat} {i : Nat} {ins : Instr} (h1 : fallsThrough ins = true)
    (h2 : isEndI ins = false ∨ 2 ≤ (labelsOf pf os).length) : i + 1 ∈ succsAt pf (labelsOf pf os) i ins := by
  unfold succsAt
  apply List.mem_append_left
  rw [if_pos]
  · exact List.mem_singleton_self _
  · simp only [h1, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    exact h2

theorem moveOK_ok (hw : WellNested pf.code) (hn : NestOK pf (openAt pf.code))
    (hwc : WC cfg pf (openAt pf.code)) {i : Nat} {ins : Instr}
    (hl : (buildCert cfg pf).lv i = true) (hc : pf.code[i]? = some ins) :
    moveOK (buildCert cfg pf) pf i ins = true := by
  have hi := FuelGas.lt_of_get pf.code i ins hc
  have hlive := cert_live hn i hl
  have hlbi : (buildCert cfg pf).lb i = labelsOf pf (openAt pf.code i) := cert_lb i (by omega)
  have hft : ∀ L, fallsThrough ins = true →
      (isEndI ins = false ∨ 2 ≤ (labelsOf pf (openAt pf.code i)).length) →
      labelsOf pf (openAt pf.code (i + 1)) = L → ftOK (buildCert cfg pf) i L = true := by
    intro L h1 h2 h3
    have hq := fall_mem (i := i) h1 h2
    have hlt := succs_lt hw hn hc hq
    unfold ftOK
    rw [cert_closed hw hn hl hc hq, cert_lb (i + 1) (by omega), h3]
    simp
  have hjump : ∀ t L, t ∈ jumpsAt pf (labelsOf pf (openAt pf.code i)) i ins →
      labelsOf pf (openAt pf.code t) = L → jumpOK (buildCert cfg pf) t L = true := by
    intro t L ht hL
    have hq : t ∈ succsAt pf (labelsOf pf (openAt pf.code i)) i ins := List.mem_append_right _ ht
    have hlt := succs_lt hw hn hc hq
    unfold jumpOK
    rw [cert_closed hw hn hl hc hq, cert_r, hwc.jump i t hlive (jumps_edge hn hc ht),
      cert_lb t (by omega), hL]
    simp
  have hother : isOpener ins = false → ins ≠ .else_ → ins ≠ .end_ → fallsThrough ins = true →
      ftOK (buildCert cfg pf) i ((buildCert cfg pf).lb i) = true := by
    intro h1 h2 h3 h4
    apply hft _ h4 (Or.inl (by cases ins <;> simp_all [isEndI]))
    rw [hlbi, hn.other i ins hc h1 h2 h3]
  have hbr : ∀ l, (∀ q ∈ brT (labelsOf pf (openAt pf.code i)) l,
      q ∈ jumpsAt pf (labelsOf pf (openAt pf.code i)) i ins) → brOK (buildCert cfg pf) i l = true := by
    intro l hsub
    unfold brOK
    rw [hlbi]
    split
    · rfl
    · rename_i hge
      rw [FuelGen.labelsOf_length] at hge
      have hlt : l < (openAt pf.code i).length := by omega
      rw [labelsOf_get _ l hlt]
      simp only [labOf]
      have hd : (openAt pf.code i).drop l = (openAt pf.code i)[l] :: (openAt pf.code i).drop (l + 1) :=
        List.drop_eq_getElem_cons hlt
      obtain ⟨-, hoenc, hop⟩ := FuelGen.nest_drop hn l i _ _ hi hd
      obtain ⟨o, ho⟩ : ∃ o, (openAt pf.code i)[l] = o := ⟨_, rfl⟩
      rw [ho] at hd hoenc hop
      rw [ho]
      have hmem : labTarget pf o ∈ brT (labelsOf pf (openAt pf.code i)) l := by
        unfold brT
        rw [FuelGen.labelsOf_length, if_pos (by omega), labelsOf_get _ l hlt, ho]
        simp [labOf]
      apply hjump _ _ (hsub _ hmem)
      obtain ⟨io, hco⟩ : ∃ io, pf.code[o]? = some io := by
        cases h : pf.code[o]? with
        | none => rw [h] at hop; cases hop
        | some io => exact ⟨io, rfl⟩
      rw [hco] at hop
      simp only [Option.map_some, Option.some.injEq] at hop
      obtain ⟨-, -, hce, henc1, henc2⟩ := hn.opener o io hco hop
      simp only [labTarget, hco, Option.map_some, Option.getD_some]
      cases io <;> simp [isOpener] at hop
      case loop bt =>
        simp only [isLoopI, if_true]
        rw [henc1, hoenc, ← hd, labelsOf_drop _ _ (by omega)]
      case block bt =>
        simp only [isLoopI, Bool.false_eq_true, if_false]
        rw [((hn.end_ _ hce).2 o (openAt pf.code o) henc2).2, hoenc, labelsOf_drop _ _ (by omega)]
      case if_ bt =>
        simp only [isLoopI, Bool.false_eq_true, if_false]
        rw [((hn.end_ _ hce).2 o (openAt pf.code o) henc2).2, hoenc, labelsOf_drop _ _ (by omega)]
  cases ins
  case block bt =>
    obtain ⟨he, -, -, henc1, -⟩ := hn.opener i _ hc rfl
    simp only [moveOK, he]
    apply hft _ rfl (Or.inl rfl)
    rw [henc1, FuelGen.labelsOf_cons, hlbi]
    simp [labOf, labTarget, hc, isLoopI]
  case loop bt =>
    obtain ⟨-, -, -, henc1, -⟩ := hn.opener i _ hc rfl
    simp only [moveOK]
    apply hft _ rfl (Or.inl rfl)
    rw [henc1, FuelGen.labelsOf_cons, hlbi]
    simp [labOf, labTarget, hc, isLoopI]
  case if_ bt =>
    obtain ⟨he, -, hce, henc1, henc2⟩ := hn.opener i _ hc rfl
    obtain ⟨hel, hif⟩ := hn.if_ i bt hc
    simp only [moveOK, he, hel, Bool.and_eq_true]
    have hlab : labOf pf i = (endAt pf i + 1, false) := labOf_if hc
    refine ⟨?_, ?_⟩
    · apply hft _ rfl (Or.inl rfl)
      rw [henc1, FuelGen.labelsOf_cons, hlbi, hlab]
    · have hmem : (if elseAt pf i ≠ endAt pf i then elseAt pf i + 1 else endAt pf i + 1) ∈
          jumpsAt pf (labelsOf pf (openAt pf.code i)) i (.if_ bt) := by
        simp only [jumpsAt, he, hel]; exact List.mem_singleton_self _
      by_cases h : elseAt pf i = endAt pf i
      · simp only [h, ne_eq, not_true_eq_false, if_false] at hmem ⊢
        apply hjump _ _ hmem
        rw [((hn.end_ _ hce).2 i (openAt pf.code i) henc2).2, hlbi]
      · simp only [h, ne_eq, not_false_eq_true, if_true] at hmem ⊢
        apply hjump _ _ hmem
        rcases hif with h' | ⟨-, -, -, h4⟩
        · exact absurd h' h
        · rw [h4, FuelGen.labelsOf_cons, hlbi, hlab]
  case else_ =>
    obtain ⟨o, rest, bt, henc, ho, -, hlt, -⟩ := hn.else_ i hc
    obtain ⟨-, hoenc, -⟩ := hn.chain i o rest hi henc
    obtain ⟨-, -, hce, -, henc2⟩ := hn.opener o _ ho rfl
    have hmem : endAt pf o + 1 ∈ jumpsAt pf (labelsOf pf (openAt pf.code i)) i .else_ := by
      simp only [jumpsAt, henc, FuelGen.labelsOf_cons, labOf_if ho]; exact List.mem_singleton_self _
    simp only [moveOK]
    rw [hlbi, henc, FuelGen.labelsOf_cons, labOf_if ho]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, hjump _ _ hmem ?_⟩
    rw [((hn.end_ _ hce).2 o (openAt pf.code o) henc2).2, hoenc]
  case end_ =>
    simp only [moveOK]
    rw [hlbi]
    cases henc : openAt pf.code i with
    | nil => rfl
    | cons o rest =>
      have hnext := ((hn.end_ i hc).2 o rest henc).2
      have h2 : 2 ≤ (labelsOf pf (openAt pf.code i)).length := by
        rw [FuelGen.labelsOf_length, henc]; simp
      have hf := hft (labelsOf pf rest) rfl (Or.inr h2) (by rw [hnext])
      cases rest with
      | nil => exact hf
      | cons o' r' => exact hf
  case br l =>
    simp only [moveOK]
    exact hbr l (fun q hq => by simpa [jumpsAt] using hq)
  case brIf l =>
    simp only [moveOK, Bool.and_eq_true]
    refine ⟨hbr l (fun q hq => by simpa [jumpsAt] using hq), ?_⟩
    apply hft _ rfl (Or.inl rfl)
    rw [hlbi, hn.other i _ hc rfl (by simp) (by simp)]
  case brTable ls d =>
    simp only [moveOK, List.all_eq_true]
    intro l hl
    exact hbr l (fun q hq => by
      simp only [jumpsAt]
      exact List.mem_flatMap.mpr ⟨l, hl, hq⟩)
  case ret => rfl
  case unreachable => rfl
  all_goals (simp only [moveOK]; exact hother rfl (by simp) (by simp) rfl)

theorem pcOK_ok (hw : WellNested pf.code) (hn : NestOK pf (openAt pf.code))
    (hwc : WC cfg pf (openAt pf.code)) (i : Nat) (hi : i < pf.code.size) :
    pcOK cfg pf (buildCert cfg pf) i = true := by
  have hc : pf.code[i]? = some pf.code[i] := Array.getElem?_eq_getElem hi
  unfold pcOK
  rw [hc]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · rw [cert_fr i (by omega), cert_fr (i + 1) (by omega), freeSuf_succ pf.code i hi]
    exact Nat.le_refl _
  · by_cases hl : (buildCert cfg pf).lv i = true
    · right
      refine ⟨moveOK_ok hw hn hwc hl hc, ?_⟩
      have hgr : grp (buildCert cfg pf) i pf.code[i] =
          costOf pf.code[i] + (if fallsThrough pf.code[i] then req pf (i + 1) else 0) := by
        simp only [grp, cert_r]; rfl
      cases hg : pf.gas[i]? with
      | none => rfl
      | some o =>
        cases o with
        | none =>
          simp only [decide_eq_true_eq]
          rw [hgr, cert_r, FuelGas.req_cons pf i _ hc (by intro e he; rw [hg] at he; cases he)]
          exact Nat.le_refl _
        | some kf =>
          obtain ⟨k, fee⟩ := kf
          simp only [decide_eq_true_eq]
          rw [hgr]
          exact hwc.charged i _ k fee (cert_live hn i hl) hc hg
    · left; simpa using hl

/-- **`FnOK` → `certOK`.** A body with the static fuel facts (at the canonical nesting `openAt`,
as `FuelGeneral.prepare_fnOK` produces them) passes the certificate check. -/
theorem certOK_of_static (cfg : NearCfg) (pf : PFunc) (hw : WellNested pf.code)
    (hn : NestOK pf (openAt pf.code)) (hwc : WC cfg pf (openAt pf.code))
    (hfree : freeCount pf.code ≤ 2 * cfg.maxBlocksPerFunction + 1) :
    certOK cfg pf (buildCert cfg pf) = true := by
  obtain ⟨hpos, -, -⟩ := last_end pf.code hw
  unfold certOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fun i hi => pcOK_ok hw hn hwc i hi⟩
  · rw [cert_lv_def]; exact buildLive_zero pf _ hpos
  · rw [cert_r]; exact hwc.entry
  · rw [cert_lb 0 (Nat.zero_le _)]; rfl
  · show (buildFree pf.code).size ≤ _
    rw [buildFree_size]
    exact Nat.le_refl _
  · intro j hj
    have hj' : j < (buildFree pf.code).size := hj
    have hs := buildFree_size pf.code
    show (buildFree pf.code)[j] ≤ _
    have h := buildFree_get pf.code j (by omega)
    rw [Array.getElem?_eq_getElem hj', Option.some.injEq] at h
    rw [h]
    exact Nat.le_trans (freeSuf_le pf.code j (by omega)) (by rw [freeSuf_zero]; exact hfree)

end main

/-- Every module `prepare` accepts passes the certificate. -/
theorem prepCertOK_of_prepare {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) (p : Prepared)
    (hp : prepare cfg code true = .ok p) : prepCertOK cfg p = true := by
  unfold prepCertOK
  rw [Array.all_eq_true]
  intro j hj
  obtain ⟨hw, he, hg, hb⟩ :=
    FuelNest.prepare_funcs cfg code true p hp j p.funcs[j] (Array.getElem?_eq_getElem hj)
  have hn := FuelNest.nestOK_of_wellNested _ hw he
  have hf := FuelNest.freeCount_le_of_wellNested _ hw
  exact certOK_of_static cfg _ hw hn (wc_gasTable cfg _ hw hn he hg hr hl) (by omega)

/-- **The fuel certificate never fails.** For every configuration with
`0 < regular_op_cost ≤ linear_op_base_cost` and every contract, `fuelCertified` is `true`: the
former guard `w.fuel_certificate` is dead. -/
theorem fuelCertified_true {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) :
    fuelCertified cfg code = true := by
  unfold fuelCertified
  split
  · rename_i p hp; exact prepCertOK_of_prepare hr hl code p hp
  · rfl

/-- At the PV86 parameters. -/
theorem fuelCertified_true_pv86 (cfg : NearCfg) (hr : cfg.regularOpCost = pv86.regularOpCost)
    (hl : cfg.linearOpBaseCost = pv86.linearOpBaseCost) (code : ByteArray) :
    fuelCertified cfg code = true :=
  fuelCertified_true (by rw [hr]; decide) (by rw [hr, hl]; decide) code


end NearSpecV3.Wasm.FuelCertOK

#print axioms NearSpecV3.Wasm.FuelCertOK.certOK_of_static
#print axioms NearSpecV3.Wasm.FuelCertOK.fuelCertified_true
#print axioms NearSpecV3.Wasm.FuelCertOK.fuelCertified_true_pv86
