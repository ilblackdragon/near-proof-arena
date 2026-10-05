import ZkFormal.Udr.Np.Ali

/-!
# ZkFormal.Udr.Np.Bus — bus multisets of the decoded trace

`busMsgs` lists, per `(table, row, interaction)` of one side, the fingerprint
coefficient list `msg ++ [bus + 1]` with its natural multiplicity.  We show:

* the multiplicity of `m ++ [b + 1]` in the expanded list is `busCount b m`
  (`count_expand_busMsgs`), hence an unbalanced bus makes the two expanded
  lists non-permutations (`not_perm_of_unbalanced`);
* size bounds: `|busMsgs| · w ≤ Air.fpBound`, `|expand busMsgs| ≤ Air.multBound`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Generic sums -/

theorem foldr_add_sum {α : Type} (l : List α) (f : α → Nat) (a : Nat) :
    l.foldr (fun x acc => f x + acc) a = (l.map f).sum + a := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons, ih, List.map_cons, List.sum_cons]; omega

theorem sum_flatMap {α β : Type} (l : List α) (g : α → List β) (F : β → Nat) :
    ((l.flatMap g).map F).sum = (l.map fun x => ((g x).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

theorem sum_range_getD {α : Type} (d : α) : ∀ (l : List α) (g : Nat → α → Nat) (G : α → Nat),
    (∀ t (ht : t < l.length), g t l[t] ≤ G l[t]) →
    ((List.range l.length).map fun t => g t (l.getD t d)).sum ≤ (l.map G).sum
  | [], _, _, _ => by simp
  | a :: l, g, G, h => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map]
    refine Nat.add_le_add (h 0 (by simp)) ?_
    have := sum_range_getD d l (fun t x => g (t + 1) x) G (fun t ht =>
      h (t + 1) (by simp; omega))
    refine Nat.le_trans (Nat.le_of_eq ?_) this
    congr 1

theorem sum_range_tables (A : Air) (g : Nat → Nat) (G : Air.Table → Nat)
    (h : ∀ t (ht : t < A.tables.length), g t ≤ G A.tables[t]) :
    ((List.range A.tables.length).map g).sum ≤ (A.tables.map G).sum :=
  sum_range_getD ⟨0, [], [], 0⟩ A.tables (fun t _ => g t) G h

theorem sum_range_getD_eq {α : Type} (d : α) : ∀ (l : List α) (g : Nat → α → Nat) (t0 : Nat),
    ((List.range l.length).map fun t => g (t0 + t) (l.getD t d)).sum =
      ((List.range l.length).map fun t => g (t0 + t) (l.getD t d)).sum
  | _, _, _ => rfl

theorem sum_le_sum {α : Type} (l : List α) (f g : α → Nat) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := sum_le_of_le l f g h

theorem sum_eq_zero_of {α : Type} (l : List α) (f : α → Nat) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem sum_filter_eq {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · rw [List.filter_cons_of_pos h]; simp [h, ih]
    · rw [List.filter_cons_of_neg h]; simp [h, ih]

theorem count_expand (M : List Fp8) (l : List (List Fp8 × Nat)) :
    List.count M (expand l) = (l.map fun p => if p.1 = M then p.2 else 0).sum := by
  unfold expand
  rw [List.count_flatMap]
  congr 1
  apply List.map_congr_left
  intro ⟨m, k⟩ _
  simp [List.count_replicate]

theorem length_expand (l : List (List Fp8 × Nat)) : (expand l).length = (l.map Prod.snd).sum := by
  unfold expand
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro ⟨m, k⟩ _
  simp

theorem mem_expand {M : List Fp8} {l : List (List Fp8 × Nat)} (h : M ∈ expand l) :
    M ∈ l.map Prod.fst := by
  unfold expand at h
  obtain ⟨⟨m, k⟩, hp, hm⟩ := List.mem_flatMap.mp h
  have := List.eq_of_mem_replicate hm
  subst this
  exact List.mem_map.mpr ⟨_, hp, rfl⟩

/-! ## The bus count as a sum -/

def tbl0 : Air.Table := ⟨0, [], [], 0⟩

theorem tableOf_eq (A : Air) (t : Nat) : tableOf A t = A.tables.getD t tbl0 := rfl

theorem tableOf_lt {A : Air} {t : Nat} (ht : t < A.tables.length) : tableOf A t = A.tables[t] := by
  unfold tableOf; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem tableBusCount_eq (is : List Interaction) (tr : Air.Trace F) (t : Nat) (pub : List F)
    (b : Nat) (s : Bool) (m : List F) :
    tableBusCount is tr t pub b s m = ((List.range (tr.height t)).map fun r =>
      (is.map fun i => if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then
        i.multNat tr t r pub else 0).sum).sum := by
  unfold tableBusCount
  have : ∀ r acc, is.foldr (fun i acc' =>
      (if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0)
        + acc') acc = (is.map fun i => if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then
        i.multNat tr t r pub else 0).sum + acc := fun r acc => foldr_add_sum _ _ _
  simp only [this]
  rw [foldr_add_sum, Nat.add_zero]

theorem busCount_go_eq (tr : Air.Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    ∀ (Ts : List Air.Table) (t0 : Nat), busCount.go tr pub b s m Ts t0 =
      ((List.range Ts.length).map fun j =>
        tableBusCount (Ts.getD j tbl0).interactions tr (t0 + j) pub b s m).sum
  | [], _ => rfl
  | T :: Ts, t0 => by
    rw [busCount.go, busCount_go_eq tr pub b s m Ts (t0 + 1), List.length_cons,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map, Nat.add_zero]
    congr 2
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, List.getD_cons_succ, Nat.succ_eq_add_one]
    congr 1; omega

theorem busCount_eq (A : Air) (tr : Air.Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    busCount A tr pub b s m = ((List.range A.tables.length).map fun t =>
      tableBusCount (tableOf A t).interactions tr t pub b s m).sum := by
  unfold busCount; rw [busCount_go_eq]; simp only [Nat.zero_add]; rfl

end

/-! ## Injectivity of the tagged messages -/

theorem natCast_fp8_inj {x y : Nat} (hx : x < Algebra.P) (hy : y < Algebra.P) (h : (x : Fp8) = (y : Fp8)) : x = y := by
  have h0 := congrArg (fun a => (Fp8.c0 a).toNat) h
  have e1 : (Fp8.c0 (x : Fp8)).toNat = x % Algebra.P := Fp.toNat_ofNat x
  have e2 : (Fp8.c0 (y : Fp8)).toNat = y % Algebra.P := Fp.toNat_ofNat y
  rw [e1, e2, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h0
  exact h0

theorem map_ofBase_inj : ∀ {a b : List Fp}, a.map Fp8.ofBase = b.map Fp8.ofBase → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Fp8.ofBase_inj h.1, map_ofBase_inj h.2]

theorem tagged_inj {a b : List Fp} {x y : Nat} (hx : x + 1 < Algebra.P) (hy : y + 1 < Algebra.P)
    (h : a.map Fp8.ofBase ++ [((x + 1 : Nat) : Fp8)] = b.map Fp8.ofBase ++ [((y + 1 : Nat) : Fp8)]) :
    a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨map_ofBase_inj h1, by have := natCast_fp8_inj hx hy h2; omega⟩

theorem tag_ne_zero {x : Nat} (hx : x + 1 < Algebra.P) : ((x + 1 : Nat) : Fp8) ≠ 0 := by
  intro h
  have : ((x + 1 : Nat) : Fp8) = ((0 : Nat) : Fp8) := h
  have := natCast_fp8_inj hx (by decide) this
  omega

/-! ## Counting tagged messages -/

section
variable (A : Air) (prm : Params)

/-- All bus tags are below `P - 1`. -/
def BusTagsOk (A : Air) : Prop :=
  ∀ t, t < A.tables.length → ∀ i ∈ (tableOf A t).interactions, i.bus + 1 < Algebra.P

theorem count_expand_busMsgs (hA : BusTagsOk A) (τ : PTn) (s : Bool) (b : Nat) (m : List Fp)
    (hb : b + 1 < Algebra.P) :
    List.count (m.map Fp8.ofBase ++ [((b + 1 : Nat) : Fp8)]) (expand (busMsgs A prm τ s)) =
      busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b s m := by
  rw [count_expand, busCount_eq]
  simp only [busMsgs]
  rw [sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [sum_flatMap, tableBusCount_eq]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [List.map_map, sum_filter_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hib := hA t (List.mem_range.mp ht) i hi
  simp only [Function.comp]
  by_cases hs : i.send = s
  · have e1 : (i.send == s) = true := by simp [hs]
    rw [if_pos e1]
    by_cases hm : i.msgVal (decTrace A prm τ) t r (pubOf Fp τ.cb) = m ∧ i.bus = b
    · rw [if_pos (by rw [hm.1, hm.2]), if_pos ⟨hm.2, hs, hm.1⟩]
    · rw [if_neg (fun h => hm (by have := tagged_inj hib hb h; exact this)),
        if_neg (fun h => hm ⟨h.2.2, h.1⟩)]
  · have e1 : (i.send == s) = false := by simp [hs]
    rw [if_neg (by simp [e1]), if_neg (fun h => hs h.2.1)]

theorem busCount_zero_of_ge (τ : PTn) (s : Bool) (b : Nat) (m : List Fp)
    (hb : ∀ t, t < A.tables.length → ∀ i ∈ (tableOf A t).interactions, i.bus ≠ b) :
    busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b s m = 0 := by
  rw [busCount_eq]
  refine sum_eq_zero_of _ _ fun t ht => ?_
  rw [tableBusCount_eq]
  refine sum_eq_zero_of _ _ fun r _ => sum_eq_zero_of _ _ fun i hi => ?_
  rw [if_neg fun h => hb t (List.mem_range.mp ht) i hi h.1]

/-- An unbalanced bus makes the expanded message lists of the two sides
non-permutations. -/
theorem not_perm_of_unbalanced (hA : BusTagsOk A) (τ : PTn)
    (hbal : ¬ ∀ b m, busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b true m =
      busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b false m) :
    ¬ (expand (busMsgs A prm τ true)).Perm (expand (busMsgs A prm τ false)) := by
  intro hp
  apply hbal
  intro b m
  by_cases hb : ∃ t, t < A.tables.length ∧ ∃ i ∈ (tableOf A t).interactions, i.bus = b
  · obtain ⟨t, ht, i, hi, rfl⟩ := hb
    have hb' := hA t ht i hi
    rw [← count_expand_busMsgs A prm hA τ true _ m hb', ← count_expand_busMsgs A prm hA τ false _ m hb']
    exact hp.count_eq _
  · have h0 : ∀ t, t < A.tables.length → ∀ i ∈ (tableOf A t).interactions, i.bus ≠ b :=
      fun t ht i hi h => hb ⟨t, ht, i, hi, h⟩
    rw [busCount_zero_of_ge A prm τ true b m h0, busCount_zero_of_ge A prm τ false b m h0]

end

/-! ## Sizes -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem multNat_go_le (tr : Air.Trace F) (t r : Nat) (pub : List F) :
    ∀ (bs : List Expr) (k : Nat), Interaction.multNat.go tr t r pub bs k + 2 ^ k ≤ 2 ^ (k + bs.length)
  | [], k => by simp [Interaction.multNat.go]
  | b :: bs, k => by
    have hih := multNat_go_le tr t r pub bs (k + 1)
    rw [Interaction.multNat.go]
    have e : k + 1 + bs.length = k + (b :: bs).length := by simp; omega
    rw [e] at hih
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have h3 := Nat.two_pow_pos k
    generalize 2 ^ k = d at h2 h3 ⊢
    generalize 2 ^ (k + 1) = d' at h2 hih
    split <;> omega

theorem multNat_le (i : Interaction) (tr : Air.Trace F) (t r : Nat) (pub : List F) :
    i.multNat tr t r pub ≤ 2 ^ i.mult.length - 1 := by
  have := multNat_go_le tr t r pub i.mult 0
  unfold Interaction.multNat
  simp only [Nat.pow_zero, Nat.zero_add] at this
  omega

end

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The fingerprint width: longest message plus the bus tag. -/
def msgW (A : Air) : Nat :=
  (A.tables.flatMap fun T => T.interactions.map fun i => i.msg.length).foldr max 0 + 1

section
variable (A : Air) (prm : Params)

theorem mem_busMsgs {τ : PTn} {s : Bool} {M : List Fp8} (h : M ∈ (busMsgs A prm τ s).map Prod.fst) :
    ∃ t, t < A.tables.length ∧ ∃ i ∈ (tableOf A t).interactions, ∃ r,
      M = (i.msgVal (decTrace A prm τ) t r (pubOf Fp τ.cb)).map Fp8.ofBase ++ [((i.bus + 1 : Nat) : Fp8)] := by
  simp only [busMsgs, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_filter] at h
  obtain ⟨_, ⟨t, ht, r, _, i, ⟨hi, _⟩, rfl⟩, rfl⟩ := h
  exact ⟨t, ht, i, hi, r, rfl⟩

theorem busMsg_shape {τ : PTn} {s : Bool} {M : List Fp8} (hA : BusTagsOk A)
    (h : M ∈ (busMsgs A prm τ s).map Prod.fst) :
    ∃ a x, M = a ++ [x] ∧ x ≠ 0 ∧ M.length ≤ msgW A := by
  obtain ⟨t, ht, i, hi, r, rfl⟩ := mem_busMsgs A prm h
  refine ⟨_, _, rfl, tag_ne_zero (hA t ht i hi), ?_⟩
  simp only [List.length_append, List.length_map, List.length_singleton, Interaction.msgVal]
  unfold msgW
  have : i.msg.length ∈ A.tables.flatMap fun T => T.interactions.map fun i => i.msg.length :=
    List.mem_flatMap.mpr ⟨tableOf A t, by rw [tableOf_lt ht]; exact List.getElem_mem ht,
      List.mem_map.mpr ⟨i, hi, rfl⟩⟩
  have := le_foldr_max this
  omega

theorem height_le {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hok : headerOk A prm l = true)
    (t : Nat) (ht : t < A.tables.length) :
    (decTrace A prm τ).height t ≤ 2 ^ (tableOf A t).maxLog := by
  obtain ⟨hlen, hlog, _, _⟩ := headerOk_facts hok
  have h := (hlog t ht (by omega)).2.1
  rw [tableOf_lt ht]
  unfold Trace.height
  refine Nat.pow_le_pow_right (by decide) ?_
  show (hdrOf τ).getD t 0 ≤ _
  unfold hdrOf; rw [hl]
  simp only [Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < l.length by omega),
    Option.getD_some]
  exact h

theorem busMsgs_length {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hok : headerOk A prm l = true) :
    (busMsgs A prm τ true).length + (busMsgs A prm τ false).length ≤
      (A.tables.map fun T => 2 ^ T.maxLog * T.interactions.length).sum := by
  simp only [busMsgs, List.length_flatMap, List.length_map]
  rw [← sum_map_add]
  refine sum_range_tables A _ _ fun t ht => ?_
  rw [sum_map_const, sum_map_const, List.length_range, ← Nat.mul_add, length_filter_send]
  have := height_le A prm hl hok t ht
  rw [tableOf_lt ht] at this ⊢
  exact Nat.mul_le_mul_right _ this

theorem fpBound_eq (A : Air) :
    A.fpBound = (A.tables.map fun T => 2 ^ T.maxLog * T.interactions.length).sum * msgW A := rfl

theorem expand_length {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hok : headerOk A prm l = true) (s : Bool) :
    (expand (busMsgs A prm τ s)).length ≤ A.multBound := by
  rw [length_expand]
  simp only [busMsgs]
  rw [sum_flatMap]
  unfold Air.multBound
  refine sum_range_tables A _ _ (fun t ht => ?_)
  rw [sum_flatMap]
  refine Nat.le_trans (sum_le_length_mul _ _
    ((A.tables[t].interactions.map fun i => 2 ^ i.mult.length - 1).sum) fun r _ => ?_) ?_
  · rw [List.map_map]
    refine Nat.le_trans (Nat.le_of_eq (sum_filter_eq _ _ _)) ?_
    rw [← tableOf_lt ht]
    refine sum_le_sum _ _ _ fun i _ => ?_
    simp only [Function.comp]
    split
    · exact multNat_le i _ _ _ _
    · exact Nat.zero_le _
  · rw [List.length_range]
    have := height_le A prm hl hok t ht
    rw [tableOf_lt ht] at this
    exact Nat.mul_le_mul_right _ this

end

/-! ## Padding -/

def pad (w : Nat) (m : List Fp8) : List Fp8 := m ++ List.replicate (w - m.length) 0

def unpad (m : List Fp8) : List Fp8 := (m.reverse.dropWhile (fun y => y == 0)).reverse

theorem fp_zeros (α : Fp8) : ∀ k, ZkFormal.Udr.fp α (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, ZkFormal.Udr.fp_cons, fp_zeros α k]; grind

theorem fpL_pad (α : Fp8) (w : Nat) (m : List Fp8) : ZkFormal.Udr.fp α (pad w m) = fpL α m := by
  unfold pad ZkFormal.Udr.fp fpL combine
  rw [List.foldr_append]
  have := fp_zeros α (w - m.length)
  unfold ZkFormal.Udr.fp at this
  rw [this]

theorem dropWhile_zeros (L : List Fp8) : ∀ k, (List.replicate k (0 : Fp8) ++ L).dropWhile
    (fun y => y == 0) = L.dropWhile (fun y => y == 0)
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, List.cons_append, List.dropWhile_cons_of_pos (by simp),
      dropWhile_zeros L k]

theorem unpad_pad (w : Nat) (a : List Fp8) (x : Fp8) (hx : x ≠ 0) :
    unpad (pad w (a ++ [x])) = a ++ [x] := by
  unfold unpad pad
  rw [List.reverse_append, List.reverse_replicate, dropWhile_zeros, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.dropWhile_cons_of_neg (by simpa using hx)]
  simp

theorem pad_length (w : Nat) (m : List Fp8) (h : m.length ≤ w) : (pad w m).length = w := by
  unfold pad; simp; omega

theorem not_perm_pad (w : Nat) {A' B' : List (List Fp8)}
    (hA : ∀ M ∈ A' ++ B', ∃ a x, M = a ++ [x] ∧ x ≠ 0) (h : ¬ A'.Perm B') :
    ¬ (A'.map (pad w)).Perm (B'.map (pad w)) := by
  intro hp
  apply h
  have e : ∀ L : List (List Fp8), (∀ M ∈ L, ∃ a x, M = a ++ [x] ∧ x ≠ 0) →
      (L.map (pad w)).map unpad = L := fun L hL => by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id L]
    apply List.map_congr_left
    intro M hM
    obtain ⟨a, x, rfl, hx⟩ := hL M hM
    exact unpad_pad w a x hx
  rw [← e A' (fun M hM => hA M (List.mem_append_left _ hM)),
    ← e B' (fun M hM => hA M (List.mem_append_right _ hM))]
  exact hp.map _

/-! ## The fingerprint round count -/

theorem count_fp_collide (A : Air) (prm : Params) (hA : BusTagsOk A) (τ : PTn)
    (hnp : ¬ (expand (busMsgs A prm τ true)).Perm (expand (busMsgs A prm τ false))) :
    count Fp8.all (fun α => ¬ FpDiffer A prm τ α) ≤
      ((busMsgs A prm τ true).length + (busMsgs A prm τ false).length) * msgW A := by
  have hshape : ∀ M ∈ expand (busMsgs A prm τ true) ++ expand (busMsgs A prm τ false),
      ∃ a x, M = a ++ [x] ∧ x ≠ 0 ∧ M.length ≤ msgW A := fun M hM => by
    rcases List.mem_append.mp hM with h | h
    · exact busMsg_shape A prm hA (mem_expand h)
    · exact busMsg_shape A prm hA (mem_expand h)
  have hnp' := not_perm_pad (msgW A) (fun M hM => by
    obtain ⟨a, x, h1, h2, _⟩ := hshape M hM; exact ⟨a, x, h1, h2⟩) hnp
  have hga := ZkFormal.Udr.gpAlpha Fp8 (msgW A) ((expand (busMsgs A prm τ true)).map (pad (msgW A)))
    ((expand (busMsgs A prm τ false)).map (pad (msgW A)))
    (((busMsgs A prm τ true ++ busMsgs A prm τ false).map Prod.fst).map (pad (msgW A)))
    Fp8.all Fp8.nodup_all (fun m hm => by
      rw [← List.map_append] at hm
      obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hm
      obtain ⟨_, _, _, _, hlen⟩ := hshape M hM
      refine ⟨List.mem_map.mpr ⟨M, ?_, rfl⟩, pad_length _ _ hlen⟩
      rw [List.map_append]
      rcases List.mem_append.mp hM with h | h
      · exact List.mem_append_left _ (mem_expand h)
      · exact List.mem_append_right _ (mem_expand h)) hnp'
  refine Nat.le_trans (count_mono _ fun α hα => ?_) (Nat.le_trans hga (Nat.le_of_eq ?_))
  · simp only [FpDiffer, Classical.not_not] at hα
    simp only [List.map_map, Function.comp_def, fpL_pad]
    exact hα
  · simp [List.length_map, List.length_append]

end ZkFormal.Udr.Np
