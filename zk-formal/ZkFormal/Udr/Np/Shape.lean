import ZkFormal.Udr.Np.Statements

/-!
# ZkFormal.Udr.Np.Shape — `ShapedPrefixStmt` and `ScheduleAltStmt`

* Prefixes of shaped transcripts are shaped (once the header is present the
  slots are fixed; before it, the empty transcript is trivially shaped).
* The schedule of `Iop.verifier` is a list of `[msg, chal]` pairs followed by
  one final message, so message slots are exactly the even ones.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Headers of extensions -/

theorem header?_append {K O : Type} (cb : Bytes) (es l : List (Entry K O)) (h : es ≠ []) :
    PT.header? (⟨cb, es ++ l⟩ : PT K O) = PT.header? (⟨cb, es⟩ : PT K O) := by
  obtain ⟨e, es', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [List.cons_append]
  cases e with
  | msg ps => cases ps with
    | nil => rfl
    | cons p ps => cases p <;> rfl
  | chal => rfl

theorem header?_push {K O : Type} (τ : PT K O) (m : List (PartV K O)) (h : τ.entries ≠ []) :
    (τ.push m).header? = τ.header? := header?_append τ.cb τ.entries _ h

theorem header?_pushChal {K O : Type} (τ : PT K O) (c : K) (h : τ.entries ≠ []) :
    (τ.pushChal c).header? = τ.header? := header?_append τ.cb τ.entries _ h

theorem header?_nil {K O : Type} (τ : PT K O) (h : τ.entries = []) : τ.header? = none := by
  unfold PT.header?; rw [h]

/-! ## Shaped prefixes -/

theorem shaped_of_append {F K : Type} (V : IopSpec F K) (τ : PT K (Oracle F))
    (x : Entry K (Oracle F)) (hs : Shaped V (⟨τ.cb, τ.entries ++ [x]⟩ : PT K (Oracle F))) :
    Shaped V τ := by
  by_cases h0 : τ.entries = []
  · refine ⟨fun l hl => ?_, ?_, fun k hk => ?_⟩
    · rw [header?_nil τ h0] at hl; cases hl
    · rw [h0]; exact Nat.zero_le _
    · rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)
  · have hh : PT.header? (⟨τ.cb, τ.entries ++ [x]⟩ : PT K (Oracle F)) = τ.header? :=
      header?_append τ.cb τ.entries _ h0
    have hsl : V.slots (⟨τ.cb, τ.entries ++ [x]⟩ : PT K (Oracle F)) = V.slots τ := by
      unfold IopSpec.slots; rw [hh]
    obtain ⟨h1, h2, h3⟩ := hs
    rw [hsl] at h2 h3
    refine ⟨fun l hl => h1 l (hh ▸ hl), ?_, fun k hk => ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at h2; omega
    · obtain ⟨s, hs1, hs2⟩ := h3 k (by simp only [List.length_append]; omega)
      refine ⟨s, hs1, ?_⟩
      simp only [List.getElem_append_left hk] at hs2
      exact hs2

theorem shapedPrefix : ShapedPrefixStmt := by
  intro A prm τ
  exact ⟨fun m hs => shaped_of_append _ τ _ hs, fun c hs => shaped_of_append _ τ _ hs⟩

/-! ## Alternation of the schedule -/

/-- A list of `[msg, chal]` pairs. -/
def IsPairs (l : List Slot) : Prop :=
  ∃ ps : List (List Part × Bool), l = ps.flatMap fun p => [Slot.msg p.1, Slot.chal p.2]

theorem IsPairs.nil : IsPairs [] := ⟨[], rfl⟩

theorem IsPairs.pair (a : List Part) (b : Bool) : IsPairs [.msg a, .chal b] := ⟨[(a, b)], rfl⟩

theorem IsPairs.append {l l' : List Slot} (h : IsPairs l) (h' : IsPairs l') : IsPairs (l ++ l') := by
  obtain ⟨ps, rfl⟩ := h; obtain ⟨ps', rfl⟩ := h'
  exact ⟨ps ++ ps', by rw [List.flatMap_append]⟩

theorem IsPairs.flatMap {α : Type} (l : List α) (f : α → List Slot) (h : ∀ a ∈ l, IsPairs (f a)) :
    IsPairs (l.flatMap f) := by
  induction l with
  | nil => exact IsPairs.nil
  | cons a l ih =>
    rw [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem IsPairs.ite (c : Prop) [Decidable c] {l l' : List Slot} (h : IsPairs l) (h' : IsPairs l') :
    IsPairs (if c then l else l') := by
  split <;> assumption

/-- Is the slot a message? -/
def slotIsMsg : Slot → Bool
  | .msg _ => true
  | .chal _ => false

theorem alt_pairs (x : List Part) : ∀ (ps : List (List Part × Bool)) (k : Nat) (s : Slot),
    ((ps.flatMap fun p => [Slot.msg p.1, Slot.chal p.2]) ++ [.msg x])[k]? = some s →
    (slotIsMsg s = true ↔ k % 2 = 0)
  | [], k, s, h => by
    match k, h with
    | 0, h => simp at h; subst h; simp [slotIsMsg]
    | k + 1, h => simp at h
  | p :: ps, k, s, h => by
    rw [List.flatMap_cons] at h
    match k, h with
    | 0, h => simp at h; subst h; simp [slotIsMsg]
    | 1, h => simp at h; subst h; simp [slotIsMsg]
    | k + 2, h =>
      have := alt_pairs x ps k s (by simpa using h)
      rw [this]; omega

theorem schedule_pairs (A : Air) (prm : Params) (l : List Nat) :
    ∃ ps : List (List Part × Bool),
      schedule A prm l = (ps.flatMap fun p => [Slot.msg p.1, Slot.chal p.2]) ++ [.msg [.elems 2]] := by
  have hp : IsPairs
      ([.msg [.header A.tables.length, .oracle ((layout A prm l).map fun L => (L.lde, L.width))],
        .chal false, .msg [], .chal false,
        .msg [.oracle ((layout A prm l).map fun L => (L.lde, 8 * L.aux)),
          .elems (((layout A prm l).map fun L => L.sendG + L.recvG).sum)], .chal false,
        .msg [.oracle ((layout A prm l).map fun L => (L.lde, 8 * L.quot))], .chal true,
        .msg [.elems (((layout A prm l).map fun L => 2 * L.width + 2 * L.aux + L.quot).sum)],
        .chal false] ++
      ((List.range (batchRounds (layout A prm l) - 1)).flatMap fun _ => [.msg [], .chal false]) ++
      (((List.range (finalLayer A prm l)).flatMap fun i =>
        (if rollInAt A prm l i then [.msg [], .chal false] else []) ++
        (match (friCommits A prm l).lookup i with
         | some a => [.msg [.oracle [(queryLog A prm l - i - a, 8 * 2 ^ a)]], .chal false]
         | none => [.msg [], .chal false])) ++
      (if rollInAt A prm l (finalLayer A prm l) then [.msg [], .chal false] else []))) := by
    have h10 : ∀ (a b c d e : List Part) (b1 b2 b3 b4 b5 : Bool),
        IsPairs [.msg a, .chal b1, .msg b, .chal b2, .msg c, .chal b3, .msg d, .chal b4, .msg e,
          .chal b5] := fun a b c d e b1 b2 b3 b4 b5 => ⟨[(a, b1), (b, b2), (c, b3), (d, b4), (e, b5)], rfl⟩
    refine IsPairs.append (IsPairs.append (h10 ..) (IsPairs.flatMap _ _ fun _ _ => IsPairs.pair _ _))
      (IsPairs.append (IsPairs.flatMap _ _ fun i _ => IsPairs.append
        (IsPairs.ite _ (IsPairs.pair _ _) IsPairs.nil) ?_) (IsPairs.ite _ (IsPairs.pair _ _) IsPairs.nil))
    split
    · exact IsPairs.pair _ _
    · exact IsPairs.pair _ _
  obtain ⟨ps, hps⟩ := hp
  refine ⟨ps, ?_⟩
  rw [← hps]
  simp only [schedule, friSchedule, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem scheduleAlt : ScheduleAltStmt := by
  intro A prm τ _
  have key : ∀ k s, (Vnp A prm).slots τ = (Vnp A prm).slots τ → ((Vnp A prm).slots τ)[k]? = some s →
      (slotIsMsg s = true ↔ k % 2 = 0) := by
    intro k s _ h
    unfold IopSpec.slots at h
    split at h
    · obtain ⟨ps, hps⟩ := schedule_pairs A prm _
      exact alt_pairs _ ps k s (by rw [← hps]; exact h)
    · exact alt_pairs _ [] k s (by simpa using h)
  refine ⟨fun ⟨ps, h⟩ => (key _ _ rfl h).mp rfl, fun ⟨b, h⟩ => ?_⟩
  have := key _ _ rfl h
  simp only [slotIsMsg, Bool.false_eq_true, false_iff] at this
  omega

end ZkFormal.Udr.Np
