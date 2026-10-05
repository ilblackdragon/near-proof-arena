import ZkFormal.Bcs.TransStatements

/-!
# ZkFormal.Bcs.DecPush — decoding is a prefix-compatible map

`decNone : DecNoneStmt`, `decMsg : DecMsgStmt`, `decChal_ok : DecChalStmt`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

theorem decEntries_snoc_none (hdr : List Nat) : ∀ (sched : List Stark.Slot) (es : List (Entry mmcs))
    (e : Entry mmcs), decEntries (F := F) (K := K) hdr sched es = none →
      decEntries (F := F) (K := K) hdr sched (es ++ [e]) = none
  | _, [], _, h => by simp [decEntries] at h
  | [], _ :: _, _, _ => by simp [decEntries]
  | .msg parts :: ss, .msg r c os :: es, e, h => by
    simp only [List.cons_append, decEntries] at h ⊢
    rcases hp : Adapter.parseClear (F := F) (K := K) hdr parts c with _ | ⟨vs, _ | ⟨b, bs⟩⟩
    · rfl
    · rw [hp] at h
      simp only [Option.map_eq_none_iff] at h ⊢
      exact decEntries_snoc_none hdr ss es e h
    · rfl
  | .chal ood :: ss, .chal y :: es, e, h => by
    simp only [List.cons_append, decEntries, Option.map_eq_none_iff] at h ⊢
    exact decEntries_snoc_none hdr ss es e h
  | .msg _ :: ss, .chal _ :: es, _, _ => by simp [decEntries]
  | .chal _ :: ss, .msg _ _ _ :: es, _, _ => by simp [decEntries]

/-- The last decoded entry comes from the slot at the prefix length. -/
theorem decEntries_snoc (hdr : List Nat) : ∀ (sched : List Stark.Slot) (es : List (Entry mmcs))
    (e : Entry mmcs) (r : List (Stark.Entry K (Stark.Oracle F))),
    decEntries (F := F) (K := K) hdr sched (es ++ [e]) = some r →
      ∃ l x, decEntries (F := F) (K := K) hdr sched es = some l ∧ r = l ++ [x] ∧ l.length = es.length ∧
        ((∃ parts roots raw os vs, sched[es.length]? = some (.msg parts) ∧ e = .msg roots raw os ∧
            x = .msg vs) ∨
         (∃ ood y, sched[es.length]? = some (.chal ood) ∧ e = .chal y ∧ x = .chal (decChal (F := F) ood y)))
  | [], [], e, r, h => by cases e <;> simp [decEntries] at h
  | .msg parts :: ss, [], e, r, h => by
    cases e with
    | chal y => simp [decEntries] at h
    | msg roots raw os =>
      simp only [List.nil_append, decEntries] at h
      split at h
      · rename_i vs hp
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨[], _, rfl, rfl, rfl, Or.inl ⟨parts, roots, raw, os, _, rfl, rfl, rfl⟩⟩
      · cases h
  | .chal ood :: ss, [], e, r, h => by
    cases e with
    | msg _ _ _ => simp [decEntries] at h
    | chal y =>
      simp only [List.nil_append, decEntries, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨[], _, rfl, rfl, rfl, Or.inr ⟨ood, y, rfl, rfl, rfl⟩⟩
  | [], _ :: _, e, r, h => by simp [decEntries] at h
  | .msg parts :: ss, .msg ro ra os :: es, e, r, h => by
    simp only [List.cons_append, decEntries] at h
    split at h
    · rename_i vs hp
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      obtain ⟨l, x, hl, rfl, hlen, hk⟩ := decEntries_snoc hdr ss es e r' hr'
      refine ⟨_ :: l, x, ?_, rfl, by simp [hlen], ?_⟩
      · simp only [decEntries, hp, hl, Option.map_some]
      · simpa using hk
    · cases h
  | .chal ood :: ss, .chal y :: es, e, r, h => by
    simp only [List.cons_append, decEntries, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    obtain ⟨l, x, hl, rfl, hlen, hk⟩ := decEntries_snoc hdr ss es e r' hr'
    refine ⟨_ :: l, x, ?_, rfl, by simp [hlen], ?_⟩
    · simp only [decEntries, hl, Option.map_some]
    · simpa using hk
  | .msg _ :: ss, .chal _ :: es, e, r, h => by simp [decEntries] at h
  | .chal _ :: ss, .msg _ _ _ :: es, e, r, h => by simp [decEntries] at h

/-- The first decoded entry carries the header. -/
theorem decEntries_head (V : Stark.IopSpec F K) (hS : Adapter.SchedOk V) (cb : Bytes) (hdr : List Nat)
    (hok : V.headerOk hdr = true) (e : Entry mmcs) (es : List (Entry mmcs))
    (l : List (Stark.Entry K (Stark.Oracle F)))
    (h : decEntries (F := F) (K := K) hdr (V.schedule hdr) (e :: es) = some l) :
    (⟨cb, l⟩ : Stark.PT K (Stark.Oracle F)).header? = some hdr := by
  obtain ⟨ps, ss, hs⟩ := hS.first hdr hok
  rw [hs] at h
  cases e with
  | chal y => simp [decEntries] at h
  | msg roots raw os =>
    simp only [decEntries] at h
    split at h
    · rename_i vs hp
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r', _, rfl⟩ := h
      simp only [Adapter.parseClear] at hp
      split at hp
      · cases hp
      · rename_i v r1 h1
        split at h1
        · rename_i lh r3 h3
          split at h1
          · rename_i hl
            cases h1
            split at hp
            · cases hp
            · rename_i ws r2 h2
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, _⟩ := hp
              simp only [fill, Stark.PT.header?]
              rw [beq_iff_eq.mp hl]
          · cases h1
        · cases h1
    · cases h

theorem slots_of_header (V : Stark.IopSpec F K) (σ : Stark.PT K (Stark.Oracle F)) (hdr : List Nat)
    (h : σ.header? = some hdr) : V.slots σ = V.schedule hdr := by
  simp [Stark.IopSpec.slots, h]

theorem decNone : DecNoneStmt := by
  intro F K _ _ _ _ V τ e h
  obtain ⟨cb, es⟩ := τ
  cases es with
  | nil => simp [decodePT] at h
  | cons e0 es =>
    simp only [decodePT, PT.push, List.cons_append] at h ⊢
    have hv : Adapter.viewHeader V (PT.view ⟨cb, e0 :: (es ++ [e])⟩).entries [] =
        Adapter.viewHeader V (PT.view ⟨cb, e0 :: es⟩).entries [] := by
      simp only [PT.view, List.map_cons]
      cases e0 <;> rfl
    rw [hv]
    cases hh : Adapter.viewHeader V (PT.view ⟨cb, e0 :: es⟩).entries [] with
    | none => rfl
    | some hdr =>
      rw [hh] at h
      simp only at h ⊢
      by_cases hok : V.headerOk hdr = true
      · rw [if_pos hok] at h ⊢
        simp only [Option.map_eq_none_iff] at h ⊢
        have := decEntries_snoc_none (F := F) (K := K) hdr (V.schedule hdr) (e0 :: es) e h
        simpa using this
      · rw [if_neg hok]

/-- Decoding a nonempty pushed transcript, unfolded. -/
theorem decodePT_push_cons (V : Stark.IopSpec F K) (cb : Bytes) (e0 : Entry mmcs) (es : List (Entry mmcs))
    (e : Entry mmcs) (σ' : Stark.PT K (Stark.Oracle F))
    (h : decodePT (F := F) V (PT.push ⟨cb, e0 :: es⟩ e) = some σ') :
    ∃ hdr r, Adapter.viewHeader V (PT.view ⟨cb, e0 :: es⟩).entries [] = some hdr ∧ V.headerOk hdr = true ∧
      decEntries (F := F) (K := K) hdr (V.schedule hdr) ((e0 :: es) ++ [e]) = some r ∧ σ' = ⟨cb, r⟩ := by
  simp only [decodePT, PT.push, List.cons_append] at h
  have hv : Adapter.viewHeader V (PT.view ⟨cb, e0 :: (es ++ [e])⟩).entries [] =
      Adapter.viewHeader V (PT.view ⟨cb, e0 :: es⟩).entries [] := by
    simp only [PT.view, List.map_cons]
    cases e0 <;> rfl
  rw [hv] at h
  cases hh : Adapter.viewHeader V (PT.view ⟨cb, e0 :: es⟩).entries [] with
  | none => rw [hh] at h; cases h
  | some hdr =>
    rw [hh] at h
    simp only at h
    by_cases hok : V.headerOk hdr = true
    · rw [if_pos hok] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨hdr, r, rfl, hok, by simpa using hr, rfl⟩
    · rw [if_neg hok] at h; cases h

theorem decodePT_cons (V : Stark.IopSpec F K) (cb : Bytes) (e0 : Entry mmcs) (es : List (Entry mmcs))
    (hdr : List Nat) (hh : Adapter.viewHeader V (PT.view ⟨cb, e0 :: es⟩).entries [] = some hdr)
    (hok : V.headerOk hdr = true) :
    decodePT (F := F) V ⟨cb, e0 :: es⟩ =
      (decEntries (F := F) (K := K) hdr (V.schedule hdr) (e0 :: es)).map (⟨cb, ·⟩) := by
  simp only [decodePT]
  rw [hh]
  simp only [hok, if_true]

theorem decMsg : DecMsgStmt := by
  intro F K _ _ _ _ V hS τ roots raw os σ' h
  obtain ⟨cb, es⟩ := τ
  cases es with
  | nil =>
    simp only [decodePT, PT.push, List.nil_append] at h
    split at h
    · rename_i hdr hh
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        obtain ⟨l, x, hl, rfl, hlen, hk⟩ := decEntries_snoc (F := F) (K := K) hdr (V.schedule hdr) [] _ r
          (by simpa using hr)
        simp only [decEntries, Option.some.injEq] at hl
        subst hl
        rcases hk with ⟨parts, ro, ra, os', vs, hs, he, rfl⟩ | ⟨ood, y, _, he, _⟩
        · refine ⟨Stark.PT.init cb, vs, by simp [decodePT], ⟨[.header V.numTables], ?_⟩, rfl⟩
          simp [Stark.IopSpec.slots, Stark.PT.header?, Stark.PT.init]
        · cases he
      · cases h
    · cases h
  | cons e0 es =>
    obtain ⟨hdr, r, hh, hok, hr, rfl⟩ := decodePT_push_cons V cb e0 es _ σ' h
    obtain ⟨l, x, hl, rfl, hlen, hk⟩ := decEntries_snoc (F := F) (K := K) hdr (V.schedule hdr) _ _ r hr
    rcases hk with ⟨parts, ro, ra, os', vs, hs, he, rfl⟩ | ⟨ood, y, _, he, _⟩
    · refine ⟨⟨cb, l⟩, vs, by rw [decodePT_cons V cb e0 es hdr hh hok, hl]; rfl, ⟨parts, ?_⟩, rfl⟩
      rw [slots_of_header V _ hdr (decEntries_head V hS cb hdr hok e0 es l hl)]
      simpa [hlen] using hs
    · cases he

theorem decChal_ok : DecChalStmt := by
  intro F K _ _ _ _ V hS τ σ hσ
  refine ⟨match (V.slots σ)[σ.entries.length]? with
    | some (.chal b) => b
    | _ => false, fun y σ' h => ?_⟩
  obtain ⟨cb, es⟩ := τ
  cases es with
  | nil => simp [decodePT, PT.push, PT.view, Entry.view, Adapter.viewHeader] at h
  | cons e0 es =>
    obtain ⟨hdr, r, hh, hok, hr, rfl⟩ := decodePT_push_cons V cb e0 es _ σ' h
    obtain ⟨l, x, hl, rfl, hlen, hk⟩ := decEntries_snoc (F := F) (K := K) hdr (V.schedule hdr) _ _ r hr
    rw [decodePT_cons V cb e0 es hdr hh hok, hl] at hσ
    simp only [Option.map_some, Option.some.injEq] at hσ
    subst hσ
    have hsl := slots_of_header V ⟨cb, l⟩ hdr (decEntries_head V hS cb hdr hok e0 es l hl)
    rcases hk with ⟨parts, ro, ra, os', vs, hs, he, _⟩ | ⟨ood, y', hs, he, rfl⟩
    · cases he
    · cases he
      have hs' : (V.slots ⟨cb, l⟩)[(⟨cb, l⟩ : Stark.PT K (Stark.Oracle F)).entries.length]? = some (.chal ood) := by
        rw [hsl]; simpa [hlen] using hs
      refine ⟨⟨ood, hs'⟩, ?_⟩
      simp only [hs']
      rfl

end

end ZkFormal.Bcs.Transport
