import ZkFormal.Bcs.StarkChain

/-!
# ZkFormal.Bcs.StarkDecode — the verifier view decodes to L4's erased transcript
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- A schedule slot and its parse. -/
def SlotParse (hdr : List Nat) : Stark.Slot → Stark.PSlot K → Prop
  | .chal ood, .chal ood' => ood' = ood
  | .msg parts, .msg vs raw =>
    (∀ s, parseClear (F := F) hdr parts (Stark.clearOf vs raw ++ s) = some (vs.map Stark.PT.PartV.erase, s)) ∧
      (∀ r ∈ Stark.rootsOf vs, r.length = 64) ∧ (Stark.rootsOf vs).length = (oracleShapes parts).length
  | _, _ => False

inductive Fa2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Fa2 R [] []
  | cons {a b as bs} : R a b → Fa2 R as bs → Fa2 R (a :: as) (b :: bs)

theorem parseSlots_rel (hdr : List Nat) : ∀ (sched : List Stark.Slot) (r : Bytes)
    (ps : List (Stark.PSlot K)) (rest : Bytes),
    Stark.parseSlots (F := F) hdr sched r = some (ps, rest) → Fa2 (SlotParse (F := F) hdr) sched ps
  | [], r, ps, rest, h => by
    simp [Stark.parseSlots] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
  | .chal ood :: ss, r, ps, rest, h => by
    simp only [Stark.parseSlots] at h
    split at h
    · cases h
    · next ps' r' h' =>
      cases h
      exact .cons rfl (parseSlots_rel hdr ss r ps' rest h')
  | .msg parts :: ss, r, ps, rest, h => by
    simp only [Stark.parseSlots] at h
    split at h
    · cases h
    · next vs r1 h1 =>
      split at h
      · cases h
      · next ps' r2 h2 =>
        cases h
        obtain ⟨raw, e, hc, hl, hn⟩ := parseParts_clear hdr parts r vs r1 h1
        have hraw : r.take (r.length - r1.length) = raw := by
          rw [e]; simp
        refine .cons ?_ (parseSlots_rel hdr ss r1 ps' rest h2)
        show SlotParse hdr (.msg parts) (.msg vs (r.take (r.length - r1.length)))
        rw [hraw]
        exact ⟨hc, hl, hn⟩

/-- **The view decodes to the erased transcript.** -/
theorem decodeEntries_eq (hdr : List Nat) : ∀ (sched : List Stark.Slot) (ps : List (Stark.PSlot K))
    (entries : List (Stark.Entry K Bytes)) (es : List EntryV),
    Fa2 (SlotParse (F := F) hdr) sched ps → Rel3 (SlotRel (F := F)) ps entries es →
    decodeEntries (F := F) hdr sched es = some (entries.map Stark.PT.Entry.erase)
  | [], [], [], [], _, _ => rfl
  | s :: ss, p :: ps, e :: entries, v :: es, .cons hsp hsp', .cons hr hr' => by
    have ih := decodeEntries_eq hdr ss ps entries es hsp' hr'
    cases hr with
    | msg vs raw =>
      cases s with
      | chal _ => exact hsp.elim
      | msg parts =>
        obtain ⟨hc, _, _⟩ := hsp
        have := hc []
        rw [List.append_nil] at this
        simp only [decodeEntries, this, ih, Option.map_some, List.map_cons]
        rfl
    | chal ood y =>
      cases s with
      | msg _ => exact hsp.elim
      | chal ood' =>
        have e : ood = ood' := hsp
        subst e
        simp only [decodeEntries, ih, Option.map_some, List.map_cons]
        rfl

omit [DecidableEq F] in
theorem roots_ok (hdr : List Nat) : ∀ (sched : List Stark.Slot) (ps : List (Stark.PSlot K)),
    Fa2 (SlotParse (F := F) hdr) sched ps →
    (∀ parts, Stark.Slot.msg parts ∈ sched → (oracleShapes parts).length < 256) → RootsOk ps
  | [], [], _, _ => fun _ _ h => by simp at h
  | s :: ss, p :: ps, .cons hsp hrest, hlt => by
    intro vs raw hm
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      cases s with
      | chal _ => exact hsp.elim
      | msg parts =>
        obtain ⟨_, hl, hn⟩ := hsp
        exact ⟨hl, hn ▸ hlt parts List.mem_cons_self⟩
    · exact roots_ok hdr ss ps hrest (fun parts hp => hlt parts (List.mem_cons_of_mem _ hp)) vs raw hm

/-- The header is read back from the first message. -/
theorem viewHeader_eq (V : Stark.IopSpec F K) (hdr : List Nat) (ps' : List Stark.Part)
    (ss : List Stark.Slot) (ps : List (Stark.PSlot K)) (entries : List (Stark.Entry K Bytes))
    (es : List EntryV) (cur : Bytes)
    (hfa : Fa2 (SlotParse (F := F) hdr) (.msg (.header V.numTables :: ps') :: ss) ps)
    (hrel : Rel3 (SlotRel (F := F)) ps entries es) :
    viewHeader V es cur = some hdr := by
  cases hfa with
  | cons hsp _ =>
    cases hrel with
    | cons hr _ =>
      cases hr with
      | chal _ _ => exact hsp.elim
      | msg vs raw =>
        obtain ⟨hc, _, _⟩ := hsp
        have h := hc []
        rw [List.append_nil] at h
        simp only [viewHeader]
        simp only [parseClear] at h
        split at h
        · cases h
        · rename_i v r1 h1
          split at h1
          · rename_i l r3 h3
            split at h1
            · rename_i hl
              cases h1
              rw [h3]
              simp only [Option.map_some, Option.some.injEq]
              exact beq_iff_eq.mp hl
            · cases h1
          · cases h1

end

end ZkFormal.Bcs.Adapter
