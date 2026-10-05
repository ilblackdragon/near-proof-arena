import ZkFormal.Prover.NpStatements
import ZkFormal.Stark.Laws

/-!
# ZkFormal.Prover.NpCompose — `NpIopCompleteStmt'` from the component statements

Every transcript the honest prover reaches has, at entry `k`, the honest message
`npMsg (chals.take (k/2)) (k/2)` (even `k`) or the `(k/2)`-th challenge (odd `k`)
(`Inv`); at the query phase the prefix property turns it into
`honT (τ.chals)`, on which `GlobalStmt` and `LocalStmt` apply.  `Shaped` and the
header facts of `ProverWf` follow from `MsgFitsStmt` and `SchedFormStmt`.
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

/-! ## Indexing pair lists -/

theorem getElem?_flatMap_pair {α β : Type} (f g : α → β) : ∀ (l : List α) (k : Nat),
    (l.flatMap fun a => [f a, g a])[k]? = (l[k / 2]?).map (fun a => if k % 2 = 0 then f a else g a)
  | [], k => by simp
  | a :: l, 0 => by simp
  | a :: l, 1 => by simp
  | a :: l, k + 2 => by
    rw [List.flatMap_cons, show [f a, g a] ++ l.flatMap (fun a => [f a, g a]) =
      f a :: g a :: l.flatMap (fun a => [f a, g a]) from rfl]
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ, getElem?_flatMap_pair f g l k,
      show (k + 2) / 2 = k / 2 + 1 by omega, List.getElem?_cons_succ,
      show (k + 2) % 2 = k % 2 by omega]

theorem length_slotsOf : ∀ ps : List (List Part × Bool), (slotsOf ps).length = 2 * ps.length
  | [] => rfl
  | p :: ps => by
    show (Slot.msg p.1 :: Slot.chal p.2 :: slotsOf ps).length = _
    rw [List.length_cons, List.length_cons, length_slotsOf ps, List.length_cons]; omega

theorem slotsOf_get (ps : List (List Part × Bool)) (k : Nat) :
    (slotsOf ps)[k]? = (ps[k / 2]?).map (fun p => if k % 2 = 0 then Slot.msg p.1 else Slot.chal p.2) :=
  getElem?_flatMap_pair (fun p : List Part × Bool => Slot.msg p.1) (fun p => Slot.chal p.2) ps k

theorem length_flatMap_pair {α β : Type} (f g : α → β) : ∀ l : List α,
    (l.flatMap fun a => [f a, g a]).length = 2 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_pair f g l, List.length_cons]
    simp; omega

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem sched_at (hS : SchedFormStmt) (k : Nat) :
    (schedule A dp (hdr A tr))[k]? =
      if k < 2 * nMsg A tr then
        (if k % 2 = 0 then some (.msg (msgParts A tr (k / 2)))
          else ((slotPairs A tr)[k / 2]?).map fun p => .chal p.2)
      else if k = 2 * nMsg A tr then some (.msg [.elems 2]) else none := by
  rw [hS A tr]
  have hlen : (slotsOf (slotPairs A tr)).length = 2 * nMsg A tr := length_slotsOf _
  by_cases hk : k < 2 * nMsg A tr
  · rw [if_pos hk, List.getElem?_append_left (by omega), slotsOf_get]
    have hj : k / 2 < (slotPairs A tr).length := by unfold nMsg at hk; omega
    rw [List.getElem?_eq_getElem hj]
    split
    · simp [msgParts, List.getElem?_eq_getElem hj]
    · simp
  · rw [if_neg hk, List.getElem?_append_right (by omega), hlen]
    by_cases he : k = 2 * nMsg A tr
    · rw [if_pos he, he, Nat.sub_self]; rfl
    · rw [if_neg he]; simp; omega

/-- Entry `k` of the honest transcript for challenges `cs` (as computed at the time). -/
noncomputable def entOf (cs : List Fp8) (k : Nat) : Entry Fp8 (Oracle Fp) :=
  if k % 2 = 0 then .msg (npMsg A cb tr (cs.take (k / 2)) (k / 2)) else .chal (cs.getD (k / 2) 0)

/-- The invariant of reachable transcripts. -/
structure Inv (τ : PT Fp8 (Oracle Fp)) : Prop where
  cb_eq : τ.cb = cb
  len : τ.chals.length = τ.entries.length / 2
  le : τ.entries.length ≤ 2 * nMsg A tr + 1
  ent : ∀ k (hk : k < τ.entries.length), τ.entries[k] = entOf A cb tr τ.chals k
  ood : 8 ≤ τ.entries.length → ¬ (τ.chals.getD 3 0).IsBase

theorem npMsg_zero (cs : List Fp8) :
    npMsg A cb tr cs 0 = [.header (hdr A tr), .oracle (mainO A tr)] := by
  simp [npMsg]

theorem inv_header {τ : PT Fp8 (Oracle Fp)} (h : Inv A cb tr τ) (hne : τ.entries ≠ []) :
    τ.header? = some (hdr A tr) := by
  have h0 := h.ent 0 (List.length_pos_iff.mpr hne)
  unfold PT.header?
  match he : τ.entries, hne with
  | e :: es, _ =>
    have : e = entOf A cb tr τ.chals 0 := by simpa [he] using h0
    rw [this]; simp [entOf, npMsg_zero]

theorem slots_of_header {τ : PT Fp8 (Oracle Fp)} (h : τ.header? = some (hdr A tr)) :
    (Vd A).slots τ = schedule A dp (hdr A tr) := by
  simp only [IopSpec.slots, h]; rfl

theorem header_nil {τ : PT Fp8 (Oracle Fp)} (h : τ.entries = []) : τ.header? = none := by
  unfold PT.header?; rw [h]

theorem chals_push' (τ : PT Fp8 (Oracle Fp)) (m : List (PartV Fp8 (Oracle Fp))) :
    (τ.push m).chals = τ.chals := chals_push τ m

theorem chals_pushChal' (τ : PT Fp8 (Oracle Fp)) (c : Fp8) :
    (τ.pushChal c).chals = τ.chals ++ [c] := chals_pushChal τ c

/-- Slot `E` of a transcript satisfying `Inv`. -/
theorem slot_at (hS : SchedFormStmt) {τ : PT Fp8 (Oracle Fp)} (h : Inv A cb tr τ) :
    ((Vd A).slots τ)[τ.entries.length]? =
      if τ.entries.length = 0 then some (.msg [.header A.tables.length])
      else (schedule A dp (hdr A tr))[τ.entries.length]? := by
  by_cases h0 : τ.entries.length = 0
  · rw [if_pos h0]
    have := header_nil (τ := τ) (List.eq_nil_of_length_eq_zero h0)
    simp only [IopSpec.slots, this, h0]; rfl
  · rw [if_neg h0, slots_of_header A tr (inv_header A cb tr h (by
      intro he; rw [he] at h0; exact h0 rfl))]

theorem msg_even (hS : SchedFormStmt) {τ : PT Fp8 (Oracle Fp)} (h : Inv A cb tr τ)
    {ps : List Part} (hs : ((Vd A).slots τ)[τ.entries.length]? = some (.msg ps)) :
    τ.entries.length % 2 = 0 ∧ τ.entries.length + 1 ≤ 2 * nMsg A tr + 1 := by
  rw [slot_at A cb tr hS h] at hs
  by_cases h0 : τ.entries.length = 0
  · rw [h0]; omega
  · rw [if_neg h0, sched_at A tr hS] at hs
    split at hs
    · split at hs
      · omega
      · cases h' : (slotPairs A tr)[τ.entries.length / 2]? <;> rw [h'] at hs <;> simp at hs
    · split at hs
      · omega
      · cases hs

theorem chal_odd (hS : SchedFormStmt) {τ : PT Fp8 (Oracle Fp)} (h : Inv A cb tr τ)
    {b : Bool} (hs : ((Vd A).slots τ)[τ.entries.length]? = some (.chal b)) :
    τ.entries.length % 2 = 1 ∧ τ.entries.length < 2 * nMsg A tr ∧
      (τ.entries.length = 7 → b = true) := by
  rw [slot_at A cb tr hS h] at hs
  by_cases h0 : τ.entries.length = 0
  · rw [if_pos h0] at hs; cases hs
  · rw [if_neg h0, sched_at A tr hS] at hs
    split at hs
    · split at hs
      · cases hs
      · rename_i hlt hodd
        refine ⟨by omega, hlt, fun h7 => ?_⟩
        rw [h7] at hs
        have : (slotPairs A tr)[3]? = some ([.oracle ((layout A dp (hdr A tr)).map fun L =>
            (L.lde, 8 * L.quot))], true) := by
          simp [slotPairs]
        simp only [show 7 / 2 = 3 from rfl, this, Option.map_some, Option.some.injEq,
          Slot.chal.injEq] at hs
        exact hs.symm
    · split at hs <;> cases hs

theorem decChal_ood (y : Bytes) :
    ¬ (Bcs.Transport.decChal (F := Fp) (K := Fp8) true y).IsBase := by
  simp only [Bcs.Transport.decChal, ite_true]
  rw [decodeOod_agree]
  exact decodeOod_not_base y

/-- **Reachable transcripts satisfy `Inv`.** -/
theorem reach_inv (hS : SchedFormStmt) {τ : PT Fp8 (Oracle Fp)}
    (hr : Reach (Vd A) (npProver A cb tr) cb τ) : Inv A cb tr τ := by
  induction hr with
  | init =>
    exact ⟨rfl, by simp [PT.init, PT.chals], by simp [PT.init], fun k hk => by simp [PT.init] at hk, fun h => by
      simp [PT.init] at h⟩
  | msg τ _ hnext ih =>
    obtain ⟨ps, hps⟩ := hnext
    obtain ⟨hev, hle⟩ := msg_even A cb tr hS ih hps
    have hE : (τ.push ((npProver A cb tr).next τ)).entries =
        τ.entries ++ [.msg (npMsg A cb tr τ.chals (τ.entries.length / 2))] := rfl
    refine ⟨ih.cb_eq, ?_, ?_, ?_, ?_⟩
    · rw [chals_push', hE, ih.len]; simp; omega
    · rw [hE]; simp; omega
    · intro k hk0
      rw [chals_push']
      have hk : k < (τ.entries ++ [Entry.msg (npMsg A cb tr τ.chals (τ.entries.length / 2))]).length := by
        rw [← hE]; exact hk0
      show (τ.entries ++ [Entry.msg (npMsg A cb tr τ.chals (τ.entries.length / 2))])[k]'hk = _
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      by_cases hk' : k < τ.entries.length
      · rw [List.getElem_append_left hk']; exact ih.ent k hk'
      · have hk2 : k = τ.entries.length := by omega
        subst hk2
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_cons_zero, entOf, hev, ite_true]
        rw [List.take_of_length_le (by rw [ih.len]; exact Nat.le_refl _)]
    · intro h8
      rw [chals_push']
      rw [hE] at h8; simp at h8
      exact ih.ood (by omega)
  | chal τ ood y _ hslot ih =>
    obtain ⟨hodd, hlt, h7⟩ := chal_odd A cb tr hS ih hslot
    have hE : (τ.pushChal (Bcs.Transport.decChal (F := Fp) ood y)).entries =
        τ.entries ++ [.chal (Bcs.Transport.decChal (F := Fp) ood y)] := rfl
    have hlenc := ih.len
    refine ⟨ih.cb_eq, ?_, ?_, ?_, ?_⟩
    · rw [chals_pushChal', hE]; simp; omega
    · rw [hE]; simp; omega
    · intro k hk0
      rw [chals_pushChal']
      have hk : k < (τ.entries ++ [Entry.chal (Bcs.Transport.decChal (F := Fp) ood y)]).length := by
        rw [← hE]; exact hk0
      show (τ.entries ++ [Entry.chal (Bcs.Transport.decChal (F := Fp) ood y)])[k]'hk = _
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      by_cases hk' : k < τ.entries.length
      · rw [List.getElem_append_left hk', ih.ent k hk']
        unfold entOf
        split
        · rw [List.take_append_of_le_length (by omega)]
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega)]
      · have hk2 : k = τ.entries.length := by omega
        subst hk2
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_cons_zero, entOf]
        rw [if_neg (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega), show τ.entries.length / 2 - τ.chals.length = 0 by
            omega]
        rfl
    · intro h8
      rw [chals_pushChal']
      rw [hE] at h8; simp at h8
      by_cases h7' : τ.entries.length = 7
      · have hb := h7 h7'
        subst hb
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          show 3 - τ.chals.length = 0 by omega]
        exact decChal_ood y
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
        exact ih.ood (by omega)

/-- At the query phase, a reachable transcript is the honest complete transcript. -/
theorem inv_query (hS : SchedFormStmt) (hP : MsgPrefixStmt) (hok : headerOk A dp (hdr A tr) = true)
    {τ : PT Fp8 (Oracle Fp)} (h : Inv A cb tr τ) (hq : (Vd A).AtQuery τ) :
    τ = honT A cb tr τ.chals ∧ τ.chals.length = nMsg A tr := by
  obtain ⟨hh, hlen⟩ := hq
  have hne : τ.entries ≠ [] := by
    intro he; rw [header_nil (τ := τ) he] at hh; cases hh
  rw [slots_of_header A tr (inv_header A cb tr h hne)] at hlen
  have hsl : (schedule A dp (hdr A tr)).length = 2 * nMsg A tr + 1 := by
    rw [hS A tr, List.length_append, length_slotsOf]; rfl
  rw [hsl] at hlen
  have hcl : τ.chals.length = nMsg A tr := by rw [h.len, hlen]; omega
  refine ⟨?_, hcl⟩
  have hfl : (fullEntries A cb tr τ.chals).length = 2 * nMsg A tr + 1 := by
    unfold fullEntries
    rw [List.length_append, length_flatMap_pair, List.length_range]; rfl
  cases τ with
  | mk cbτ es =>
    simp only [honT, PT.mk.injEq]
    simp only at hlen hcl
    refine ⟨h.cb_eq, List.ext_getElem? fun k => ?_⟩
    by_cases hk1 : k < es.length
    · rw [List.getElem?_eq_getElem hk1, h.ent k hk1]
      unfold fullEntries entOf
      by_cases hk : k < 2 * nMsg A tr
      · rw [List.getElem?_append_left (by rw [length_flatMap_pair, List.length_range]; exact hk),
          getElem?_flatMap_pair, List.getElem?_range (by omega)]
        simp only [Option.map_some]
        split
        · rw [hP A cb tr hok _ _ (by omega) (by omega)]
        · rfl
      · have hk' : k = 2 * nMsg A tr := by omega
        subst hk'
        rw [List.getElem?_append_right (by rw [length_flatMap_pair, List.length_range]; exact Nat.le_refl _),
          length_flatMap_pair, List.length_range, Nat.sub_self]
        rw [if_pos (by omega), show 2 * nMsg A tr / 2 = nMsg A tr by omega,
          hP A cb tr hok _ _ (Nat.le_refl _) (by omega)]
        rfl
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by
        show (fullEntries A cb tr (PT.chals ⟨cbτ, es⟩)).length ≤ k; rw [hfl]; omega)]

/-- Reachable transcripts are shaped. -/
theorem inv_shaped (hS : SchedFormStmt) (hF : MsgFitsStmt) (hok : (Vd A).headerOk (hdr A tr) = true)
    {τ : PT Fp8 (Oracle Fp)} (h : Inv A cb tr τ) : Shaped (Vd A) τ := by
  by_cases h0 : τ.entries = []
  · refine ⟨fun l hl => (by rw [header_nil h0] at hl; cases hl), by simp [h0], fun k hk => ?_⟩
    simp [h0] at hk
  have hh := inv_header A cb tr h h0
  have hsl : (schedule A dp (hdr A tr)).length = 2 * nMsg A tr + 1 := by
    rw [hS A tr, List.length_append, length_slotsOf]; rfl
  refine ⟨fun l hl => by rw [hh] at hl; cases hl; exact hok, ?_, fun k hk => ?_⟩
  · rw [slots_of_header A tr hh, hsl]; exact h.le
  · rw [slots_of_header A tr hh, sched_at A tr hS]
    have hkl := h.le
    rw [h.ent k hk]
    unfold entOf
    by_cases hk2 : k < 2 * nMsg A tr
    · rw [if_pos hk2]
      split
      · exact ⟨_, rfl, hF A cb tr _ _ (by omega)⟩
      · have hj : k / 2 < (slotPairs A tr).length := by unfold nMsg at hk2; omega
        rw [List.getElem?_eq_getElem hj]
        exact ⟨_, rfl, trivial⟩
    · have hk' : k = 2 * nMsg A tr := by omega
      rw [if_neg hk2, if_pos hk', if_pos (by omega)]
      refine ⟨_, rfl, ?_⟩
      have := hF A cb tr (τ.chals.take (k / 2)) (k / 2) (by omega)
      have hm : msgParts A tr (k / 2) = [.elems 2] := by
        simp [msgParts, show k / 2 = nMsg A tr by omega, nMsg]
      rw [hm] at this; exact this

theorem npMsg_header (cs : List Fp8) (j : Nat) (l : List Nat)
    (h : PartV.header l ∈ npMsg A cb tr cs j) : l = hdr A tr := by
  unfold npMsg at h
  split at h
  · simp at h; exact h
  · split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h
    · rename_i k _
      unfold kindMsg at h
      split at h
      · simp at h
      · split at h <;> simp at h
    · simp at h

end

/-- **Completeness of the np IOP** (corrected statement) from the components. -/
theorem npIopComplete_of (hS : SchedFormStmt) (hF : MsgFitsStmt) (hP : MsgPrefixStmt)
    (hG : GlobalStmt) (hL : LocalStmt) : NpIopCompleteStmt' := by
  intro A cb tr h32 hH hokV
  have hok : headerOk A dp (hdr A tr) = true := (verifier_headerOk hokV).1
  refine ⟨npProver A cb tr, rfl, ?_, ?_⟩
  · refine ⟨hokV, by simp [npProver, hdr, trHdr]; rfl, ?_, h32, fun τ hr =>
      inv_shaped A cb tr hS hF hokV (reach_inv A cb tr hS hr),
      fun τ hr hne => inv_header A cb tr (reach_inv A cb tr hS hr) hne,
      fun τ _ _ l hl => npMsg_header A cb tr _ _ l hl⟩
    intro h hm
    simp only [npProver, hdr, trHdr, List.mem_map, List.mem_range] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    have := headerOk_facts (A := A) (prm := dp) hok
    simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := hok
    have hmem : (A.tables[t], tr.log t) ∈ A.tables.zip (trHdr A tr) := by
      rw [List.mem_iff_getElem]
      exact ⟨t, by simp [trHdr]; omega, by simp [trHdr]⟩
    have := hall _ hmem
    simp only [dp, Params.default] at this
    omega
  · intro τ hr hq
    have hi := reach_inv A cb tr hS hr
    obtain ⟨he, hlen⟩ := inv_query A cb tr hS hP hok hi hq
    have hz := hi.ood (by
      have := hq.2
      rw [slots_of_header A tr (inv_header A cb tr hi (by
        intro h0; have h1 := hq.1; rw [header_nil (τ := τ) h0] at h1; cases h1))] at this
      rw [this, hS A tr]; simp [slotsOf, List.length_flatMap, slotPairs])
    refine ⟨?_, fun x hx => ?_⟩
    · rw [he]; exact hG A cb tr hH hok _ hlen hz
    · have hd : (Vd A).domSize τ = 2 ^ n0 A tr := by
        simp [IopSpec.domSize, inv_header A cb tr hi (by
          intro h0; have h1 := hq.1; rw [header_nil (τ := τ) h0] at h1; cases h1), n0]; rfl
      rw [hd] at hx
      rw [he]; exact hL A cb tr hH hok _ hlen hz x hx

end ZkFormal.Prover.Np
