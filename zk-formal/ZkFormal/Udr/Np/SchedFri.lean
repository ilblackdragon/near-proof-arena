import ZkFormal.Udr.Np.Commits
import ZkFormal.Udr.Np.Facts

/-!
# ZkFormal.Udr.Np.SchedFri — oracles and clear-text parts of a shaped transcript

* `F2 R l l'`: pointwise relation of two lists;
* a shaped transcript's oracles fit the oracle parts of the schedule prefix
  (`sh_oracles_fit`), its clear-text parts have the scheduled lengths
  (`sh_elems_fit`);
* the schedule as `pre ++ friSchedule`; the prefix up to layer `c`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Pointwise relations -/

inductive F2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : F2 R [] []
  | cons {a b l l'} : R a b → F2 R l l' → F2 R (a :: l) (b :: l')

namespace F2
variable {α β : Type} {R : α → β → Prop}

theorem length_eq : ∀ {l : List α} {l' : List β}, F2 R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [t.length_eq]

theorem append : ∀ {l₁ l₂ : List α} {l₁' l₂' : List β}, F2 R l₁ l₁' → F2 R l₂ l₂' →
    F2 R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r t, h => .cons r (t.append h)

theorem get : ∀ {l : List α} {l' : List β}, F2 R l l' → ∀ k (hk : k < l.length) (hk' : k < l'.length),
    R l[k] l'[k]
  | _, _, .nil, k, hk, _ => absurd hk (by simp)
  | _, _, .cons r t, 0, _, _ => r
  | _, _, .cons r t, k + 1, hk, hk' => t.get k (by simp at hk; omega) (by simp at hk'; omega)

end F2

/-! ## Oracle and clear-text parts -/

def partOr : Part → Option (List (Nat × Nat))
  | .oracle m => some m
  | _ => none

def partEl : Part → Option Nat
  | .elems n => some n
  | _ => none

def slotOr : Slot → List (List (Nat × Nat))
  | .msg ps => ps.filterMap partOr
  | .chal _ => []

def slotEl : Slot → List Nat
  | .msg ps => ps.filterMap partEl
  | .chal _ => []

def pvOr : PartV Fp8 (Oracle Fp) → Option (Oracle Fp)
  | .oracle o => some o
  | _ => none

def pvEl : PartV Fp8 (Oracle Fp) → Option (List Fp8)
  | .elems xs => some xs
  | _ => none

def entOr : Entry Fp8 (Oracle Fp) → List (Oracle Fp)
  | .msg ps => ps.filterMap pvOr
  | .chal _ => []

def entEl : Entry Fp8 (Oracle Fp) → List (List Fp8)
  | .msg ps => ps.filterMap pvEl
  | .chal _ => []

theorem oracles_eq (τ : PTn) : τ.oracles = τ.entries.flatMap entOr := by
  simp only [PT.oracles]; congr 1; funext e; rcases e with ps | c
  · simp only [entOr]; congr 1; funext p; rcases p <;> rfl
  · rfl

theorem elems_eq (τ : PTn) : τ.elems = τ.entries.flatMap entEl := by
  simp only [PT.elems]; congr 1; funext e; rcases e with ps | c
  · simp only [entEl]; congr 1; funext p; rcases p <;> rfl
  · rfl

/-- An oracle fits its shape. -/
def OFit (o : Oracle Fp) (mats : List (Nat × Nat)) : Prop := PartV.Fits (K := Fp8) (.oracle o) (.oracle mats)

theorem parts_fit_or : ∀ (ps : List (PartV Fp8 (Oracle Fp))) (parts : List Part), ps.length = parts.length →
    (∀ k (hk : k < ps.length), ∃ pt, parts[k]? = some pt ∧ PartV.Fits ps[k] pt) →
    F2 OFit (ps.filterMap pvOr) (parts.filterMap partOr)
  | [], [], _, _ => .nil
  | p :: ps, pt :: parts, hl, h => by
    have ih := parts_fit_or ps parts (by simpa using hl) fun k hk => by
      obtain ⟨pt, h1, h2⟩ := h (k + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at h2
      exact ⟨pt, by simpa using h1, h2⟩
    obtain ⟨pt', hpt', hf⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hpt'
    subst hpt'
    simp only [List.getElem_cons_zero] at hf
    rcases p with l | o | xs <;> rcases pt with n | mats | n <;>
      first | exact absurd hf id | (simp only [List.filterMap_cons, pvOr, partOr]; first | exact ih | exact .cons hf ih)

theorem parts_fit_el : ∀ (ps : List (PartV Fp8 (Oracle Fp))) (parts : List Part), ps.length = parts.length →
    (∀ k (hk : k < ps.length), ∃ pt, parts[k]? = some pt ∧ PartV.Fits ps[k] pt) →
    F2 (fun (xs : List Fp8) n => xs.length = n) (ps.filterMap pvEl) (parts.filterMap partEl)
  | [], [], _, _ => .nil
  | p :: ps, pt :: parts, hl, h => by
    have ih := parts_fit_el ps parts (by simpa using hl) fun k hk => by
      obtain ⟨pt, h1, h2⟩ := h (k + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at h2
      exact ⟨pt, by simpa using h1, h2⟩
    obtain ⟨pt', hpt', hf⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hpt'
    subst hpt'
    simp only [List.getElem_cons_zero] at hf
    rcases p with l | o | xs <;> rcases pt with n | mats | n <;>
      first | exact absurd hf id | (simp only [List.filterMap_cons, pvEl, partEl]; first | exact ih | exact .cons hf ih)

theorem entries_fit : ∀ (es : List (Entry Fp8 (Oracle Fp))) (sl : List Slot), es.length ≤ sl.length →
    (∀ k (hk : k < es.length), ∃ s, sl[k]? = some s ∧ Entry.Fits es[k] s) →
    F2 OFit (es.flatMap entOr) ((sl.take es.length).flatMap slotOr) ∧
    F2 (fun (xs : List Fp8) n => xs.length = n) (es.flatMap entEl) ((sl.take es.length).flatMap slotEl)
  | [], _, _, _ => by simp; exact ⟨.nil, .nil⟩
  | e :: es, s :: sl, hl, h => by
    obtain ⟨ih1, ih2⟩ := entries_fit es sl (by simpa using hl) fun k hk => by
      obtain ⟨pt, h1, h2⟩ := h (k + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at h2
      exact ⟨pt, by simpa using h1, h2⟩
    obtain ⟨s', hs', hf⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs'
    subst hs'
    simp only [List.getElem_cons_zero] at hf
    simp only [List.length_cons, List.take_succ_cons, List.flatMap_cons]
    rcases e with ps | c <;> rcases s with parts | b
    · obtain ⟨hl', hk⟩ := hf
      exact ⟨(parts_fit_or ps parts hl' hk).append ih1, (parts_fit_el ps parts hl' hk).append ih2⟩
    · exact absurd hf id
    · exact absurd hf id
    · exact ⟨ih1, ih2⟩
  | _ :: _, [], hl, _ => by simp at hl

section
variable (A : Air) (prm : Params)

/-- The oracles of a shaped transcript fit the schedule prefix. -/
theorem sh_fit (τ : PTn) (hs : Shaped (Vnp A prm) τ) :
    F2 OFit τ.oracles (((Vnp A prm).slots τ |>.take τ.entries.length).flatMap slotOr) ∧
    F2 (fun (xs : List Fp8) n => xs.length = n) τ.elems
      (((Vnp A prm).slots τ |>.take τ.entries.length).flatMap slotEl) := by
  rw [oracles_eq, elems_eq]
  exact entries_fit _ _ hs.2.1 fun k hk => hs.2.2 k hk

/-! ## The schedule -/

/-- The slots before the FRI part. -/
def preSlots (hdr : List Nat) : List Slot :=
  let lay := layout A prm hdr
  let finals := (lay.map fun L => L.sendG + L.recvG).sum
  let ood := (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum
  [.msg [.header A.tables.length, .oracle (lay.map fun L => (L.lde, L.width))], .chal false,
   .msg [], .chal false,
   .msg [.oracle (lay.map fun L => (L.lde, 8 * L.aux)), .elems finals], .chal false,
   .msg [.oracle (lay.map fun L => (L.lde, 8 * L.quot))], .chal true,
   .msg [.elems ood], .chal false] ++
  ((List.range (batchRounds lay - 1)).flatMap fun _ => [.msg [], .chal false])

theorem schedule_eq (hdr : List Nat) : schedule A prm hdr = preSlots A prm hdr ++ friSchedule A prm hdr := rfl

theorem pairs_length (n : Nat) :
    ((List.range n).flatMap fun _ => ([.msg [], .chal false] : List Slot)).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega

theorem pairs_or (n : Nat) :
    ((List.range n).flatMap fun _ => ([.msg [], .chal false] : List Slot)).flatMap slotOr = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih]; rfl

theorem pairs_el (n : Nat) :
    ((List.range n).flatMap fun _ => ([.msg [], .chal false] : List Slot)).flatMap slotEl = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih]; rfl

theorem preSlots_length (hdr : List Nat) :
    (preSlots A prm hdr).length = 2 * (4 + batchRounds (layout A prm hdr)) := by
  simp only [preSlots, List.length_append, pairs_length]
  have : 1 ≤ batchRounds (layout A prm hdr) := Nat.le_max_left _ _
  simp only [List.length_cons, List.length_nil]
  omega

theorem preSlots_or (hdr : List Nat) : ((preSlots A prm hdr).flatMap slotOr).length = 3 := by
  simp only [preSlots, List.flatMap_append, List.length_append, pairs_or]
  rfl

theorem preSlots_el (hdr : List Nat) : ((preSlots A prm hdr).flatMap slotEl).length = 2 := by
  simp only [preSlots, List.flatMap_append, List.length_append, pairs_el]
  rfl

end
end ZkFormal.Udr.Np
