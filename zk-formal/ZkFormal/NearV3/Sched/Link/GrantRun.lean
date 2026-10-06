import ZkFormal.NearV3.Sched.Link.SoundFin

/-!
# ZkFormal.NearV3.Sched.Link.GrantRun — the granted totals along the replay (stage E step a)

The memory's `w` column of a link address is the spec's `granted[l]`. This file has the spec side
of that link: `stAt` (the replay state at every time, `Link/MemRun.lean`) with its `granted` array.

* `GArr`: the four arrays the memory holds (`Arr`) together with `granted`;
* `tryGrant_garr`, **`stAt_slotG`**, **`stAt_endG`**: `stAt` agrees with the replay states
  (`stepSt`, `specSt … m`) on all four arrays;
* **`tryGrant_gget`**: under `GInv` (`Spec/Granted.lean`), `tryGrant` adds `bw` to `granted[l]`
  exactly when it grants (no `u64::MAX` saturation), and changes no other `granted` entry;
* `stAt_ginv`, `stAt_szOk`: `GInv` and the sizes hold at every `stAt t`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler

/-- The arrays the memory holds, with the granted totals. -/
def GArr (S : St) : Array Nat × Array Nat × Array Nat × Array Nat :=
  (S.senderBudget, S.receiverBudget, S.allowance, S.granted)

section
variable (n : Nat) (allowed : Array Bool)

theorem tryGrant_garr {S S' : St} (h : GArr S = GArr S') (l bw : Nat) :
    GArr (tryGrant n allowed S l bw).2 = GArr (tryGrant n allowed S' l bw).2 := by
  obtain ⟨sb, rb, al, g, rg⟩ := S
  obtain ⟨sb', rb', al', g', rg'⟩ := S'
  simp only [GArr, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  unfold tryGrant grantMore
  split
  · rfl
  · simp only
    split <;> rfl

/-- **What `tryGrant` does to `granted`** (no saturation under `GInv`). -/
theorem tryGrant_gget {S : St} (hG : GInv n 4500000 S) {l : Nat} (hl : l < S.granted.size) (bw x : Nat) :
    let d := allowed[l]! && decide (bw ≤ S.senderBudget[l / n]!) && decide (bw ≤ S.receiverBudget[l % n]!)
    (tryGrant n allowed S l bw).2.granted[x]! =
      (if d = true ∧ x = l then S.granted[x]! + bw else S.granted[x]!) := by
  intro d
  by_cases ha : allowed[l]! = true
  · by_cases hb : S.senderBudget[l / n]! < bw ∨ S.receiverBudget[l % n]! < bw
    · have hd : d = false := by
        simp only [d, ha, Bool.true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      have e : (tryGrant n allowed S l bw).2 = S := by
        unfold tryGrant; simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [if_pos hb]
      rw [e, hd]; simp
    · have hd : d = true := by
        simp only [d, ha, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega
      have hg : S.granted[l]! + bw ≤ u64Max := by
        have := hG l; have : (4500000 : Nat) ≤ u64Max := by decide
        omega
      have e : (tryGrant n allowed S l bw).2.granted = S.granted.set! l (S.granted[l]! + bw) := by
        unfold tryGrant grantMore
        simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [if_neg hb]
        simp only [hg, ↓reduceIte]
      rw [e, getElem!_set!_eq, hd]
      by_cases ex : x = l
      · subst ex; simp [hl]
      · rw [if_neg (fun c => ex c.1.symm), if_neg (fun c => ex c.2)]
  · have hd : d = false := by simp [d, ha]
    have e : (tryGrant n allowed S l bw).2 = S := by
      unfold tryGrant; simp [ha]
    rw [e, hd]; simp

end

section
variable (n : Nat) (allowed : Array Bool) (tr : Trace Fp) (tp f m : Nat) (st : St)

theorem stAt_ginv (h : GInv n 4500000 st) : ∀ t, GInv n 4500000 (stAt n allowed tr tp f m st t)
  | 0 => h
  | t + 1 => by
    simp only [stAt]
    split
    · exact (tryGrant_granted (by decide) allowed (stAt_ginv h t) _ _).1
    · exact stAt_ginv h t

theorem stAt_szOk (h : SzOk n st) : ∀ t, SzOk n (stAt n allowed tr tp f m st t)
  | 0 => h
  | t + 1 => by
    simp only [stAt]
    split
    · exact tryGrant_szOk allowed _ _ (stAt_szOk h t)
    · exact stAt_szOk h t

end

section
variable {pub : List Fp} {n : Nat} {allowed : Array Bool} {reqs : List Req} {tr : Trace Fp} {tp f m : Nat}
  {st : St}

/-- **The replay state at every entry slot, with `granted`.** -/
theorem stAt_slotG (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m)
    (hE : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      (∃ rest, (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).incs =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc :: rest) ∧
      (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).link =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link) :
    ∀ i, i < m → ∀ j, j ≤ cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      GArr (stAt n allowed tr tp f m st (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)) =
        GArr (stepSt n allowed reqs tr tp f st i j) := by
  intro i
  induction i with
  | zero =>
    intro hi j
    induction j with
    | zero =>
      intro _
      rw [Nat.add_zero, (I.first hi).1, stAt_pre hL hH I T0 (Nat.le_refl _)]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨⟨rest, hinc⟩, hlk⟩ := hE 0 hi j (by omega)
      rw [← Nat.add_assoc, stAt_some n allowed tr tp f m st (entAt_slot I hi (by omega))]
      show _ = GArr (stepE n allowed reqs _ _ _ _ _).1
      rw [stepE_fst n allowed reqs _ _ _ _ _ hinc hlk]
      exact tryGrant_garr n allowed (ih (by omega)) _ _
  | succ i ihi =>
    intro hi j
    induction j with
    | zero =>
      intro _
      rw [Nat.add_zero, (I.chain i hi).1, ihi (by omega) _ (Nat.le_refl _)]
      show _ = GArr (specSt n allowed reqs tr tp f st (i + 1))
      rw [specSt_succ]
    | succ j ih =>
      intro hj
      obtain ⟨⟨rest, hinc⟩, hlk⟩ := hE (i + 1) hi j (by omega)
      rw [← Nat.add_assoc, stAt_some n allowed tr tp f m st (entAt_slot I hi (by omega))]
      show _ = GArr (stepE n allowed reqs _ _ _ _ _).1
      rw [stepE_fst n allowed reqs _ _ _ _ _ hinc hlk]
      exact tryGrant_garr n allowed (ih (by omega)) _ _

end

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd f m : Nat}
  {P : InstPub} {allowed : Array Bool} {st : St}

namespace MemCtx
variable (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
include C

/-- **The simulation after all slots is the spec's final process state, with `granted`.** -/
theorem stAt_endG :
    GArr (stAt P.n allowed tr tp f m st (2 ^ 29)) = GArr (specSt P.n allowed (reqsOf P) tr tp f st m) := by
  have hHt := C.hHt
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    have hnone : ∀ t, 0 ≤ t → entAt tr tp f 0 t = none := by
      intro t _
      cases he : entAt tr tp f 0 t with
      | none => rfl
      | some p => obtain ⟨i, j⟩ := p; exact absurd (entAt_some he).1 (Nat.not_lt_zero _)
    have := C.stAt_from hnone (2 ^ 29)
    rw [Nat.zero_add] at this
    rw [this]; rfl
  · have hlt := (C.I.hdr (m - 1) (by omega)).2
    have hT0 : T0 = 1048576 := rfl
    have hA := stAt_slotG (n := P.n) (allowed := allowed) (reqs := reqsOf P) (st := st) C.hL C.hHt C.I
      (fun i hi j hj => by
        obtain ⟨⟨rest, h1, -⟩, h2, -⟩ := entry_inc C.hH C.O C.OS C.SP C.PO C.I rfl hi hj
        exact ⟨⟨rest, h1⟩, h2⟩) (m - 1) (by omega) _ (Nat.le_refl _)
    have hs := C.stAt_from (fun t ht => C.entAt_after h0 ht)
      (2 ^ 29 - (cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr))
    rw [show cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr +
      (2 ^ 29 - (cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr)) =
      2 ^ 29 by omega] at hs
    rw [hs, hA, show m = m - 1 + 1 by omega, specSt_succ, show m - 1 + 1 - 1 = m - 1 by omega]

end MemCtx

end

end ZkFormal.NearV3.Sched
