import NearSpecV3.Successor.TierO3Dec

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5a — the pipeline relation of the two runs

With `globalActions` off the pipeline decodes stored receipts with the D2 codec and sets
`uncertain` where that codec excludes; the run with the flag on decodes them. The two pipes are
then related by **`PipeRel pL pU`: equal, or the lower one is `uncertain` and has noted a race
wherever the upper one has** (`raced`, G3 2026-10-31: a race is noted per executed call and decided
at the end of the run, `StorageExecution.raceCheck`). Everything the engine proof needs about the
pipe is in this file:

* `PipeRel.det`: where the lower pipe calls a deploy-served code `deterministic`, so does the upper
  one (an uncertain pipe is never deterministic).
* `PipeRel.raced`: where the lower pipe noted no race, neither did the upper one.
* `PipeFn f g`: `f` and `g` map related pipes to related pipes. Proved for every pipe update of
  `StorageExecution` (`pipeFn_*`), from: nothing resets `uncertain` (`*_unc`), the scheduler never
  touches `raced` (`*_raced`), and on equal pipes the lower update with the D2 decoder is the upper
  one with the global decoder, or uncertain (`*_rel`); and for the per-call race note
  (`pipeFn_noteRace`).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 Pipeline

/-- The pipes of the two runs: equal, or the lower one (`globalActions` off) is uncertain and has
noted a race wherever the upper one has. -/
def PipeRel (pL pU : Pipe) : Prop :=
  pL = pU ∨ (pL.uncertain = true ∧ (pU.raced = true → pL.raced = true))

theorem PipeRel.refl (p : Pipe) : PipeRel p p := Or.inl rfl

theorem PipeRel.det {pL pU : Pipe} (h : PipeRel pL pU) (rid : Bytes) (idx : Nat) (hash : Bytes)
    (hd : pL.deterministic rid idx hash = true) : pU.deterministic rid idx hash = true := by
  rcases h with rfl | ⟨hu, _⟩
  · exact hd
  · unfold Pipe.deterministic at hd
    rw [hu] at hd
    simp at hd

/-- Where the lower run noted no race, the upper one noted none either. -/
theorem PipeRel.raced {pL pU : Pipe} (h : PipeRel pL pU) (hL : pL.raced = false) : pU.raced = false := by
  rcases h with rfl | ⟨_, hr⟩
  · exact hL
  · cases hU : pU.raced
    · rfl
    · have := hr hU; rw [hL] at this; cases this

/-- Two pipe updates map related pipes to related pipes. -/
def PipeFn (f g : Pipe → Pipe) : Prop := ∀ pL pU, PipeRel pL pU → PipeRel (f pL) (g pU)

/-- Decoder agreement: where the lower decoder decodes, the upper one decodes the same. -/
def DecLe {β : Type} (dL dU : Bytes → Except String β) : Prop := ∀ b v, dL b = .ok v → dU b = .ok v

/-! ## Nothing resets `uncertain` -/

theorem submitActions_unc (o : Ovl) (rid recv : Bytes) :
    ∀ (l : List Act) (p : Pipe) (acct : Option (Option Acct)) (i : Nat) (any : Bool),
      p.uncertain = true → (submitActions o rid recv p acct i any l).1.uncertain = true
  | [], p, _, _, _, h => h
  | a :: rest, p, acct, i, any, h => by
    have ih := fun p acct i any (h : Pipe.uncertain p = true) => submitActions_unc o rid recv rest p acct i any h
    unfold submitActions
    rcases acct with _ | acct
    · cases hpk : peek o (kAccount recv) with
      | none =>
        split <;> (try simp only [hpk]) <;> (repeat' split) <;> (try dsimp only) <;>
          first | exact h | exact ih _ _ _ _ h | exact ih _ _ _ _ rfl
      | some v =>
        cases v with
        | none =>
          split <;> (try simp only [hpk]) <;> (repeat' split) <;> (try dsimp only) <;>
            first | exact h | exact ih _ _ _ _ h | exact ih _ _ _ _ rfl
        | some raw =>
          cases hd : decodeAcct raw <;>
          (split <;> (try simp only [hpk, hd]) <;> (repeat' split) <;> (try dsimp only) <;>
            first | exact h | exact ih _ _ _ _ h | exact ih _ _ _ _ rfl)
    · split <;> (try dsimp only) <;> (repeat' split) <;> (try dsimp only) <;>
        first | exact h | exact ih _ _ _ _ h | exact ih _ _ _ _ rfl

theorem submitRcpt_unc (o : Ovl) (p : Pipe) (r : Rcpt) (h : p.uncertain = true) :
    (submitRcpt o p r).1.uncertain = true := by
  unfold submitRcpt
  split
  · exact h
  · split
    · exact submitActions_unc _ _ _ _ _ _ _ _ h
    · exact h

theorem handle_unc (d : Bytes → Except String Rcpt) (o : Ovl) (p : Pipe) (r : Rcpt)
    (h : p.uncertain = true) : (handle d o p r).1.uncertain = true := by
  unfold handle
  dsimp only
  repeat' split
  all_goals first | exact h | rfl | exact submitRcpt_unc _ _ _ h

theorem schedule_unc (d : Bytes → Except String Rcpt) (o : Ovl) :
    ∀ (l : List Rcpt) (p : Pipe), p.uncertain = true → (schedule d o p l).1.uncertain = true
  | [], p, h => h
  | r :: rest, p, h => by
    unfold schedule
    dsimp only
    split
    · exact handle_unc d o p r h
    · exact schedule_unc d o rest _ (handle_unc d o p r h)

theorem peekDelayed_unc (ds : Bytes → Except String Stored) (L : Layout) (own : Nat) (o : Ovl) :
    ∀ (fuel i next : Nat) (p : Pipe), p.uncertain = true →
      (peekDelayed ds L own o p fuel i next).1.uncertain = true
  | 0, _, _, _, h => h
  | fuel + 1, i, next, p, h => by
    unfold peekDelayed
    split
    · exact h
    · have ih := peekDelayed_unc ds L own o fuel (i + 1) next p h
      split
      · split
        · revert ih
          generalize peekDelayed ds L own o p fuel (i + 1) next = q
          rcases q with ⟨q, rest⟩
          intro ih; exact ih
        · rfl
      · exact h

/-! ## The scheduler never touches `raced` -/

theorem submitActions_raced (o : Ovl) (rid recv : Bytes) (b : Bool) :
    ∀ (l : List Act) (p : Pipe) (acct : Option (Option Acct)) (i : Nat) (any : Bool),
      p.raced = b → (submitActions o rid recv p acct i any l).1.raced = b
  | [], p, _, _, _, h => h
  | a :: rest, p, acct, i, any, h => by
    have ih := fun p acct i any (h : Pipe.raced p = b) => submitActions_raced o rid recv b rest p acct i any h
    unfold submitActions
    rcases acct with _ | acct
    · cases hpk : peek o (kAccount recv) with
      | none =>
        split <;> (try simp only [hpk]) <;> (repeat' split) <;> (try dsimp only) <;>
          first | exact h | exact ih _ _ _ _ h
      | some v =>
        cases v with
        | none =>
          split <;> (try simp only [hpk]) <;> (repeat' split) <;> (try dsimp only) <;>
            first | exact h | exact ih _ _ _ _ h
        | some raw =>
          cases hd : decodeAcct raw <;>
          (split <;> (try simp only [hpk, hd]) <;> (repeat' split) <;> (try dsimp only) <;>
            first | exact h | exact ih _ _ _ _ h)
    · split <;> (try dsimp only) <;> (repeat' split) <;> (try dsimp only) <;>
        first | exact h | exact ih _ _ _ _ h

theorem submitRcpt_raced (o : Ovl) (p : Pipe) (r : Rcpt) (b : Bool) (h : p.raced = b) :
    (submitRcpt o p r).1.raced = b := by
  unfold submitRcpt
  split
  · exact h
  · split
    · exact submitActions_raced _ _ _ _ _ _ _ _ _ h
    · exact h

theorem handle_raced (d : Bytes → Except String Rcpt) (o : Ovl) (p : Pipe) (r : Rcpt) (b : Bool)
    (h : p.raced = b) : (handle d o p r).1.raced = b := by
  unfold handle
  dsimp only
  repeat' split
  all_goals first | exact h | exact submitRcpt_raced _ _ _ _ h

theorem schedule_raced (d : Bytes → Except String Rcpt) (o : Ovl) (b : Bool) :
    ∀ (l : List Rcpt) (p : Pipe), p.raced = b → (schedule d o p l).1.raced = b
  | [], p, h => h
  | r :: rest, p, h => by
    unfold schedule
    dsimp only
    split
    · exact handle_raced d o p r b h
    · exact schedule_raced d o b rest _ (handle_raced d o p r b h)

theorem peekDelayed_raced (ds : Bytes → Except String Stored) (L : Layout) (own : Nat) (o : Ovl) (b : Bool) :
    ∀ (fuel i next : Nat) (p : Pipe), p.raced = b →
      (peekDelayed ds L own o p fuel i next).1.raced = b
  | 0, _, _, _, h => h
  | fuel + 1, i, next, p, h => by
    unfold peekDelayed
    split
    · exact h
    · have ih := peekDelayed_raced ds L own o b fuel (i + 1) next p h
      split
      · split
        · revert ih
          generalize peekDelayed ds L own o p fuel (i + 1) next = q
          rcases q with ⟨q, rest⟩
          intro ih; exact ih
        · exact h
      · exact h

/-! ## Equal pipes: the lower update is the upper one, or uncertain -/

theorem handle_rel (dL dU : Bytes → Except String Rcpt) (hd : DecLe dL dU) (o : Ovl) (p : Pipe) (r : Rcpt) :
    handle dL o p r = handle dU o p r ∨ (handle dL o p r).1.uncertain = true := by
  unfold handle
  dsimp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | (right; rfl)
    | skip
  all_goals (rename_i hl _ _ hu; have hx := hd _ _ hl; rw [hu] at hx; cases hx; try exact Or.inl rfl)

theorem schedule_rel (dL dU : Bytes → Except String Rcpt) (hd : DecLe dL dU) (o : Ovl) :
    ∀ (l : List Rcpt) (p : Pipe),
      schedule dL o p l = schedule dU o p l ∨ (schedule dL o p l).1.uncertain = true
  | [], p => Or.inl rfl
  | r :: rest, p => by
    unfold schedule
    rcases handle_rel dL dU hd o p r with h | h
    · rw [h]
      generalize handle dU o p r = q
      rcases q with ⟨p', ok⟩
      dsimp only
      cases ok
      · rcases schedule_rel dL dU hd o rest p' with h2 | h2
        · rw [h2]; exact Or.inl rfl
        · right
          revert h2
          generalize schedule dL o p' rest = s
          rcases s with ⟨s1, s2, s3⟩
          intro h2; exact h2
      · exact Or.inl rfl
    · right
      revert h
      generalize handle dL o p r = q
      rcases q with ⟨p', ok⟩
      intro h
      dsimp only at h ⊢
      cases ok
      · have h2 := schedule_unc dL o rest p' h
        revert h2
        generalize schedule dL o p' rest = s
        rcases s with ⟨s1, s2, s3⟩
        intro h2; exact h2
      · exact h

theorem peekDelayed_rel (dL dU : Bytes → Except String Stored) (hd : DecLe dL dU) (L : Layout) (own : Nat)
    (o : Ovl) : ∀ (fuel i next : Nat) (p : Pipe),
      peekDelayed dL L own o p fuel i next = peekDelayed dU L own o p fuel i next ∨
        (peekDelayed dL L own o p fuel i next).1.uncertain = true
  | 0, _, _, _ => Or.inl rfl
  | fuel + 1, i, next, p => by
    unfold peekDelayed
    split
    · exact Or.inl rfl
    · split
      · rename_i b _
        cases hl : dL b with
        | error e => right; rfl
        | ok st =>
          rw [hd _ _ hl]
          dsimp only
          rcases peekDelayed_rel dL dU hd L own o fuel (i + 1) next p with h2 | h2
          · rw [h2]; exact Or.inl rfl
          · right
            revert h2
            generalize peekDelayed dL L own o p fuel (i + 1) next = s
            rcases s with ⟨s1, s2⟩
            intro h2; exact h2
      · exact Or.inl rfl

/-! ## The pipe updates of `StorageExecution` -/

theorem PipeFn.of_unc {f g : Pipe → Pipe} (hu : ∀ p, p.uncertain = true → (f p).uncertain = true)
    (hrf : ∀ p b, p.raced = b → (f p).raced = b) (hrg : ∀ p b, p.raced = b → (g p).raced = b)
    (he : ∀ p, f p = g p ∨ (f p).uncertain = true) : PipeFn f g := by
  intro pL pU h
  rcases h with rfl | ⟨h, hr⟩
  · rcases he pL with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1, fun hg => ?_⟩
      rw [hrf pL _ rfl]; rw [hrg pL _ rfl] at hg; exact hg
  · refine Or.inr ⟨hu pL h, fun hg => ?_⟩
    rw [hrf pL _ rfl]; rw [hrg pU _ rfl] at hg; exact hr hg

theorem PipeFn.same (f : Pipe → Pipe) (hu : ∀ p, p.uncertain = true → (f p).uncertain = true)
    (hr : ∀ p b, p.raced = b → (f p).raced = b) :
    PipeFn f f := PipeFn.of_unc hu hr hr fun _ => Or.inl rfl

theorem pipeFn_startReceipt : PipeFn startReceipt startReceipt :=
  PipeFn.same _ (fun _ h => h) fun _ _ h => h
theorem pipeFn_recordDeploys (codes : List Bytes) :
    PipeFn (·.recordDeploys codes) (·.recordDeploys codes) := PipeFn.same _ (fun _ h => h) fun _ _ h => h
theorem pipeFn_next (n : Option Nat) : PipeFn (fun p => { p with next := n }) (fun p => { p with next := n }) :=
  PipeFn.same _ (fun _ h => h) fun _ _ h => h

/-- The per-call race note (`StorageExecution.functionCallRecorded`): the lower pipe, uncertain, is
never `deterministic`, so it notes a race at every deploy-served call the upper one notes. -/
theorem pipeFn_noteRace (rid : Bytes) (idx : Nat) (hash : Bytes) (served : Bool) :
    PipeFn (Pipe.noteRace rid idx hash served) (Pipe.noteRace rid idx hash served) := by
  intro pL pU h
  rcases h with rfl | ⟨hu, hr⟩
  · exact Or.inl rfl
  · have hd : pL.deterministic rid idx hash = false := by
      unfold Pipe.deterministic; rw [hu]; rfl
    right
    unfold Pipe.noteRace
    rw [hd]
    cases served
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hu, hr⟩
    · simp only [Bool.not_false, Bool.and_self, ↓reduceIte, Bool.true_and]
      exact ⟨hu, fun _ => trivial⟩

theorem startList_raced (d : Bytes → Except String Rcpt) (o : Ovl) (l : List Rcpt) (p : Pipe) (b : Bool)
    (h : p.raced = b) : (startList d o p l).raced = b := by
  unfold startList
  have h2 := schedule_raced d o b l p h
  revert h2
  generalize schedule d o p l = s
  rcases s with ⟨s1, s2, s3⟩
  intro h2; exact h2

theorem stepList_raced (d : Bytes → Except String Rcpt) (o : Ovl) (p : Pipe) (b : Bool)
    (h : p.raced = b) : (stepList d o p).raced = b := by
  unfold stepList
  split
  · exact h
  · split
    · have h2 := schedule_raced d o b p.look p h
      revert h2
      generalize schedule d o p p.look = s
      rcases s with ⟨s1, s2, s3⟩
      intro h2; exact h2
    · exact h

theorem startList_unc (d : Bytes → Except String Rcpt) (o : Ovl) (l : List Rcpt) (p : Pipe)
    (h : p.uncertain = true) : (startList d o p l).uncertain = true := by
  unfold startList
  have h2 := schedule_unc d o l p h
  revert h2
  generalize schedule d o p l = s
  rcases s with ⟨s1, s2, s3⟩
  intro h2; exact h2

theorem pipeFn_startList (dL dU : Bytes → Except String Rcpt) (hd : DecLe dL dU) (o : Ovl) (l : List Rcpt) :
    PipeFn (startList dL o · l) (startList dU o · l) := by
  refine PipeFn.of_unc (fun p h => startList_unc dL o l p h) (fun p b h => startList_raced dL o l p b h)
    (fun p b h => startList_raced dU o l p b h) fun p => ?_
  unfold startList
  rcases schedule_rel dL dU hd o l p with h | h
  · rw [h]; exact Or.inl rfl
  · right
    revert h
    generalize schedule dL o p l = s
    rcases s with ⟨s1, s2, s3⟩
    intro h; exact h

theorem pipeFn_stepList (dL dU : Bytes → Except String Rcpt) (hd : DecLe dL dU) (o : Ovl) :
    PipeFn (stepList dL o) (stepList dU o) := by
  refine PipeFn.of_unc (fun p h => ?_) (fun p b h => stepList_raced dL o p b h)
    (fun p b h => stepList_raced dU o p b h) fun p => ?_
  · unfold stepList
    split
    · exact h
    · split
      · have h2 := schedule_unc dL o p.look p h
        revert h2
        generalize schedule dL o p p.look = s
        rcases s with ⟨s1, s2, s3⟩
        intro h2; exact h2
      · exact h
  · unfold stepList
    split
    · exact Or.inl rfl
    · split
      · rcases schedule_rel dL dU hd o p.look p with h | h
        · rw [h]; exact Or.inl rfl
        · right
          revert h
          generalize schedule dL o p p.look = s
          rcases s with ⟨s1, s2, s3⟩
          intro h; exact h
      · exact Or.inl rfl

/-- The pipe update of `scheduleDelayed`. -/
def schedFn (decode : Bytes → Except String Rcpt) (ds : Bytes → Except String Stored) (L : Layout)
    (own : Nat) (o : Ovl) (fuel first next : Nat) (p : Pipe) : Pipe :=
  let (p, look) := Pipeline.peekDelayed ds L own o p fuel first next
  let (p, _, next) := Pipeline.schedule decode o p look
  { p with next }

theorem schedFn_unc (decode : Bytes → Except String Rcpt) (ds : Bytes → Except String Stored) (L : Layout)
    (own : Nat) (o : Ovl) (fuel first next : Nat) (p : Pipe) (h : p.uncertain = true) :
    (schedFn decode ds L own o fuel first next p).uncertain = true := by
  unfold schedFn
  have h1 := peekDelayed_unc ds L own o fuel first next p h
  revert h1
  generalize peekDelayed ds L own o p fuel first next = q
  rcases q with ⟨q, look⟩
  intro h1
  dsimp only
  have h2 := schedule_unc decode o look q h1
  revert h2
  generalize schedule decode o q look = s
  rcases s with ⟨s1, s2, s3⟩
  intro h2; exact h2

theorem schedFn_raced (decode : Bytes → Except String Rcpt) (ds : Bytes → Except String Stored) (L : Layout)
    (own : Nat) (o : Ovl) (fuel first next : Nat) (p : Pipe) (b : Bool) (h : p.raced = b) :
    (schedFn decode ds L own o fuel first next p).raced = b := by
  unfold schedFn
  have h1 := peekDelayed_raced ds L own o b fuel first next p h
  revert h1
  generalize peekDelayed ds L own o p fuel first next = q
  rcases q with ⟨q, look⟩
  intro h1
  dsimp only
  have h2 := schedule_raced decode o b look q h1
  revert h2
  generalize schedule decode o q look = s
  rcases s with ⟨s1, s2, s3⟩
  intro h2; exact h2

theorem pipeFn_sched (dL dU : Bytes → Except String Rcpt) (hd : DecLe dL dU)
    (sL sU : Bytes → Except String Stored) (hs : DecLe sL sU) (L : Layout) (own : Nat) (o : Ovl)
    (fuel first next : Nat) :
    PipeFn (schedFn dL sL L own o fuel first next) (schedFn dU sU L own o fuel first next) := by
  refine PipeFn.of_unc (fun p h => schedFn_unc _ _ _ _ _ _ _ _ p h)
    (fun p b h => schedFn_raced _ _ _ _ _ _ _ _ p b h) (fun p b h => schedFn_raced _ _ _ _ _ _ _ _ p b h)
    fun p => ?_
  rcases peekDelayed_rel sL sU hs L own o fuel first next p with h | h
  · unfold schedFn
    rw [← h]
    generalize peekDelayed sL L own o p fuel first next = q
    rcases q with ⟨q, look⟩
    dsimp only
    rcases schedule_rel dL dU hd o look q with h2 | h2
    · rw [h2]; exact Or.inl rfl
    · right
      revert h2
      generalize schedule dL o q look = s
      rcases s with ⟨s1, s2, s3⟩
      intro h2; exact h2
  · right
    unfold schedFn
    revert h
    generalize peekDelayed sL L own o p fuel first next = q
    rcases q with ⟨q, look⟩
    intro h
    dsimp only at h ⊢
    have h2 := schedule_unc dL o look q h
    revert h2
    generalize schedule dL o q look = s
    rcases s with ⟨s1, s2, s3⟩
    intro h2; exact h2

theorem decLe_storedRcpt (what : String) :
    DecLe (fun b => decodeStoredRcpt b what) (fun b => GlobalCodecs.decodeStoredRcptGlobal b what) :=
  fun b v h => (Codec.decodeStoredRcpt_ref b what).ok v h

theorem decLe_stored : DecLe decodeStored GlobalCodecs.decodeStoredGlobal :=
  fun b v h => (Codec.decodeStored_ref b).ok v h

#print axioms PipeRel.det
#print axioms PipeRel.raced
#print axioms pipeFn_noteRace
#print axioms pipeFn_startList
#print axioms pipeFn_stepList
#print axioms pipeFn_sched

end NearSpecV3.Successor
