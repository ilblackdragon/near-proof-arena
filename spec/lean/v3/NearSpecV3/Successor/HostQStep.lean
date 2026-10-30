import NearSpecV3.Successor.HostQArms

/-!
# W12 / O3 — the lower run keeps its invariant, instruction by instruction and over a whole run

`LowQ` (`HostQArms.lean`): global-actions flag off, trie-backed store, no raw action in the log.
`QRes r`: the state carried by a step result satisfies `LowQ` (an exclusion carries none).

* `QRes_callHost`: a host call from a `LowQ` state. On a trie-backed state with the flag off,
  `callHost` excludes every `realOodHosts` name, so only arms outside `globalPromiseHosts` run
  (`HQ_dispatchArm`).
* `QRes_exec`, `QRes_step`, `QRes_run`: every instruction (the non-call ones by `X_exec`, read at
  `setX s`), every step, every run.
* `globalHyp`: O3's per-call hypothesis `CallHyp XG none (some true) LowQ` (`callHost_RR_global`).
-/

namespace NearSpecV3.Successor.HostComm
open NearSpecV3.Wasm

/-- The state of a step result satisfies `LowQ`. -/
def QRes : Res → Prop
  | .cont s => LowQ s
  | .fin s => LowQ s
  | .abort s _ => LowQ s
  | .unmodeled _ => True

theorem QRes_mapRes {s : St} (hq : LowQ s) (r : Res) : QRes (mapRes (setX s) r) := by
  cases r with
  | cont t => exact hq.ofSetX t
  | fin t => exact hq.ofSetX t
  | abort t e => exact hq.ofSetX t
  | unmodeled w => trivial

/-- A result that is its own image under `setX s`. -/
theorem QRes_of_eq {s : St} (hq : LowQ s) {r : Res} (e : r = mapRes (setX s) r) : QRes r := by
  rw [e]; exact QRes_mapRes hq r

theorem LowQ.ofSync {s s' : St} (hq : LowQ s) (e : sync s = .ok s') : LowQ s' := by
  have h := X_sync (q0 := s) (s := s)
  rw [setX_self, e] at h
  injection h with h2
  rw [h2]; exact hq.ofSetX _

theorem LowQ.ofSetFrame {s : St} (hq : LowQ s) (f : Frame) : LowQ (setFrame s f) := by
  have h := X_setFrame (q0 := s) (s := s) f
  rw [setX_self] at h
  rw [h]; exact hq.ofSetX _

theorem QRes_enter (p : Prepared) {s : St} (hq : LowQ s) (fi : Nat) : QRes (enter p s fi) := by
  have h := X_enter (q0 := s) (s := s) p fi
  rw [setX_self] at h
  exact QRes_of_eq hq h

theorem QRes_charge {s : St} (hq : LowQ s) (fee : Fee) (c : Nat) : QRes (charge s fee c) := by
  have h := X_charge (q0 := s) (s := s) fee c
  rw [setX_self] at h
  exact QRes_of_eq hq h

theorem globalPromiseHosts_contains_false (name : String)
    (hro : ¬ realOodHosts.contains name = true) : globalPromiseHosts.contains name = false := by
  cases h : globalPromiseHosts.contains name
  · rfl
  · exact absurd (globalPromiseHosts_realOod name h) hro

/-- **A host call keeps the invariant.** -/
theorem QRes_callHost {s : St} (hq : LowQ s) (name : String) : QRes (callHost s name) := by
  unfold callHost
  rw [hq.ga, hq.real]
  by_cases hro : realOodHosts.contains name = true
  · rw [if_pos (by rw [hro]; rfl)]; trivial
  have hgp := globalPromiseHosts_contains_false name hro
  have hro' : realOodHosts.contains name = false := by simpa using hro
  rw [if_neg (by rw [hro']; simp)]
  cases hsy : sync s with
  | error e => trivial
  | ok s' =>
    have hq' := hq.ofSync hsy
    simp only
    cases hd : dispatchArm s' name with
    | none => trivial
    | some h =>
      simp only
      have hh := HQ_dispatchArm s' name h hd hgp s' hq'
      revert hh
      cases h.run s' with
      | ok a t => intro hh; exact LowQ.of hh rfl (Or.inr rfl) rfl
      | error e t =>
        intro hh
        simp only
        split
        · trivial
        · exact hh

theorem QRes_callFunc (cfg : NearCfg) (p : Prepared) {s : St} (hq : LowQ s) (fi : Nat) :
    QRes (callFunc cfg p s fi) := by
  unfold callFunc
  split
  · exact QRes_callHost hq _
  · exact QRes_enter p hq fi

set_option maxHeartbeats 10000000 in
theorem QRes_exec (cfg : NearCfg) (p : Prepared) {s : St} (hq : LowQ s) (f : Frame) (pf : PFunc)
    (i : Instr) : QRes (exec cfg p s f pf i) := by
  by_cases h1 : ∃ fi, i = .call fi
  · obtain ⟨fi, rfl⟩ := h1
    simp only [exec]
    exact QRes_callFunc cfg p (hq.ofSetFrame _) fi
  by_cases h2 : ∃ ty y, i = .callIndirect ty y
  · obtain ⟨ty, y, rfl⟩ := h2
    have hp := hq.ofPopN
    simp only [exec]
    repeat' split
    all_goals first
      | trivial
      | exact hp
      | exact QRes_callFunc cfg p (hp.ofSetFrame _) _
  have h := X_exec cfg p s f pf i (fun fi e => h1 ⟨fi, e⟩) (fun ty y e => h2 ⟨ty, y, e⟩) s
  rw [setX_self] at h
  exact QRes_of_eq hq h

/-- **A step keeps the invariant.** -/
theorem QRes_step (cfg : NearCfg) (p : Prepared) {s : St} (hq : LowQ s) : QRes (step cfg p s) := by
  unfold step
  split
  · exact hq
  split
  · trivial
  split
  · trivial
  split
  · trivial
  · exact QRes_exec cfg p hq _ _ _
  · rename_i k fee _
    have hc := QRes_charge hq fee (if k = .linear then topCount s else 0)
    revert hc
    cases charge s fee (if k = .linear then topCount s else 0) with
    | cont s' => intro hc; exact QRes_exec cfg p hc _ _ _
    | fin s' => intro hc; exact hc
    | abort s' e => intro hc; exact hc
    | unmodeled w => intro _; trivial

/-- **A whole run keeps the invariant.** -/
theorem QRes_run (cfg : NearCfg) (p : Prepared) : ∀ n {s : St}, LowQ s → QRes (run cfg p n s)
  | 0, _, _ => trivial
  | n + 1, s, hq => by
    unfold run
    have hs := QRes_step cfg p hq
    revert hs
    cases step cfg p s with
    | cont s' => intro hs; exact QRes_run cfg p n hs
    | fin s' => intro hs; exact hs
    | abort s' e => intro hs; exact hs
    | unmodeled w => intro _; trivial

/-- `callEntry`'s run, after its entry. -/
def entryRun (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s0 : St) (fi : Nat) : Res :=
  match enter p s0 fi with
  | .cont s => run cfg p fuel s
  | r => r

theorem entryCore_eq_run (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s0 : St) (fi : Nat) :
    entryCore cfg p fuel s0 fi =
      match entryRun cfg p fuel s0 fi with
      | .fin s => (sync s).map (·, none)
      | .abort s e => (sync s).map (·, some e)
      | .unmodeled why => .error why
      | .cont _ => .error "cont" := rfl

theorem QRes_entryRun (cfg : NearCfg) (p : Prepared) (fuel : Nat) {s0 : St} (fi : Nat) (hq : LowQ s0) :
    QRes (entryRun cfg p fuel s0 fi) := by
  unfold entryRun
  have h0 := QRes_enter p hq fi
  revert h0
  cases enter p s0 fi with
  | cont s1 => intro h0; exact QRes_run cfg p fuel h0
  | fin s1 => intro h0; exact h0
  | abort s1 e => intro h0; exact h0
  | unmodeled w => intro _; trivial

/-- `callEntry` from a state whose reset satisfies `LowQ` ends in a state satisfying it. -/
theorem LowQ_callEntry (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat)
    (hq : LowQ (entryReset s)) (s' : St) (e : Option String)
    (he : callEntry cfg p fuel s fi = .ok (s', e)) : LowQ s' := by
  rw [callEntry_eq_core, entryCore_eq_run] at he
  have hr := QRes_entryRun cfg p fuel fi hq
  revert hr he
  generalize entryRun cfg p fuel (entryReset s) fi = r
  intro he hr
  cases r with
  | fin t =>
    simp only at he
    cases hs : sync t with
    | error x => rw [hs] at he; cases he
    | ok t' => rw [hs] at he; cases he; exact LowQ.ofSync hr hs
  | abort t x =>
    simp only at he
    cases hs : sync t with
    | error x => rw [hs] at he; cases he
    | ok t' => rw [hs] at he; cases he; exact LowQ.ofSync hr hs
  | unmodeled w => cases he
  | cont t => cases he

/-! ## O3's per-call hypothesis -/

theorem LowQ.ofCharge {s s' : St} (hq : LowQ s) (fee : Fee) (c : Nat) (e : charge s fee c = .cont s') :
    LowQ s' := by
  have h := QRes_charge hq fee c
  rw [e] at h; exact h

/-- **O3, per call.** From a lower state with the flag off, trie-backed and without raw actions,
a host call is a two-run step (`callHost_RR_global`), and the invariant survives the lower run's
frames, pops and charges. -/
theorem globalHyp : CallHyp XG none (some true) LowQ :=
  ⟨fun s name hq => callHost_RR_global s name hq.ga hq.real,
   fun _ f hq => hq.ofSetFrame f,
   fun _ hq => hq.ofPopN,
   fun _ fee c _ hq e => hq.ofCharge fee c e⟩

theorem LowQ_step_cont (cfg : NearCfg) (p : Prepared) (s s' : St) (hq : LowQ s)
    (e : step cfg p s = .cont s') : LowQ s' := by
  have h := QRes_step cfg p hq
  rw [e] at h; exact h

theorem LowQ_enter_cont (p : Prepared) (fi : Nat) (s s' : St) (hq : LowQ s)
    (e : enter p s fi = .cont s') : LowQ s' := by
  have h := QRes_enter p hq fi
  rw [e] at h; exact h

#print axioms QRes_callHost
#print axioms QRes_run
#print axioms LowQ_callEntry
#print axioms globalHyp

end NearSpecV3.Successor.HostComm
