import ZkFormal.NearV3.Render.Ups.SignedInstance

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def endCase : UCase→Bool
  | .LP | .BR | .BV | .LSb | .ESl0 | .ESl1 => true
  | _ => false

def TreeRun.TerminalEnd (run : TreeRun) : Prop :=
  run.matched=run.terminalKey.length ↔ endCase run.terminal=true

theorem leafSplitRun_terminalEnd (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).TerminalEnd := by
  have hl := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hl
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h2,List.length_cons,List.length_nil] at hl <;>
    simp only [h1,h2] <;> cases p <;>
    simp_all [TreeRun.TerminalEnd,terminalRun,wrapRun,pushPart,endCase] <;> omega

theorem extSplitRun_terminalEnd (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hprefix : isPrefix k key=false) : (extSplitRun k c m key v).TerminalEnd := by
  have hnon : k.drop (commonPrefix k key).length≠[] := by
    intro h
    have ho := commonPrefix_left k key
    rw [h,List.append_nil] at ho
    have hp := commonPrefix_right k key
    have hpre := (isPrefix_iff k key).mpr ⟨_,by simpa only [←ho] using hp⟩
    simp [hprefix] at hpre
  have hl := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hl
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => exact (hnon h1).elim
  | cons x xs =>
    cases h2 : key.drop p.length <;>
      simp only [h2,List.length_cons,List.length_nil] at hl <;>
      simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp_all [TreeRun.TerminalEnd,terminalRun,wrapRun,pushPart,endCase] <;> omega

mutual
/-- End-of-key case classification is determined by native execution. -/
theorem traceUpsert_terminalEnd : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.TerminalEnd
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [TreeRun.TerminalEnd,terminalRun,endCase]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_terminalEnd k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_terminalEnd k c m key v hp
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          exact traceUpsert_terminalEnd c _ v inner hr
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [TreeRun.TerminalEnd,terminalRun,endCase]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_terminalEnd _ _ cs n key v inner hr (by simp)

theorem traceKids_terminalEnd : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → wholeKey≠[] → run.inner.TerminalEnd
  | _, _, .nil, _, _, _, _, h, _ => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h, hn => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    have hl := List.length_pos_iff.mpr hn
    simp only [TreeRun.TerminalEnd,terminalRun,endCase,Bool.false_eq_true,iff_false]
    omega
  | source, wholeKey, .some c rest, 0, key, v, run, h, _ => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_terminalEnd c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h, hn => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_terminalEnd source wholeKey rest n key v inner hr hn
  | source, wholeKey, .some c rest, n+1, key, v, run, h, hn => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_terminalEnd source wholeKey rest n key v inner hr hn
end

/-- The renderer's END versus nibble-terminal cases are consequences of the native trace. -/
theorem traceInstance_terminalCases {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) (base : UpsInst) :
    ((traceInstance base run v).ts=3 → (traceInstance base run v).ci=0 ∨
      (traceInstance base run v).ci=1 ∨ (traceInstance base run v).ci=2 ∨
      (traceInstance base run v).ci=5 ∨ (traceInstance base run v).ci=7 ∨ (traceInstance base run v).ci=8) ∧
    ((traceInstance base run v).ts≠3 → (traceInstance base run v).ci=3 ∨
      (traceInstance base run v).ci=4 ∨ (traceInstance base run v).ci=6 ∨
      (traceInstance base run v).ci=9 ∨ (traceInstance base run v).ci=10) := by
  have he := traceUpsert_terminalEnd t [0,15] v run hr
  obtain ⟨consumed,hc,hkey,hm⟩ := traceUpsert_keys t [0,15] v run hr
  have hk := congrArg List.length hkey
  simp only [List.length_drop,List.length_cons,List.length_nil] at hk hc
  have hend : (traceInstance base run v).ts=3 ↔ run.matched=run.terminalKey.length := by
    change 2-run.terminalKey.length+run.matched+1=3 ↔ _
    omega
  simp only [Ne,hend]
  change (_ → run.terminal.ix=0 ∨ run.terminal.ix=1 ∨ run.terminal.ix=2 ∨
    run.terminal.ix=5 ∨ run.terminal.ix=7 ∨ run.terminal.ix=8) ∧
    (_ → run.terminal.ix=3 ∨ run.terminal.ix=4 ∨ run.terminal.ix=6 ∨ run.terminal.ix=9 ∨ run.terminal.ix=10)
  change (run.matched=run.terminalKey.length ↔ endCase run.terminal=true) at he
  simp only [he]
  cases hcase : run.terminal <;> simp_all [endCase,UCase.ix]
end ZkFormal.NearV3.Render.UpsGen
