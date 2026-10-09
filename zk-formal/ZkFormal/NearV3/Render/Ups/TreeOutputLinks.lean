import ZkFormal.NearV3.Render.Ups.TreeChildLookup

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem leafSplitRun_rootOutput (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).parts.getLast?.map TreePart.output=
      some (leafSplitRun k s m key v).output := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;> simp [terminalRun,wrapRun,pushPart]

theorem extSplitRun_rootOutput (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hprefix : isPrefix k key=false) :
    (extSplitRun k c m key v).parts.getLast?.map TreePart.output=
      some (extSplitRun k c m key v).output := by
  have hnon : k.drop (commonPrefix k key).length≠[] := by
    intro h
    have ho := commonPrefix_left k key
    rw [h,List.append_nil] at ho
    have hp := commonPrefix_right k key
    have hpre := (isPrefix_iff k key).mpr ⟨_,by simpa only [←ho] using hp⟩
    simp [hprefix] at hpre
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => exact (hnon h1).elim
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [terminalRun,wrapRun,pushPart]

/-- The last emitted output is exactly the native upsert result. -/
theorem traceUpsert_rootOutput {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) : run.parts.getLast?.map TreePart.output=some run.output := by
  cases t with
  | hash h => simp [traceUpsert] at hr
  | leaf k s m =>
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [terminalRun]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_rootOutput k s m key v
  | ext k c m =>
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_rootOutput k c m key v hp
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run; simp [pushPart]
  | branch value kids mem =>
    cases key with
    | nil =>
      simp only [traceUpsert,Option.some.injEq] at hr
      subst run; simp [terminalRun]
    | cons n key =>
      cases hc : traceKids (.branch value kids mem) (n::key) kids n key v with
      | none => simp [traceUpsert,hc] at hr
      | some inner =>
        simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
        subst run; simp [pushPart]

/-- The rewritten branch slot contains exactly the recursively produced new child. -/
theorem traceKids_newChild (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun)
    (hr : traceKids source wholeKey cs n key v=some run) :
    nativeChildAt run.output n=some run.inner.output := by
  cases cs with
  | nil => simp [traceKids] at hr
  | none rest =>
    cases n with
    | zero => simp only [traceKids,Option.some.injEq] at hr; subst run; rfl
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_newChild source wholeKey rest n key v inner hc
  | some child rest =>
    cases n with
    | zero =>
      cases hm : child.mem? with
      | none => simp [traceKids,hm] at hr
      | some cm =>
        cases hc : traceUpsert child key v with
        | none => simp [traceKids,hm,hc] at hr
        | some inner =>
          simp only [traceKids,hm,hc,Option.some.injEq] at hr
          subst run; rfl
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_newChild source wholeKey rest n key v inner hc
termination_by cs
end ZkFormal.NearV3.Render.UpsGen
