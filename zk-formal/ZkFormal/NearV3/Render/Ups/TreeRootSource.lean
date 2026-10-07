import ZkFormal.NearV3.Render.Ups.SourceDepthAllocation

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem leafSplitRun_rootSource (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).parts.getLast?.map TreePart.source=some (.leaf k s m) := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [terminalRun,wrapRun,pushPart]

theorem extSplitRun_rootSource (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hprefix : isPrefix k key=false) :
    (extSplitRun k c m key v).parts.getLast?.map TreePart.source=some (.ext k c m) := by
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

/-- The final emitted part always consumes the actual native root source. -/
theorem traceUpsert_rootSource {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) : run.parts.getLast?.map TreePart.source=some t := by
  cases t with
  | hash h => simp [traceUpsert] at hr
  | leaf k s m =>
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [terminalRun,he]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_rootSource k s m key v
  | ext k c m =>
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_rootSource k c m key v hp
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
end ZkFormal.NearV3.Render.UpsGen
