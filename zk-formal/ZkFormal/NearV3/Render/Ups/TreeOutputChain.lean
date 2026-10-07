import ZkFormal.NearV3.Render.Ups.TreeSourceChain
import ZkFormal.NearV3.Render.Ups.TreeOutputLinks

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem traceKids_rootOutput (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun)
    (hr : traceKids source wholeKey cs n key v=some run) :
    run.inner.parts.getLast?.map TreePart.output=some run.inner.output := by
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
        exact traceKids_rootOutput source wholeKey rest n key v inner hc
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
          subst run
          exact traceUpsert_rootOutput hc
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_rootOutput source wholeKey rest n key v inner hc

termination_by cs


def outputPathChild (p : TreePart) : Option PTrie :=
  match p.output with
  | .branch _ kids _ => nativeChildAt kids p.slot
  | .ext _ child _ => some child
  | _ => none

/-- Every rewritten upper node contains the preceding part's output child. -/
def OutputLinked : List TreePart → Prop
  | [] => True
  | [_] => True
  | a::b::rest => (upperKind b.kind → outputPathChild b=some a.output) ∧ OutputLinked (b::rest)

theorem OutputLinked.append (xs : List TreePart) (p : TreePart) (h : OutputLinked xs)
    (edge : ∀ a, xs.getLast?=some a → upperKind p.kind → outputPathChild p=some a.output) :
    OutputLinked (xs++[p]) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    cases xs with
    | nil => exact ⟨edge a rfl,trivial⟩
    | cons b rest =>
      exact ⟨h.1,ih h.2 (by simpa using edge)⟩

theorem OutputLinked.wrap (source : PTrie) (key : List Nat) (run : TreeRun)
    (h : OutputLinked run.parts) : OutputLinked (wrapRun source key run).parts := by
  cases key with
  | nil => exact h
  | cons x xs =>
    apply OutputLinked.append _ _ h
    intro a ha hu
    simp [upperKind] at hu

theorem leafSplitRun_outputLinked (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    OutputLinked (leafSplitRun k s m key v).parts := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [h1,h2]
  all_goals cases p <;> simp [terminalRun,wrapRun,pushPart,OutputLinked,upperKind]

theorem extSplitRun_outputLinked (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    OutputLinked (extSplitRun k c m key v).parts := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun,OutputLinked]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2]
    all_goals cases xs <;> cases p <;> simp [terminalRun,wrapRun,pushPart,OutputLinked,upperKind]


mutual
/-- Actual native execution satisfies every upper-node output-child link. -/
theorem traceUpsert_outputLinked : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run →
    OutputLinked run.parts
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [terminalRun,OutputLinked]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact leafSplitRun_outputLinked k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact extSplitRun_outputLinked k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have ih := traceUpsert_outputLinked c (key.drop k.length) v inner hr
          apply OutputLinked.append _ _ ih
          intro a ha hu
          have hs := traceUpsert_rootOutput hr
          rw [ha] at hs
          simp only [Option.map_some,Option.some.injEq] at hs
          simp [outputPathChild,UpsSpec.qRDE,hs]
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [terminalRun,OutputLinked]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_outputLinked (.branch bv cs m) (n::key) cs n key v inner hr
      apply OutputLinked.append _ _ ih
      intro a ha hu
      cases hi : inner.inserted with
      | true => simp [hi,upperKind] at hu
      | false =>
        have hs := traceKids_rootOutput (.branch bv cs m) (n::key) cs n key v inner hr
        rw [ha] at hs
        simp only [Option.map_some,Option.some.injEq] at hs
        have hc := traceKids_newChild (.branch bv cs m) (n::key) cs n key v inner hr
        simpa [outputPathChild,hi,hs] using hc
/-- Branch recursion preserves the complete bottom-up output chain. -/
theorem traceKids_outputLinked : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run →
    OutputLinked run.inner.parts
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [terminalRun,OutputLinked]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_outputLinked c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_outputLinked source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_outputLinked source wholeKey rest n key v inner hr
end

/-- Indexed form consumed by the executable part allocator. -/
theorem OutputLinked.adjacent {parts : List TreePart} (h : OutputLinked parts)
    {k : Nat} {a b : TreePart} (ha : parts[k]?=some a) (hb : parts[k+1]?=some b)
    (hu : upperKind b.kind) : outputPathChild b=some a.output := by
  induction parts generalizing k with
  | nil => simp at ha
  | cons x rest ih =>
    cases rest with
    | nil => cases k <;> simp at hb
    | cons y rest =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at ha
        simp only [Nat.zero_add,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hb
        subst x; subst y; exact h.1 hu
      | succ k =>
        exact ih h.2 (by simpa using ha) (by simpa [Nat.add_assoc] using hb)

/-- Actual adjacent update outputs have the native parent-child relation before
any record-id or byte-window allocation is chosen. -/
theorem traceUpsert_outputChild {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) {k : Nat} {a b : TreePart}
    (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hu : upperKind b.kind) : outputPathChild b=some a.output :=
  (traceUpsert_outputLinked t key v run hr).adjacent ha hb hu
end ZkFormal.NearV3.Render.UpsGen
