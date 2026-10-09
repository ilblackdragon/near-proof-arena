import ZkFormal.NearV3.Render.Ups.TreeOutputChain

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def parentDigestKind (k : UKind) : Prop := k=.RDB ∨ k=.RDE ∨ k=.PT ∨ k=.RBI ∨ k=.WEX

/-- Every rewritten upper node contains the preceding part's output child. -/
def ParentLinked : List TreePart → Prop
  | [] => True
  | [_] => True
  | a::b::rest => (parentDigestKind b.kind → outputPathChild b=some a.output) ∧ ParentLinked (b::rest)

theorem ParentLinked.append (xs : List TreePart) (p : TreePart) (h : ParentLinked xs)
    (edge : ∀ a, xs.getLast?=some a → parentDigestKind p.kind → outputPathChild p=some a.output) :
    ParentLinked (xs++[p]) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    cases xs with
    | nil => exact ⟨edge a rfl,trivial⟩
    | cons b rest =>
      exact ⟨h.1,ih h.2 (by simpa using edge)⟩

theorem leafSplitRun_parentLinked (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    ParentLinked (leafSplitRun k s m key v).parts := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [h1,h2]
  all_goals cases p <;> simp [terminalRun,wrapRun,pushPart,ParentLinked,parentDigestKind,outputPathChild,wrapExt]

theorem extSplitRun_parentLinked (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    ParentLinked (extSplitRun k c m key v).parts := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun,ParentLinked]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2]
    all_goals cases xs <;> cases p <;> simp [terminalRun,wrapRun,pushPart,ParentLinked,parentDigestKind,outputPathChild,wrapExt]


mutual
/-- Actual native execution satisfies every upper-node output-child link. -/
theorem traceUpsert_parentLinked : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run →
    ParentLinked run.parts
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [terminalRun,ParentLinked]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact leafSplitRun_parentLinked k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact extSplitRun_parentLinked k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have ih := traceUpsert_parentLinked c (key.drop k.length) v inner hr
          apply ParentLinked.append _ _ ih
          intro a ha hu
          have hs := traceUpsert_rootOutput hr
          rw [ha] at hs
          simp only [Option.map_some,Option.some.injEq] at hs
          simp [outputPathChild,UpsSpec.qRDE,hs]
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [terminalRun,ParentLinked]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_parentLinked (.branch bv cs m) (n::key) cs n key v inner hr
      apply ParentLinked.append _ _ ih
      intro a ha hu
      have hs := traceKids_rootOutput (.branch bv cs m) (n::key) cs n key v inner hr
      rw [ha] at hs
      simp only [Option.map_some,Option.some.injEq] at hs
      have hc := traceKids_newChild (.branch bv cs m) (n::key) cs n key v inner hr
      simpa [outputPathChild,hs] using hc
/-- Branch recursion preserves the complete bottom-up output chain. -/
theorem traceKids_parentLinked : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run →
    ParentLinked run.inner.parts
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [terminalRun,ParentLinked]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_parentLinked c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_parentLinked source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_parentLinked source wholeKey rest n key v inner hr
end

/-- Indexed form consumed by the executable part allocator. -/
theorem ParentLinked.adjacent {parts : List TreePart} (h : ParentLinked parts)
    {k : Nat} {a b : TreePart} (ha : parts[k]?=some a) (hb : parts[k+1]?=some b)
    (hu : parentDigestKind b.kind) : outputPathChild b=some a.output := by
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
theorem traceUpsert_parentChild {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) {k : Nat} {a b : TreePart}
    (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hu : parentDigestKind b.kind) : outputPathChild b=some a.output :=
  (traceUpsert_parentLinked t key v run hr).adjacent ha hb hu
end ZkFormal.NearV3.Render.UpsGen
