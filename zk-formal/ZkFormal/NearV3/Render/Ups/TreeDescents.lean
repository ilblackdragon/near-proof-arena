import ZkFormal.NearV3.Render.Ups.PlanAllocation

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Only proper descents consume a walk source level; empty extensions are pass-throughs. -/
def descendKind (kind : UKind) : Bool := match kind with | .RDB | .RDE => true | _ => false

def descentCount (parts : List TreePart) : Nat := (parts.filter (fun p => descendKind p.kind)).length

@[simp] theorem descentCount_append (a b : List TreePart) :
    descentCount (a++b)=descentCount a+descentCount b := by simp [descentCount,List.filter_append]

@[simp] theorem descentCount_single (p : TreePart) :
    descentCount [p]=if descendKind p.kind then 1 else 0 := by
  cases h : descendKind p.kind <;> simp [descentCount,h]

theorem leafSplitRun_descents (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    descentCount (leafSplitRun k s m key v).parts=0 := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [wrapRun,pushPart,terminalRun,descentCount,descendKind]

theorem extSplitRun_descents (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    descentCount (extSplitRun k c m key v).parts=0 := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun,descentCount]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [wrapRun,pushPart,terminalRun,descentCount,descendKind]

mutual
/-- Every counted descent consumes a query nibble, even with unbounded empty-extension chains. -/
theorem traceUpsert_descents : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → descentCount run.parts≤key.length
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [terminalRun,descentCount,descendKind]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; simp [leafSplitRun_descents]
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; simp [extSplitRun_descents]
    | true =>
      obtain ⟨suffix,hsuffix⟩ := (isPrefix_iff k key).mp hp
      have hlen := congrArg List.length hsuffix
      simp only [List.length_append] at hlen
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have ih := traceUpsert_descents c (key.drop k.length) v inner hr
          simp only [List.length_drop] at ih
          cases k <;> simp [pushPart,descentCount_append,descendKind] <;>
            simp only [List.length_nil,List.length_cons] at ih hlen <;> omega
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [terminalRun,descentCount,descendKind]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_descents (.branch bv cs m) (n::key) cs n key v inner hr
      cases hi : inner.inserted <;> simp [pushPart,descentCount_append,descendKind,hi] <;> omega

theorem traceKids_descents : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → descentCount run.inner.parts≤key.length
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [terminalRun,descentCount,descendKind]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_descents c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_descents source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_descents source wholeKey rest n key v inner hr
end

theorem fixed_trace_descents {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) : descentCount run.parts<3 := by
  have h := traceUpsert_descents t [0,15] v run hr
  simp only [List.length_cons,List.length_nil] at h
  omega
end ZkFormal.NearV3.Render.UpsGen
