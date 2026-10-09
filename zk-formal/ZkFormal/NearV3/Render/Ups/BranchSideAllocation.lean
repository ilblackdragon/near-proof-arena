import ZkFormal.NearV3.Render.Ups.TreeChildLookup
import ZkFormal.NearV3.Render.Ups.PositionedPart
import ZkFormal.NearV3.Render.Ups.TreeBranchInput
import ZkFormal.NearV3.Render.Ups.FixedSuffix
import ZkFormal.NearV3.Render.Ups.TreeInsertTrace

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Native branch slots agree with their top-down proper-descent coordinate. -/
def BranchSides (start : Nat) (parts : List TreePart) : Prop :=
  ∀ k p, parts[k]?=some p → p.kind=.RDB →
    start+remainingDescents parts (k+1)<2 ∧
    p.slot=edgeSlot (start+remainingDescents parts (k+1))

theorem BranchSides.of_zero (start : Nat) (parts : List TreePart) (hz : descentCount parts=0) :
    BranchSides start parts := by
  intro k p hp hk
  have hs := remainingDescents_step parts k p hp
  have hb := remainingDescents_le parts k
  simp only [hk,descendKind,ite_true] at hs
  omega

theorem BranchSides.append (start : Nat) (parts : List TreePart) (p : TreePart)
    (h : BranchSides (start+(if descendKind p.kind then 1 else 0)) parts)
    (hedge : p.kind=.RDB → start<2 ∧ p.slot=edgeSlot start) :
    BranchSides start (parts++[p]) := by
  intro k q hq hkind
  have hn := List.getElem?_eq_some_iff.mp hq |>.1
  by_cases hk : k<parts.length
  · have hq' : parts[k]?=some q := by simpa [List.getElem?_append,hk] using hq
    have hi := h k q hq' hkind
    have hdrop : remainingDescents (parts++[p]) (k+1)=
        remainingDescents parts (k+1)+(if descendKind p.kind then 1 else 0) := by
      simp [remainingDescents,List.drop_append,show k+1≤parts.length by omega,
        Nat.sub_eq_zero_of_le (show k+1≤parts.length by omega)]
    rw [hdrop]
    have he : start+(remainingDescents parts (k+1)+(if descendKind p.kind then 1 else 0))=
        start+(if descendKind p.kind then 1 else 0)+remainingDescents parts (k+1) := by omega
    simpa [he] using hi
  · have he : k=parts.length := by simp only [List.length_append,List.length_singleton] at hn; omega
    subst k
    simp at hq
    subst q
    simpa [remainingDescents,List.drop_append,descentCount,
      List.drop_eq_nil_of_le (show parts.length≤parts.length+1 by omega)] using hedge hkind
theorem FixedSuffix.drop {key : List Nat} (hk : FixedSuffix key) (n : Nat) :
    FixedSuffix (key.drop n) := by
  rcases hk with rfl|rfl|rfl <;> cases n with
  | zero => simp [FixedSuffix]
  | succ n => cases n <;> simp [FixedSuffix]

mutual
theorem traceUpsert_branchSides : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → FixedSuffix key → ∀ start,
    (key=[] ∨ start+key.length=2) → BranchSides start run.parts
  | .hash _, _, _, _, hr, _, _, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, _, start, _ => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      apply BranchSides.of_zero
      simp [terminalRun,descentCount,descendKind]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run
      exact BranchSides.of_zero start _ (leafSplitRun_descents k s m key v)
  | .ext k c m, key, v, run, hr, hk, start, hstart => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      exact BranchSides.of_zero start _ (extSplitRun_descents k c m key v)
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          have hkey := hk.drop k.length
          have hlen := hk.length
          cases k with
          | nil =>
            have ih := traceUpsert_branchSides c key v inner (by simpa using hc) hk start hstart
            apply BranchSides.append
            · simpa [descendKind] using ih
            · simp [upperKind]
          | cons a ks =>
            have hnext : key.drop (a::ks).length=[] ∨ start+1+(key.drop (a::ks).length).length=2 := by
              by_cases hz : key.drop (a::ks).length=[]
              · exact Or.inl hz
              · right
                have hpos := List.length_pos_iff.mpr hz
                simp only [List.length_drop,List.length_cons] at hpos ⊢
                rcases hstart with he|he
                · subst key; simp at hz
                · omega
            have ih := traceUpsert_branchSides c (key.drop (a::ks).length) v inner hc hkey (start+1) hnext
            apply BranchSides.append
            · simpa [descendKind] using ih
            · simp [upperKind]
  | .branch bv cs m, [], v, run, hr, _, start, _ => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    apply BranchSides.of_zero
    cases bv <;> simp [terminalRun,descentCount,descendKind]
  | .branch bv cs m, n::key, v, run, hr, hk, start, hstart => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have htail : FixedSuffix key := by simpa using hk.drop 1
      have hnext : key=[] ∨ start+1+key.length=2 := by
        right; simp only [List.cons_ne_nil,false_or,List.length_cons] at hstart; omega
      cases hi : inner.inserted with
      | true =>
        have hz := (traceKids_inserted _ _ _ _ _ _ _ hc hi).2.2
        apply BranchSides.of_zero
        simp [pushPart,hi,hz,terminalRun,descentCount,descendKind]
      | false =>
        have ih := traceKids_branchSides (.branch bv cs m) (n::key) cs n key v inner hc htail (start+1) hnext
        apply BranchSides.append
        · simpa [hi,descendKind] using ih
        · intro _
          rcases hk with h|h|h
          · simp at h
          · obtain ⟨rfl,rfl⟩ := List.cons.inj h
            simp at hstart
            simp [edgeSlot,show start=1 by omega]
          · obtain ⟨rfl,rfl⟩ := List.cons.inj h
            simp at hstart
            simp [edgeSlot,show start=0 by omega]
theorem traceKids_branchSides : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → FixedSuffix key → ∀ start,
    (key=[] ∨ start+key.length=2) → BranchSides start run.inner.parts
  | _, _, .nil, _, _, _, _, hr, _, _, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr, _, start, _ => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    apply BranchSides.of_zero
    simp [terminalRun,descentCount,descendKind]
  | source, wholeKey, .some child rest, 0, key, v, run, hr, hk, start, hstart => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_branchSides child key v inner hc hk start hstart
  | source, wholeKey, .none rest, n+1, key, v, run, hr, hk, start, hstart => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_branchSides source wholeKey rest n key v inner hc hk start hstart
  | source, wholeKey, .some child rest, n+1, key, v, run, hr, hk, start, hstart => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_branchSides source wholeKey rest n key v inner hc hk start hstart
end
/-- The existing-child byte constructor's edge-side metadata is derived from actual
fixed-key traversal, including empty-extension chains and two-nibble extensions. -/
theorem positionedPart_branchSide (recordId : PTrie→Nat) (depth : Nat)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (k : Nat) (p : TreePart) (hp : run.parts[k]?=some p) (hkind : p.kind=.RDB) (base : UpsPartI) :
    let Q := positionedPart recordId depth run k p base
    (Q.sd=0 ∨ Q.sd=1) ∧ p.slot=edgeSlot Q.sd := by
  have hs := traceUpsert_branchSides root [0,15] v run hr (Or.inr (Or.inr rfl)) 0 (Or.inr rfl)
  obtain ⟨hbound,hslot⟩ := hs k p hp hkind
  have hstep := remainingDescents_step run.parts k p hp
  simp only [hkind,descendKind,ite_true] at hstep
  have he : remainingDescents run.parts k-1=remainingDescents run.parts (k+1) := by omega
  simp only [Nat.zero_add] at hbound hslot
  simp only [positionedPart,withPlanPosition,withDescentPosition,hkind,UKind.ix,true_or,ite_true]
  rw [he]
  exact ⟨by omega,hslot⟩
end ZkFormal.NearV3.Render.UpsGen
