import ZkFormal.NearV3.Render.Ups.TreePlan

/-! Terminal key positions are derived from the executable runtime trace. In
particular a two-nibble update always produces a matched-prefix index at most two. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

@[simp] theorem wrapRun_terminalKey (src : PTrie) (path : List Nat) (run : TreeRun) :
    (wrapRun src path run).terminalKey=run.terminalKey := by cases path <;> rfl
@[simp] theorem wrapRun_matched (src : PTrie) (path : List Nat) (run : TreeRun) :
    (wrapRun src path run).matched=run.matched := by cases path <;> rfl

def TreeRun.KeyInfo (key : List Nat) (run : TreeRun) : Prop :=
  ∃ consumed, consumed≤key.length ∧ run.terminalKey=key.drop consumed ∧ run.matched≤run.terminalKey.length

theorem keyInfo_drop {key : List Nat} {n : Nat} {run : TreeRun} (hn : n≤key.length)
    (h : run.KeyInfo (key.drop n)) : run.KeyInfo key := by
  obtain ⟨d,hd,hk,hm⟩ := h
  refine ⟨n+d,?_,?_,hm⟩
  · simp only [List.length_drop] at hd; omega
  · simpa only [List.drop_drop,Nat.add_comm] using hk

theorem keyInfo_cons {key : List Nat} {run : TreeRun} (n : Nat) (h : run.KeyInfo key) :
    run.KeyInfo (n::key) := by
  obtain ⟨d,hd,hk,hm⟩ := h
  exact ⟨d+1,by simp; omega,by simpa using hk,hm⟩

theorem leafSplitRun_keys (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).KeyInfo key := by
  have hb := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hb
  unfold leafSplitRun
  generalize hp : commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> refine ⟨0,by omega,?_,?_⟩ <;>
    simp [wrapRun_terminalKey,wrapRun_matched,terminalRun] <;> omega

theorem extSplitRun_keys (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).KeyInfo key := by
  have hb := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hb
  unfold extSplitRun
  generalize hp : commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil =>
    simp only [h1]
    exact ⟨0,by omega,rfl,by simpa [terminalRun] using (show p.length≤key.length by omega)⟩
  | cons x xs =>
    simp only [h1]
    cases h2 : key.drop p.length <;> simp only [h2] <;>
      refine ⟨0,by omega,?_,?_⟩ <;> simp [wrapRun_terminalKey,wrapRun_matched,terminalRun] <;> omega

mutual
theorem traceUpsert_keys : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.KeyInfo key
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; exact ⟨0,by omega,rfl,by simp [terminalRun]⟩
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_keys k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_keys k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have hn : k.length≤key.length := by
            obtain ⟨rest,he⟩ := (isPrefix_iff k key).mp hp
            simp [he]
          exact keyInfo_drop hn (traceUpsert_keys c (key.drop k.length) v inner hr)
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run; exact ⟨0,by omega,rfl,by simp [terminalRun]⟩
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_keys (.branch bv cs m) (n::key) cs n key v inner hr
      cases hi : inner.inserted
      · simp only [hi,Bool.false_eq_true,ite_false] at ih
        exact keyInfo_cons n ih
      · simpa only [hi,ite_true,TreeRun.KeyInfo,pushPart] using ih
theorem traceKids_keys : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    run.inner.KeyInfo (if run.inserted then wholeKey else key)
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; exact ⟨0,by omega,rfl,by simp [terminalRun]⟩
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run; exact traceUpsert_keys c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run; exact traceKids_keys source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run; exact traceKids_keys source wholeKey rest n key v inner hr
end

/-- Number of key nibbles consumed before reaching the terminal source node. -/
def TreeRun.consumed (key : List Nat) (run : TreeRun) : Nat := key.length-run.terminalKey.length

/-- The next symbol position at a split or a missing-child terminal. -/
def TreeRun.splitCursor (key : List Nat) (run : TreeRun) : Nat := run.consumed key+run.matched+1

theorem keyInfo_canonical {key : List Nat} {run : TreeRun} (h : run.KeyInfo key) :
    run.terminalKey=key.drop (run.consumed key) ∧ run.consumed key+run.matched≤key.length := by
  obtain ⟨d,hd,hk,hm⟩ := h
  have hl := congrArg List.length hk
  simp only [List.length_drop] at hl
  have he : run.consumed key=d := by unfold TreeRun.consumed; omega
  exact ⟨by simpa only [he] using hk,by rw [he]; omega⟩

theorem trace_fixedKey_bounds {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) :
    run.terminalKey=[0,15].drop (run.consumed [0,15]) ∧
    run.consumed [0,15]+run.matched≤2 ∧
    1≤run.splitCursor [0,15] ∧ run.splitCursor [0,15]≤3 := by
  have h := keyInfo_canonical (traceUpsert_keys t [0,15] v run hr)
  refine ⟨h.1,by simpa using h.2,?_,?_⟩ <;> unfold TreeRun.splitCursor <;> simp at h <;> omega

theorem trace_fixedKey_wrap {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) (hm : 0<run.matched) :
    (run.splitCursor [0,15]=2 ∧ run.matched=1) ∨
    (run.splitCursor [0,15]=3 ∧ run.matched=1) ∨
    (run.splitCursor [0,15]=3 ∧ run.matched=2) := by
  have h := trace_fixedKey_bounds hr
  unfold TreeRun.splitCursor at *
  omega

theorem trace_fixedKey_newSuffix {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) :
    run.terminalKey.drop (run.matched+1)=[0,15].drop (run.splitCursor [0,15]) := by
  rw [(trace_fixedKey_bounds hr).1,List.drop_drop]
  simp [TreeRun.splitCursor,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem trace_fixedKey_prefix {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) :
    run.terminalKey.take run.matched=
      ([0,15].drop (run.splitCursor [0,15]-1-run.matched)).take run.matched := by
  rw [(trace_fixedKey_bounds hr).1]
  simp [TreeRun.splitCursor]

end ZkFormal.NearV3.Render.UpsGen
