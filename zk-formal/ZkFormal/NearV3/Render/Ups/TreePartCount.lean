import ZkFormal.NearV3.Render.Ups.TreeEncodingTotal
import ZkFormal.NearV3.Spec.StoreBuilt

/-! Exact native builder depth bounds the number of emitted update parts, including
empty-extension pass-throughs and the largest split terminal. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows UpsSpec

theorem leafSplitRun_count (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).parts.length≤4 := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;> simp [terminalRun,wrapRun,pushPart]

theorem extSplitRun_count (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).parts.length≤4 := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [terminalRun,wrapRun,pushPart]

mutual
theorem traceUpsert_count : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.parts.length≤fdepth t key+3
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [terminalRun,fdepth]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_count k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      simpa [fdepth,hp] using extSplitRun_count k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have ih := traceUpsert_count c (key.drop k.length) v inner hr
          simp [pushPart,fdepth,hp]; omega
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run; simp [terminalRun,fdepth]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_count (.branch bv cs m) (n::key) cs n key v inner hr
      simp [pushPart,fdepth]; omega
theorem traceKids_count : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → run.inner.parts.length≤kfdepth cs n key+3
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [terminalRun,kfdepth]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_count c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_count source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_count source wholeKey rest n key v inner hr
end

/-- The actual 400-step native builder leaves room in the 512-part identifier space. -/
theorem partialTrie_part_count (values : List Bytes) (root : Bytes) (keys : List (List Nat))
    (hr : root.length=32) (key : List Nat) (v : Bytes) (run : TreeRun)
    (h : traceUpsert (partialTrie values root keys) key v=some run) :
    run.parts.length≤403 ∧ run.parts.length<512 := by
  have hd := (built_spec values 400 root keys hr).2.2.2 key
  have hc := traceUpsert_count (partialTrie values root keys) key v run h
  change fdepth (partialTrie values root keys) key≤400 at hd
  omega
end ZkFormal.NearV3.Render.UpsGen
