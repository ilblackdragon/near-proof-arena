import ZkFormal.NearV3.Render.Ups.BranchSideAllocation
import ZkFormal.NearV3.Render.Ups.TreeValueDispatch
import ZkFormal.NearV3.Render.Ups.TreeExtSplitDispatch
import ZkFormal.NearV3.Render.Ups.TreeInsertDispatch
import ZkFormal.NearV3.Render.Ups.TreeExtInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

/-- Temporary local encoding input, derived by `positionedPart_branchSide` for the
actual complete allocator. It refers only to the native selected branch slot. -/
def NativeBranchSide (base : UpsPartI) (p : TreePart) : Prop :=
  p.kind=.RDB → (base.sd=0 ∨ base.sd=1) ∧ p.slot=edgeSlot base.sd

theorem trace_suffix_bounds {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (hw : t.wf=true) (hk : FixedSuffix key) (baseI : UpsInst) :
    (1≤(traceInstance baseI run v).ts ∧ (traceInstance baseI run v).ts≤3) ∧
      (traceInstance baseI run v).x<16 := by
  obtain ⟨d,hd,he,hm⟩ := traceUpsert_keys t key v run hr
  have hlen := hk.length
  have hterm : run.terminalKey.length≤2 := by rw [he,List.length_drop]; omega
  refine ⟨?_,splitNibble_lt (traceUpsert_sources t key v run hw hr).1⟩
  simp only [traceInstance,TreeRun.splitCursor,TreeRun.consumed,List.length_cons,List.length_nil]
  omega

mutual
/-- All twelve native constructors dispatch to ordinary byte semantics along the
whole runtime path, before source-id authentication and physical row allocation. -/
theorem traceUpsert_byteInputs : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.wf=true → FixedSuffix key → ∀ (baseI : UpsInst)
    (p : TreePart), p∈run.parts → ∀ base Q, encodeTreePart base p=some Q →
    NativeBranchSide base p → Nonempty (ByteInput (traceInstance baseI run v) Q)
  | .hash _, _, _, _, hr, _, _, _, _, _, _, _, _, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hw, hk, baseI, p, hp, base, Q, he, _ => by
    by_cases hkey : k=key
    · exact ⟨trace_value_byteInput hr hw hkey hk.length baseI hp base he⟩
    · simp only [traceUpsert,hkey,ite_false,Option.some.injEq] at hr
      subst run
      exact leafSplitRun_byteInput k s m key v hw hk hkey baseI p hp base Q he
  | .ext k c m, key, v, run, hr, hw, hk, baseI, p, hpart, base, Q, he, hside => by
    have bounds := trace_suffix_bounds hr hw hk baseI
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      exact extSplitRun_byteInput k c m key v hw hk hp baseI p hpart base Q he
    | true =>
      have hcwf : c.wf=true := by
        simp only [PTrie.wf,Bool.and_eq_true] at hw
        exact hw.1.1.2
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
          rcases hpart with hold|hnew
          · exact traceUpsert_byteInputs c (key.drop k.length) v inner hc hcwf (hk.drop _) baseI p hold base Q he hside
          · subst p
            exact ⟨treeExt_byteInput _ base k c m cm (key.drop k.length) v inner Q hc he hw bounds.1 bounds.2⟩
  | .branch bv cs m, [], v, run, hr, hw, hk, baseI, p, hp, base, Q, he, _ => by
    exact ⟨trace_value_byteInput hr hw rfl (by decide) baseI hp base he⟩
  | .branch bv cs m, n::key, v, run, hr, hw, hk, baseI, p, hpart, base, Q, he, hside => by
    have bounds := trace_suffix_bounds hr hw hk baseI
    have hcs : Kids.wf cs 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.2
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      cases hi : inner.inserted with
      | true =>
        have hkey : n::key=[0,15] ∨ n::key=[15] := by
          rcases hk with h|h|h
          · simp at h
          · exact Or.inr h
          · exact Or.inl h
        exact ⟨trace_insert_byteInput hc hi hw hkey baseI hpart base he⟩
      | false =>
        simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
        rcases hpart with hold|hnew
        · exact traceKids_byteInputs (.branch bv cs m) (n::key) cs 16 n key v inner hcs hc hi
            (by simpa using hk.drop 1) baseI p hold base Q he hside
        · subst p
          have hside' := hside (by simp [hi])
          have hn : n=edgeSlot base.sd := hside'.2
          refine ⟨treeRdb_byteInput _ base bv cs m key v inner Q ?_ hi ?_ hw hside'.1 bounds.1 bounds.2⟩
          · simpa only [←hn] using hc
          · simpa only [hi,Bool.false_eq_true,ite_false,←hn] using he

theorem traceKids_byteInputs : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), Kids.wf cs width=true →
    traceKids source wholeKey cs n key v=some run → run.inserted=false → FixedSuffix key →
    ∀ (baseI : UpsInst) (p : TreePart), p∈run.inner.parts → ∀ base Q,
    encodeTreePart base p=some Q → NativeBranchSide base p →
    Nonempty (ByteInput (traceInstance baseI run.inner v) Q)
  | _, _, .nil, _, _, _, _, _, _, hr, _, _, _, _, _, _, _, _, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, _, 0, key, v, run, _, hr, hi, _, _, _, _, _, _, _, _ => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; cases hi
  | source, wholeKey, .some child rest, width, 0, key, v, run, hw, hr, hi, hk, baseI, p, hp, base, Q, he, hside => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_byteInputs child key v inner hc hw.1.2 hk baseI p hp base Q he hside
  | source, wholeKey, .none rest, width, n+1, key, v, run, hw, hr, hi, hk, baseI, p, hp, base, Q, he, hside => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_byteInputs source wholeKey rest (width-1) n key v inner hw.2 hc hi hk baseI p hp base Q he hside
  | source, wholeKey, .some child rest, width, n+1, key, v, run, hw, hr, hi, hk, baseI, p, hp, base, Q, he, hside => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_byteInputs source wholeKey rest (width-1) n key v inner hw.2 hc hi hk baseI p hp base Q he hside
end
end ZkFormal.NearV3.Render.UpsGen
