import ZkFormal.NearV3.Render.Ups.TreeSourceChain
import ZkFormal.NearV3.Render.Ups.TreeEncodedBounds
import ZkFormal.NearV3.Render.Ups.SplitMatched
import ZkFormal.NearV3.Render.Ups.TreeInsertMemoryDispatch
import ZkFormal.NearV3.Render.Ups.TreeByteAssembly

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

mutual
/-- All terminal and split memory inputs are derived along the complete native path. -/
theorem traceUpsert_terminalMemOk : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.wf=true → FixedSuffix key → v.length<2^24 →
    ∀ (baseI : UpsInst) (p : TreePart), p∈run.parts → ∀ base Q,
    encodeTreePart base p=some Q → ¬upperKind p.kind → Q.mB=splitChildMemory run.matched p →
    Q.qhk<2^22 → Q.phk<2^22 → SourceBytes (child (traceInstance baseI run v) Q) →
    MemOk (traceInstance baseI run v) (withMemorySign (traceInstance baseI run v) Q)
  | .hash _, _, _, _, hr, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hw, hk, hv, baseI, p, hp, base, Q, he, _, hm, hq, hph, hchild => by
    by_cases hkey : k=key
    · exact trace_value_memOk hr hw hkey hk.length hv baseI hp base he hchild
    · simp only [traceUpsert,hkey,ite_false,Option.some.injEq] at hr
      subst run
      rw [leafSplitRun_matched k s m key v hkey] at hm
      obtain ⟨data⟩ := leafSplitRun_byteMemory k s m key v hw hk hkey hv baseI p hp base Q he hm hq hph hchild
      exact data.memory
  | .ext k c m, key, v, run, hr, hw, hk, hv, baseI, p, hpart, base, Q, he, hu, hmB, hq, hph, hchild => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      rw [extSplitRun_matched] at hmB
      obtain ⟨data⟩ := extSplitRun_byteMemory k c m key v hw hk hp hv baseI p hpart base Q he hmB hq hph hchild
      exact data.memory
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
          · exact traceUpsert_terminalMemOk c (key.drop k.length) v inner hc hcwf (hk.drop _) hv baseI p hold base Q he hu hmB hq hph hchild
          · subst p
            exfalso; apply hu
            cases k <;> simp [upperKind]
  | .branch bv cs m, [], v, run, hr, hw, hk, hv, baseI, p, hp, base, Q, he, _, _, _, _, hchild => by
    exact trace_value_memOk hr hw rfl (by decide) hv baseI hp base he hchild
  | .branch bv cs m, n::key, v, run, hr, hw, hk, hv, baseI, p, hpart, base, Q, he, hu, hmB, hq, hph, hchild => by
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
        have hmb : base.mB<2^74 := by
          have hin := (traceKids_inserted _ _ _ _ _ _ _ hc hi).2.2
          have hparts := hpart
          simp only [pushPart,hin,terminalRun,List.mem_append,List.mem_singleton] at hparts
          have hb := encodeTreePart_mB he
          rcases hparts with rfl|rfl <;> simp [hi,splitChildMemory] at hmB <;> omega
        exact (trace_insert_byteMemory hc hi hw hkey hv baseI hpart base he hmb hchild).memory
      | false =>
        simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
        rcases hpart with hold|hnew
        · exact traceKids_terminalMemOk (.branch bv cs m) (n::key) cs 16 n key v inner hcs hc hi
            (by simpa using hk.drop 1) hv baseI p hold base Q he hu hmB hq hph hchild
        · subst p
          exact (hu (by simp [hi,upperKind])).elim

theorem traceKids_terminalMemOk : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), Kids.wf cs width=true →
    traceKids source wholeKey cs n key v=some run → run.inserted=false → FixedSuffix key → v.length<2^24 →
    ∀ (baseI : UpsInst) (p : TreePart), p∈run.inner.parts → ∀ base Q,
    encodeTreePart base p=some Q → ¬upperKind p.kind → Q.mB=splitChildMemory run.inner.matched p →
    Q.qhk<2^22 → Q.phk<2^22 → SourceBytes (child (traceInstance baseI run.inner v) Q) →
    MemOk (traceInstance baseI run.inner v) (withMemorySign (traceInstance baseI run.inner v) Q)
  | _, _, .nil, _, _, _, _, _, _, hr, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, _, 0, key, v, run, _, hr, hi, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; cases hi
  | source, wholeKey, .some child rest, width, 0, key, v, run, hw, hr, hi, hk, hv, baseI, p, hp, base, Q, he, hu, hmB, hq, hph, hchild => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_terminalMemOk child key v inner hc hw.1.2 hk hv baseI p hp base Q he hu hmB hq hph hchild
  | source, wholeKey, .none rest, width, n+1, key, v, run, hw, hr, hi, hk, hv, baseI, p, hp, base, Q, he, hu, hmB, hq, hph, hchild => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalMemOk source wholeKey rest (width-1) n key v inner hw.2 hc hi hk hv baseI p hp base Q he hu hmB hq hph hchild
  | source, wholeKey, .some child rest, width, n+1, key, v, run, hw, hr, hi, hk, hv, baseI, p, hp, base, Q, he, hu, hmB, hq, hph, hchild => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalMemOk source wholeKey rest (width-1) n key v inner hw.2 hc hi hk hv baseI p hp base Q he hu hmB hq hph hchild
end
end ZkFormal.NearV3.Render.UpsGen
