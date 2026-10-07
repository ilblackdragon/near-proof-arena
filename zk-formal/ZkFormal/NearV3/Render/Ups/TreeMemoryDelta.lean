import ZkFormal.NearV3.Render.Ups.TreeOutputChain
import ZkFormal.NearV3.Render.Ups.TreeExistingTrace

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

/-- Exact native arithmetic at an upper update; truncation is applied only by serialization. -/
def NativeDelta (p : TreePart) : Prop := upperKind p.kind →
  ∃ oldChild newChild, sourcePathChild p=some oldChild ∧ outputPathChild p=some newChild ∧
    p.output.memD=p.source.memD+newChild.memD-oldChild.memD

def NativeDeltas (parts : List TreePart) : Prop := ∀ p∈parts,NativeDelta p

theorem NativeDeltas.append {parts : List TreePart} {p : TreePart}
    (h : NativeDeltas parts) (hp : NativeDelta p) : NativeDeltas (parts++[p]) := by
  intro q hq
  simp only [List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  exact h q hq
  exact hp

theorem leafSplitRun_deltas (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    NativeDeltas (leafSplitRun k s m key v).parts := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [NativeDeltas,NativeDelta,upperKind,terminalRun,wrapRun,pushPart]

theorem extSplitRun_deltas (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    NativeDeltas (extSplitRun k c m key v).parts := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,NativeDeltas,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [NativeDeltas,NativeDelta,upperKind,terminalRun,wrapRun,pushPart]

mutual
/-- Native execution determines every upper arithmetic transition even when
accepted source parent/child memory fields are inconsistent. -/
theorem traceUpsert_deltas : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.wf=true → NativeDeltas run.parts
  | .hash _, _, _, _, hr, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hw => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [terminalRun,NativeDeltas,NativeDelta,upperKind]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_deltas k s m key v
  | .ext k c m, key, v, run, hr, hw => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_deltas k c m key v
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
          apply NativeDeltas.append (traceUpsert_deltas c _ v inner hc hcwf)
          intro _
          refine ⟨c,inner.output,rfl,rfl,?_⟩
          change m+inner.output.memD-cm=m+inner.output.memD-c.memD
          simp [PTrie.memD,hm]
  | .branch bv cs m, [], v, run, hr, _ => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run; cases bv <;> simp [terminalRun,NativeDeltas,NativeDelta,upperKind]
  | .branch bv cs m, n::key, v, run, hr, hw => by
    have hcs : Kids.wf cs 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.2
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      apply NativeDeltas.append (traceKids_deltas (.branch bv cs m) (n::key) cs 16 n key v inner hc hcs)
      intro hu
      cases hi : inner.inserted with
      | true => simp [hi,upperKind] at hu
      | false =>
        let e := traceKids_existing (.branch bv cs m) (n::key) cs 16 n key v inner hcs hc hi
        have hold := traceKids_childSource (.branch bv cs m) (n::key) cs n key v inner hc hi
        rw [traceUpsert_rootSource e.trace] at hold
        refine ⟨e.node,inner.inner.output,hold.symm,traceKids_newChild _ _ _ _ _ _ _ hc,?_⟩
        simp [PTrie.memD,PTrie.mem?,e.oldMem,e.newMem]

theorem traceKids_deltas : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → Kids.wf cs width=true → NativeDeltas run.inner.parts
  | _, _, .nil, _, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, _, 0, key, v, run, hr, _ => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [terminalRun,NativeDeltas,NativeDelta,upperKind]
  | source, wholeKey, .some child rest, width, 0, key, v, run, hr, hw => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_deltas child key v inner hc hw.1.2
  | source, wholeKey, .none rest, width, n+1, key, v, run, hr, hw => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_deltas source wholeKey rest (width-1) n key v inner hc hw.2
  | source, wholeKey, .some child rest, width, n+1, key, v, run, hr, hw => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_deltas source wholeKey rest (width-1) n key v inner hc hw.2
end
end ZkFormal.NearV3.Render.UpsGen
