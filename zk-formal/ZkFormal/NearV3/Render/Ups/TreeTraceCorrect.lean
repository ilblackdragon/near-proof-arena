import ZkFormal.NearV3.Render.Ups.TreeTrace

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

@[simp] theorem wrapRun_output (src : PTrie) (path : List Nat) (run : TreeRun) :
    (wrapRun src path run).output=wrapExt path run.output := by
  cases path <;> rfl

@[simp] theorem leafSplitRun_output (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).output=splitLeaf k s key v := by
  unfold leafSplitRun splitLeaf
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp [h1,h2,wrapRun_output,terminalRun]

@[simp] theorem extSplitRun_output (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).output=splitExt k c m key v := by
  unfold extSplitRun splitExt
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp [h1,h2,wrapRun_output,terminalRun] <;> cases xs <;> rfl

mutual
/-- Erasing instrumentation is exactly the actual runtime upsert, on every input. -/
theorem traceUpsert_output : ∀ (t : PTrie) (key : List Nat) (v : Bytes),
    (traceUpsert t key v).map TreeRun.output=t.upsert key v
  | .hash _, _, _ => rfl
  | .leaf k s m, key, v => by
    by_cases h : k=key <;> simp [traceUpsert,PTrie.upsert,h,terminalRun]
  | .ext k c m, key, v => by
    have ih := traceUpsert_output c (key.drop k.length) v
    cases hp : isPrefix k key
    · simp [traceUpsert,PTrie.upsert,hp]
    · cases hm : c.mem? <;> cases hr : traceUpsert c (key.drop k.length) v <;>
        simp [hr] at ih <;> simp [traceUpsert,PTrie.upsert,hp,hm,hr,←ih,pushPart,qRDE]
  | .branch bv cs m, [], v => by
    cases bv <;> simp [traceUpsert,PTrie.upsert,terminalRun]
  | .branch bv cs m, n::key, v => by
    have ih := traceKids_output (.branch bv cs m) (n::key) cs n key v
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v <;>
      simp [hr] at ih <;> simp [traceUpsert,PTrie.upsert,hr,←ih,pushPart]
theorem traceKids_output : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes),
    (traceKids source wholeKey cs n key v).map (fun run => (run.output,run.oldMem,run.newMem))=
      Kids.upsert cs n key v
  | _, _, .nil, _, _, _ => rfl
  | _, _, .none rest, 0, key, v => rfl
  | source, wholeKey, .some c rest, 0, key, v => by
    have ih := traceUpsert_output c key v
    cases hm : c.mem? <;> cases hr : traceUpsert c key v <;>
      simp [hr] at ih <;> simp [traceKids,Kids.upsert,hm,hr,←ih]
  | source, wholeKey, .none rest, n+1, key, v => by
    have ih := traceKids_output source wholeKey rest n key v
    cases hr : traceKids source wholeKey rest n key v <;>
      simp [hr] at ih <;> simp [traceKids,Kids.upsert,hr,←ih]
  | source, wholeKey, .some c rest, n+1, key, v => by
    have ih := traceKids_output source wholeKey rest n key v
    cases hr : traceKids source wholeKey rest n key v <;>
      simp [hr] at ih <;> simp [traceKids,Kids.upsert,hr,←ih]
end

/-- Every successful runtime upsert has an executable instrumented witness. -/
theorem traceUpsert_complete {t result : PTrie} {key : List Nat} {v : Bytes}
    (h : t.upsert key v=some result) :
    ∃run,traceUpsert t key v=some run ∧ run.output=result := by
  have he := traceUpsert_output t key v
  rw [h] at he
  cases ht : traceUpsert t key v with
  | none => simp [ht] at he
  | some run => exact ⟨run,rfl,by simpa [ht] using he⟩

end ZkFormal.NearV3.Render.UpsGen
