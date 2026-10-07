import ZkFormal.NearV3.Assembly.TrieShapeUpsert

namespace ZkFormal.NearV3.Assembly
open NearSpec

/-- Exact native lookup update under the minimal preserved structural invariant. -/
theorem shape_upsert_find {pre post : PTrie} {key query : List Nat} {value : Bytes}
    (hs : TrieShape pre) (hk : nibblesOk key=true) (hu : pre.upsert key value=some post) :
    post.find query=if query=key then some (some value) else pre.find query := by
  by_cases he : query=key
  · subst query
    simpa using PTrie.find_upsert_self pre key value post hk hu
  · simpa [he] using shape_find_upsert_other pre key query value post hs hk he hu

theorem shape_upsert_known {pre post : PTrie} {key query : List Nat} {value : Bytes}
    (hs : TrieShape pre) (hk : nibblesOk key=true) (hu : pre.upsert key value=some post)
    (hq : pre.find query≠none) : post.find query≠none := by
  rw [shape_upsert_find hs hk hu]
  split
  · simp
  · exact hq

/-- A concrete sequence of the unchanged native upsert function. -/
def runWrites : PTrie → List (List Nat × Bytes) → Option PTrie
  | t,[] => some t
  | t,(key,value)::rest => (t.upsert key value).bind (fun u => runWrites u rest)

theorem runWrites_shape_known {pre post : PTrie} {writes : List (List Nat × Bytes)}
    (hs : TrieShape pre) (hk : ∀ w ∈ writes, nibblesOk w.1=true)
    (hr : runWrites pre writes=some post) :
    TrieShape post ∧ ∀ query, pre.find query≠none → post.find query≠none := by
  induction writes generalizing pre with
  | nil =>
    simp only [runWrites,Option.some.injEq] at hr
    subst post
    exact ⟨hs,fun _ h => h⟩
  | cons w writes ih =>
    obtain ⟨key,value⟩ := w
    simp only [runWrites] at hr
    cases hu : pre.upsert key value with
    | none => simp [hu] at hr
    | some mid =>
      simp only [hu,Option.bind_some] at hr
      have hkey := hk (key,value) (by simp)
      have hmid := shape_upsert pre key value mid hs hkey hu
      obtain ⟨hout,hknown⟩ := ih hmid (fun w hw => hk w (by simp [hw])) hr
      exact ⟨hout,fun query hq => hknown query (shape_upsert_known hs hkey hu hq)⟩

theorem wf_runWrites_known {pre post : PTrie} {writes : List (List Nat × Bytes)}
    (hw : pre.wf=true) (hk : ∀ w ∈ writes, nibblesOk w.1=true)
    (hr : runWrites pre writes=some post) (query : List Nat) (hq : pre.find query≠none) :
    post.find query≠none :=
  (runWrites_shape_known (TrieShape.of_wf pre hw) hk hr).2 query hq

end ZkFormal.NearV3.Assembly
