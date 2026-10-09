import ZkFormal.NearV3.Assembly.SourceCoverage

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly

mutual
/-- A property of every revealed occurrence covers every actual search path. -/
theorem pathCovered_of_occs (P : PTrie→Prop) (hh : ∀ h,P (.hash h)) :
    ∀ t key,(∀ a∈occs t,P a) → PathCovered P t key
  | .hash h,key,_ => hh h
  | .leaf k s m,key,h => h _ (by simp [occs])
  | .ext k c m,key,h => by
    refine ⟨h _ (by simp [occs]),?_⟩
    intro _
    exact pathCovered_of_occs P hh c _ (fun a ha=>h a (by simp [occs,ha]))
  | .branch sv kids m,[],h => h _ (by simp [occs])
  | .branch sv kids m,slot::key,h => by
    refine ⟨h _ (by simp [occs]),?_⟩
    exact kidsCovered_of_occs P hh kids slot key (fun a ha=>h a (by simp [occs,ha]))
theorem kidsCovered_of_occs (P : PTrie→Prop) (hh : ∀ h,P (.hash h)) :
    ∀ kids slot key,(∀ a∈kOccs kids,P a) → KidsCovered P kids slot key
  | .nil,_,_,_ => True.intro
  | .none _,0,_,_ => True.intro
  | .some c rest,0,key,h => pathCovered_of_occs P hh c key (fun a ha=>h a (by simp [kOccs,ha]))
  | .none rest,slot+1,key,h => kidsCovered_of_occs P hh rest slot key h
  | .some c rest,slot+1,key,h => kidsCovered_of_occs P hh rest slot key (fun a ha=>h a (by simp [kOccs,ha]))
end

/-- Every emitted source, including repeated split sources, is an actual revealed
occurrence of the input trie. No distinctness or normalization assumption is needed. -/
theorem traceUpsert_source_occurrence {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {p : TreePart} (hp : p∈run.parts) :
    p.source∈occs root := by
  let P := fun t=>isNode t=true → t∈occs root
  have hpath : PathCovered P root key := pathCovered_of_occs P
    (fun h hn=>by simp [isNode] at hn) root key (fun a ha _=>ha)
  have hcovered := traceUpsert_covered P root key value run hpath hr
  exact hcovered.2 p hp ((traceUpsert_nodeParts root key value run hr p hp).1)
end ZkFormal.NearV3.Render.UpsGen
