import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupLeafChain

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem lookupRows_prefix (pre tail : List WStep3)
    (hp : ∀s∈pre,StepOk s false) (ht : lookupRows tail) (hn : 0<tail.length) :
    lookupRows (pre++tail) := by
  induction pre with
  | nil=>exact ht
  | cons s rest ih=>
    have hr:=ih (fun t hm=>hp t (by simp [hm]))
    have hpos : 0<(rest++tail).length := by simp only [List.length_append];omega
    cases he : rest++tail with
    | nil=>simp [he] at hpos
    | cons t ts=>
      change lookupRows (s::(rest++tail))
      rw [he]
      exact ⟨hp s (by simp),by simpa [he] using hr⟩

theorem lookupExtensionEdges_rows (nid target : Nat) (key : List Nat) :
    ∀s∈lookupExtensionEdges nid target key,StepOk s false := by
  intro s hs
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hs
  constructor <;> simp [lookupEdge]

theorem nativeLookup_extension_rows (nid vid : Nat) (stored : List Nat) (child : PTrie)
    (mem : Nat) (key : List Nat) (steps : List WStep3)
    (hs : ∀a∈stored,a<16) (hk : ∀a∈key,a<16)
    (hc : ∀tail,nativeLookupSteps (nid+1) vid child (key.drop stored.length)=some tail→lookupRows tail)
    (h : nativeLookupSteps nid vid (.ext stored child mem) key=some steps) : lookupRows steps := by
  cases hp : isPrefix stored key with
  | false=>
    simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
    cases he : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
    | none=>simp [he] at h
    | some raw=>
      simp only [he,Option.map_some,Option.some.injEq] at h;rw [←h]
      exact extensionMismatchFix_rows nid child stored.length raw
        (leafLookupSteps_rows nid vid (.ref 0 []) 0 stored key raw hs hk he)
  | true=>
    simp only [nativeLookupSteps,hp,ite_true] at h
    cases ht : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
    | none=>simp [ht] at h
    | some tail=>
      simp only [ht,Option.map_some,Option.some.injEq] at h
      rw [←h]
      exact lookupRows_prefix _ tail (lookupExtensionEdges_rows _ _ _) (hc tail ht)
        (by have hh:=nativeLookupSteps_length (nid+1) vid child _ tail ht;omega)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
