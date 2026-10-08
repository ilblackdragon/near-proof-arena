import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionFix

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- All matched extension edges; the last edge targets the resolved child. -/
def lookupExtensionEdges (nid target : Nat) (key : List Nat) : List WStep3 :=
  (List.range key.length).map (fun i=>lookupEdge 0 (key.getD i 0)
    [nid,i,key.getD i 0,if i+1=key.length then target else nid,
      if i+1=key.length then 0 else i+1,EK_KEY])

def lookupBranchAbsent (nid bm hv sym : Nat) (rest : List Nat) : List WStep3 :=
  ⟨2,sym,[nid,0,0,0,0,0],0,bm,hv,0⟩::lookupDrain rest

mutual
/-- Executable arbitrary-key native lookup, using occurrence-based compact IDs. -/
def nativeLookupSteps (nid vid : Nat) : PTrie→List Nat→Option (List WStep3)
  | .hash _,_=>none
  | .leaf stored slot _,key=>leafLookupSteps nid vid slot 0 stored key
  | .ext stored child _,key=>if isPrefix stored key then
      (nativeLookupSteps (nid+1) vid child (key.drop stored.length)).map
        (lookupExtensionEdges nid (viewTarget (nid+1) child) stored++·)
    else (leafLookupSteps nid vid (.ref 0 []) 0 stored key).map (extensionMismatchFix nid child stored.length)
  | .branch value kids _,[]=>match value with
    | none=>some [⟨2,SYM_END,[nid,0,0,0,0,0],0,kidsBitmap kids 0,0,0⟩]
    | some (.ref _ _)=>none
    | some (.val _)=>some [lookupEdge 0 SYM_END [nid,0,SYM_END,vid,0,EK_VAL]]
  | .branch value kids _,x::xs=>nativeKidsLookupSteps nid (kidsBitmap kids 0)
      (if value.isSome then 1 else 0) x (nid+1) (vid+(optSlotVal value).length) kids x xs
/-- Child cursor IDs advance over every earlier revealed occurrence/value. -/
def nativeKidsLookupSteps (parent bm hv sym nid vid : Nat) : Kids→Nat→List Nat→Option (List WStep3)
  | .nil,_,key=>some (lookupBranchAbsent parent bm hv sym key)
  | .none _,0,key=>some (lookupBranchAbsent parent bm hv sym key)
  | .some child _,0,key=>(nativeLookupSteps nid vid child key).map
      (lookupEdge 0 sym [parent,0,sym,viewTarget nid child,0,EK_DOWN]::·)
  | .none rest,j+1,key=>nativeKidsLookupSteps parent bm hv sym nid vid rest j key
  | .some child rest,j+1,key=>nativeKidsLookupSteps parent bm hv sym
      (nid+tsize child) (vid+(valsOf child).length) rest j key
end

private theorem prefix_self : ∀key : List Nat,isPrefix key key=true
  | []=>rfl
  | x::xs=>by simp [isPrefix,prefix_self xs]

mutual
/-- Defined paths coincide with native proven lookup; unknown hashes stay unknown. -/
theorem nativeLookupSteps_defined (nid vid : Nat) : ∀tree key,
    (nativeLookupSteps nid vid tree key).isSome=(tree.find key).isSome
  | .hash _,_=>rfl
  | .leaf stored slot mem,key=>leafLookupSteps_defined nid vid slot 0 stored key
  | .ext stored child mem,key=>by
    cases hp : isPrefix stored key with
    | true=>simpa [nativeLookupSteps,PTrie.find,hp] using
        nativeLookupSteps_defined (nid+1) vid child (key.drop stored.length)
    | false=>
      have he : stored≠key := by intro he;subst key;rw [prefix_self] at hp;cases hp
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false,Option.isSome_map]
      rw [leafLookupSteps_defined]
      simp [PTrie.find,hp,he]
  | .branch value kids mem,[]=>by cases value with
    | none=>rfl
    | some v=>cases v <;> rfl
  | .branch value kids mem,x::xs=>nativeKidsLookupSteps_defined _ _ _ _ _ _ kids x xs

theorem nativeKidsLookupSteps_defined (parent bm hv sym nid vid : Nat) : ∀kids j key,
    (nativeKidsLookupSteps parent bm hv sym nid vid kids j key).isSome=(Kids.find kids j key).isSome
  | .nil,_,_=>rfl
  | .none _,0,_=>rfl
  | .some child _,0,key=>by
    simpa [nativeKidsLookupSteps,Kids.find] using nativeLookupSteps_defined nid vid child key
  | .none rest,j+1,key=>nativeKidsLookupSteps_defined parent bm hv sym nid vid rest j key
  | .some child rest,j+1,key=>nativeKidsLookupSteps_defined parent bm hv sym
      (nid+tsize child) (vid+(valsOf child).length) rest j key
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
