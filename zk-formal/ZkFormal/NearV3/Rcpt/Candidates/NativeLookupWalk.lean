import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupChain

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

def nativeLookupWalk (wid tau nid : Nat) (tree : PTrie) (steps : List WStep3) : WalkR :=
  ⟨wid,tau,lookupEdge 0 SYM_START [0,tau,SYM_START,viewTarget nid tree,0,EK_DOWN]::steps⟩

theorem nativeLookupWalk_length (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (h : nativeLookupSteps nid vid tree key=some steps) :
    (nativeLookupWalk wid tau nid tree steps).steps.length=key.length+2 := by
  have hh:=nativeLookupSteps_length nid vid tree key steps h
  simp [nativeLookupWalk,hh,Nat.add_assoc]

theorem nativeLookupWalk_symbols (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (h : nativeLookupSteps nid vid tree key=some steps) :
    (nativeLookupWalk wid tau nid tree steps).steps.map WStep3.sym=SYM_START::(key++[SYM_END]) := by
  simp only [nativeLookupWalk,List.map_cons,lookupEdge,nativeLookupSteps_symbols nid vid tree key steps h]

theorem nativeLookupWalk_rows (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (hw : tree.wf=true) (hk : ∀a∈key,a<16)
    (h : nativeLookupSteps nid vid tree key=some steps) :
    ∀i (hi : i<(nativeLookupWalk wid tau nid tree steps).steps.length),
      StepOk (nativeLookupWalk wid tau nid tree steps).steps[i]
        (i+1==(nativeLookupWalk wid tau nid tree steps).steps.length) := by
  apply lookupRows_indexed
  apply lookupRows_prefix [_] steps
  · intro s hs
    simp only [List.mem_singleton] at hs;subst s
    constructor <;> simp [lookupEdge]
  · exact nativeLookupSteps_rows nid vid tree key steps hw hk h
  · have hh:=nativeLookupSteps_length nid vid tree key steps h;omega

theorem nativeLookupWalk_chain (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (h : nativeLookupSteps nid vid tree key=some steps) :
    lookupChain (nativeLookupWalk wid tau nid tree steps).steps := by
  apply lookupChain_append [_] steps trivial (nativeLookupSteps_chain nid vid tree key steps h)
  intro a b ha hb
  simp only [List.getLast?_singleton,Option.some.injEq] at ha;subst a
  have hf:=nativeLookupSteps_first nid vid tree key steps b h hb
  exact lookupNext_matched _ b rfl (by simpa [lookupEdge] using hf.1) hf.2

theorem nativeLookupWalk_start (wid tau nid : Nat) (tree : PTrie) (steps : List WStep3) :
    ((nativeLookupWalk wid tau nid tree steps).step 0).mode=0 ∧
    ((nativeLookupWalk wid tau nid tree steps).step 0).sym=SYM_START ∧
    ((nativeLookupWalk wid tau nid tree steps).step 0).e.getD 1 0=tau := by
  simp [WalkR.step,nativeLookupWalk,lookupEdge]

/-- Exact row/chain assembly; payload canonicality is an explicit remaining provider obligation. -/
theorem nativeLookupWalk_wf (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (hw : tree.wf=true) (hk : ∀a∈key,a<16)
    (h : nativeLookupSteps nid vid tree key=some steps)
    (hwid : wid<P) (htau : tau<P) (hroot : viewTarget nid tree<P)
    (hc : ∀s∈steps,s.sym<P ∧ s.u<P ∧ s.ub<P ∧ ∀x∈s.e,x<P)
    (hn : key.length+2≤2^23) : WalkWf3 [nativeLookupWalk wid tau nid tree steps] := by
  constructor
  · intro w hm
    simp only [List.mem_singleton] at hm;subst w
    rw [nativeLookupWalk_length wid tau nid vid tree key steps h];omega
  · intro w hm
    simp only [List.mem_singleton] at hm;subst w
    refine ⟨hwid,htau,?_⟩
    intro s hs
    simp only [nativeLookupWalk,List.mem_cons] at hs
    rcases hs with rfl|hs
    · simp [lookupEdge,SYM_START,EK_DOWN,htau,hroot];decide
    · exact hc s hs
  · intro w hm
    simp only [List.mem_singleton] at hm;subst w
    exact nativeLookupWalk_rows wid tau nid vid tree key steps hw hk h
  · intro w hm
    simp only [List.mem_singleton] at hm;subst w
    exact nativeLookupWalk_start wid tau nid tree steps
  · intro w hm i hi
    simp only [List.mem_singleton] at hm;subst w
    have hh:=(lookupChain_indexed _).mp (nativeLookupWalk_chain wid tau nid vid tree key steps h) i hi
    have hi0 : i<(nativeLookupWalk wid tau nid tree steps).steps.length := by omega
    simpa only [WalkR.step,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi0,
      List.getElem?_eq_getElem hi,Option.getD_some,lookupNext] using hh
  · simpa [List.flatMap_cons,List.flatMap_nil,nativeLookupWalk_length wid tau nid vid tree key steps h] using hn

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
