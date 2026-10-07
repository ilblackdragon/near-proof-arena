import ZkFormal.NearV3.Render.Ups.TreePrefixShapes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def nativeHplen (t : PTrie) : Nat := match t with
  | .leaf key .. | .ext key .. => 1+key.length/2
  | _ => 0

def nativeOdd (t : PTrie) : Nat := match t with
  | .leaf key .. | .ext key .. => key.length%2
  | _ => 0

theorem nativeOdd_bit (t : PTrie) : nativeOdd t≤1 := by cases t <;> simp [nativeOdd] <;> omega

theorem native_prefix_length (t : PTrie) (h : nativeNodeType t≤1) :
    2*nativeHplen t+nativeOdd t=(nativeKey t).length+2 := by
  cases t with
  | hash => simp [nativeNodeType] at h
  | leaf => simp [nativeHplen,nativeOdd,nativeKey]; omega
  | ext => simp [nativeHplen,nativeOdd,nativeKey]; omega
  | branch value kids mem => cases value <;> simp [nativeNodeType] at h

theorem native_prefix_of_nonempty (t : PTrie) (h : nativeKey t≠[]) : nativeNodeType t≤1 := by
  cases t <;> simp_all [nativeKey,nativeNodeType]

theorem treeNode_prefix {t : PTrie} {node : NodeV3} (he : treeNode t=some node) :
    NodeGen3.hplenOf node=nativeHplen t ∧ NodeGen3.oddOf node=nativeOdd t := by
  cases t with
  | hash => simp [treeNode] at he
  | leaf => simp [treeNode] at he; subst node; exact ⟨rfl,rfl⟩
  | ext => simp [treeNode] at he; subst node; exact ⟨rfl,rfl⟩
  | branch value kids mem => simp [treeNode] at he; subst node; exact ⟨rfl,rfl⟩

theorem encodeTreePart_prefix {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) :
    Q.qhk=nativeHplen part.output ∧ Q.qodd=nativeOdd part.output ∧
    Q.phk=nativeHplen part.source ∧ Q.podd=nativeOdd part.source := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q
  exact ⟨(treeNode_prefix hd).1,(treeNode_prefix hd).2,(treeNode_prefix hs).1,(treeNode_prefix hs).2⟩

structure PartNativePrefixFacts (I : UpsInst) (Q : UpsPartI) : Prop where
  tySpb : Q.kind=10 → (Q.ty=3 ↔ I.ci=4 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
  pt : Q.kind=11 → Q.qhk=1 ∧ Q.qodd=0
  mv : Q.kind=6 ∨ Q.kind=7 → 2*Q.qhk+Q.qodd+I.ti+1=2*Q.phk+Q.podd
  mveOdd : Q.kind=7 → Q.ty≤1 → Q.qhk=1 → Q.qodd=1
  xcp : Q.kind=10 → (I.ci=8 ∨ I.ci=10) → 2*Q.phk+Q.podd=I.ti+3

theorem trace_nativePrefixFacts {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (baseI : UpsInst) {part : TreePart} (hp : part∈run.parts)
    {base Q : UpsPartI} (he : encodeTreePart base part=some Q) :
    PartNativePrefixFacts (traceInstance baseI run v) Q := by
  have hs := traceUpsert_prefixShapes t key v run hr part hp
  have ht := trace_encoded_typeFacts hr hp he
  have htype := encodeTreePart_type he
  have hk := encodeTreePart_kind he
  obtain ⟨hqh,hqo,hph,hpo⟩ := encodeTreePart_prefix he
  have hodd := nativeOdd_bit part.output
  constructor
  · intro h
    have hkind : part.kind=.SPB := by cases hc : part.kind <;> simp_all [UKind.ix]
    have hv := hs.2.2.2.2 hkind
    rw [htype]
    change nativeNodeType part.output=3 ↔ run.terminal.ix=4 ∨ run.terminal.ix=5 ∨
      run.terminal.ix=7 ∨ run.terminal.ix=8
    simpa only [show (run.terminal.ix=4 ∨ run.terminal.ix=5 ∨ run.terminal.ix=7 ∨ run.terminal.ix=8)↔
      run.terminal∈[UCase.LSa,UCase.LSb,UCase.ESl0,UCase.ESl1] by cases run.terminal <;> decide] using hv
  · intro h
    have hkind : part.kind=.PT := by cases hc : part.kind <;> simp_all [UKind.ix]
    have hkey := hs.2.2.1 hkind
    have hty : nativeNodeType part.output=1 := by rw [←htype]; exact ht.tyExt (Or.inr (Or.inr (Or.inr h)))
    cases ho : part.output with
    | branch value kids mem => cases value <;> simp_all [nativeNodeType]
    | hash => simp_all [nativeNodeType]
    | leaf => simp_all [nativeNodeType]
    | ext => simp_all [nativeNodeType,nativeKey,nativeHplen,nativeOdd]
  · intro h
    have hkind : part.kind=.MVL ∨ part.kind=.MVE := by cases hc : part.kind <;> simp_all [UKind.ix]
    have hlen := hs.1 hkind
    have hn : nativeKey part.source≠[] := by intro hz; rw [hz,List.length_nil] at hlen; omega
    have hsrc := native_prefix_length part.source (native_prefix_of_nonempty part.source hn)
    have hdst : nativeNodeType part.output≤1 := by
      rw [←htype]
      rcases h with h|h
      · rw [ht.tyLeaf (Or.inr (Or.inl h))]; decide
      · rw [ht.tyExt (Or.inr (Or.inl h))]; decide
    have hout := native_prefix_length part.output hdst
    change 2*Q.qhk+Q.qodd+run.matched+1=2*Q.phk+Q.podd
    omega
  · intro h _ hhead
    have hkind : part.kind=.MVE := by cases hc : part.kind <;> simp_all [UKind.ix]
    have hn := List.length_pos_iff.mpr (hs.2.1 hkind)
    have hdst : nativeNodeType part.output≤1 := by
      rw [←htype,ht.tyExt (Or.inr (Or.inl h))]; decide
    have hout := native_prefix_length part.output hdst
    omega
  · intro h hc
    have hkind : part.kind=.SPB := by cases hc : part.kind <;> simp_all [UKind.ix]
    have hcase : run.terminal=.ESl1 ∨ run.terminal=.ESn1 := by
      change run.terminal.ix=8 ∨ run.terminal.ix=10 at hc
      cases ht : run.terminal <;> simp_all [UCase.ix,UKind.ix]
    have hlen := hs.2.2.2.1 hkind hcase
    have hn : nativeKey part.source≠[] := by intro hz; rw [hz,List.length_nil] at hlen; omega
    have hsrc := native_prefix_length part.source (native_prefix_of_nonempty part.source hn)
    change 2*Q.phk+Q.podd=run.matched+3
    omega
end ZkFormal.NearV3.Render.UpsGen
