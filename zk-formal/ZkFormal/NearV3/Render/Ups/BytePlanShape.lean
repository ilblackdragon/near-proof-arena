import ZkFormal.NearV3.Render.Ups.NativePrefixMetadata
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

/-- Newly created leaf header metadata follows from its ordinary remaining key. -/
theorem ByteInput.nlf_plan {I : UpsInst} {Q : UpsPartI} (data : ByteInput I Q) (hk : Q.kind=8) :
    Q.qhk=1 ∧ Q.qodd=(if I.ts=1 then 1 else 0) := by
  obtain ⟨hkey,hleaf⟩ := data.freshPrefix.leaf hk
  have hh := data.output.hplen
  have ho := data.output.odd
  have hts := data.freshPrefix.terminal
  cases hn : data.output.node with
  | ext => simp [hn,NodeGen3.isLeaf] at hleaf
  | branch => simp [hn,NodeGen3.isLeaf] at hleaf
  | leaf key val mem =>
    simp only [hn,NodeGen3.keyOf] at hkey
    rcases (show I.ts=1 ∨ I.ts=2 ∨ I.ts=3 by omega) with ht|ht|ht <;>
      simp_all [NodeGen3.hplenOf,NodeGen3.oddOf,NodeGen3.isLE,NodeGen3.keyOf]

/-- Wrapping extension metadata follows from the exact consumed prefix. -/
theorem ByteInput.wex_plan {I : UpsInst} {Q : UpsPartI} (data : ByteInput I Q)
    (types : PartTypeFacts Q) (hk : Q.kind=9) :
    Q.qhk=1+(if I.ts=3 ∧ I.ti=2 then 1 else 0) ∧ Q.qodd=(if I.ti=1 then 1 else 0) := by
  obtain ⟨hcases,hkey,hleaf⟩ := data.freshPrefix.wrap hk
  have hh := data.output.hplen
  have ho := data.output.odd
  have ht := (data.output.ty).symm.trans (types.tyExt (Or.inr (Or.inr (Or.inl hk))))
  cases hn : data.output.node with
  | leaf => simp [hn,nodeTypeCode] at ht
  | branch value kids mem => cases value <;> simp [hn,nodeTypeCode] at ht
  | ext key kid mem =>
    simp only [hn,NodeGen3.keyOf] at hkey
    rcases hcases with ⟨hts,hti⟩|⟨hts,hti⟩|⟨hts,hti⟩ <;>
      simp_all [NodeGen3.hplenOf,NodeGen3.oddOf,NodeGen3.isLE,NodeGen3.keyOf]

private theorem branchChildren_positive (value : Option NSlot3) (kids : List NKid) (mem : List Nat)
    (j : Nat) (hj : j<kids.length) (hn : kids.getD j .none≠.none) :
    0<nodeChildren (.branch value kids mem) := by
  have hm : kids.getD j .none∈kids := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
    exact List.getElem_mem hj
  have hf : kids.getD j .none∈kids.filter (·≠.none) := List.mem_filter.mpr ⟨hm,by simpa using hn⟩
  have hp : 0<(kids.filter (·≠.none)).length := List.length_pos_iff.mpr (by intro he; rw [he] at hf; exact List.not_mem_nil hf)
  change 0<(NodeGen3.branchWins kids).length
  simp only [NodeGen3.branchWins,List.length_map,List.length_zip,List.length_range,Nat.min_self]
  change 0<(NodeGen3.presentOf kids).length
  rw [NodeGen3.popK_eq]
  exact hp

/-- Every split branch has an occupied child slot; the no-child bit is therefore zero. -/
theorem ByteInput.spb_children {I : UpsInst} {Q : UpsPartI} (data : ByteInput I Q) (hk : Q.kind=10) :
    Q.nochild=0 := by
  have hex : ∃ j, j<16 ∧ (NodeGen3.kidsOf data.output.node).getD j .none≠.none := by
    by_cases hc : I.ci=4
    · refine ⟨splitNewSlot I,?_,?_⟩
      · unfold splitNewSlot; split <;> decide
      · apply (data.splitBitmap.slots hk _ (by unfold splitNewSlot; split <;> decide)).mpr
        exact Or.inr ⟨Or.inl hc,rfl⟩
    · exact ⟨I.x,data.splitBitmap.xbound,(data.splitBitmap.slots hk I.x data.splitBitmap.xbound).mpr (Or.inl ⟨hc,rfl⟩)⟩
  obtain ⟨j,hj,hkid⟩ := hex
  have hw := data.output.wf
  have hpos : 0<nodeChildren data.output.node := by
    cases hn : data.output.node with
    | leaf => simp [hn,NodeGen3.kidsOf] at hkid
    | ext => simp [nodeChildren]
    | branch value kids mem =>
      simp only [hn,NodeV3.wf] at hw
      simp only [hn,NodeGen3.kidsOf] at hkid
      exact branchChildren_positive value kids mem j (by omega) hkid
  rw [data.nochild]
  simp [show nodeChildren data.output.node≠0 by omega]
end ZkFormal.NearV3.Render.UpsGen
