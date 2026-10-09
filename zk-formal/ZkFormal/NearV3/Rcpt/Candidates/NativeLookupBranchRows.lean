import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionRows
import ZkFormal.NearV3.Render.Ups.NativeWalkBitmap
import ZkFormal.NearV3.Spec.Codec

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem native_absent_bitmap (kids : Kids) (sym : Nat) (h : nativeChildAt kids sym=none) :
    kidsBitmap kids 0 / 2^sym % 2=0 := by
  have habs:=(nativeChildAt_none_iff kids sym).mpr h
  have hbit : Near.Render.NodeGen.bitOf (kidBitmap (treeKids kids)) sym=0 := by
    rw [Render.NodeGen3.bitOf_kidBitmap]
    simp only [List.getD_eq_getElem?_getD] at habs
    simp [Render.NodeGen3.kbit,habs]
  simpa [Near.Render.NodeGen.bitOf,treeKids_bitmap] using hbit

theorem lookupBranchAbsent_rows (nid bm hv sym : Nat) (rest : List Nat)
    (hb : bm<2^16) (hv' : hv≤1) (hs : sym<16) (hz : bm/2^sym%2=0) :
    lookupRows (lookupBranchAbsent nid bm hv sym rest) := by
  have ht:=lookupDrain_rows rest
  have hn : 0<(lookupDrain rest).length := by simp [lookupDrain]
  have hp : StepOk (⟨2,sym,[nid,0,0,0,0,0],0,bm,hv,0⟩ : WStep3) false := by
    constructor <;> simp [hb,hv',hs,hz]
  have hh:=lookupRows_prefix [⟨2,sym,[nid,0,0,0,0,0],0,bm,hv,0⟩] (lookupDrain rest)
    (by intro s hm;simp only [List.mem_singleton] at hm;subst s;exact hp) ht hn
  exact hh

theorem native_branch_absent_rows (nid : Nat) (value : Option Slot) (kids : Kids)
    (sym : Nat) (rest : List Nat) (hw : Kids.wf kids 16=true) (hs : sym<16)
    (ha : nativeChildAt kids sym=none) :
    lookupRows (lookupBranchAbsent nid (kidsBitmap kids 0)
      (if value.isSome then 1 else 0) sym rest) :=
  lookupBranchAbsent_rows nid _ _ sym rest (kidsBitmap_lt kids 16 hw)
    (by split <;> decide) hs (native_absent_bitmap kids sym ha)

theorem native_branch_value_rows (nid vid : Nat) (value : Option Slot) (kids : Kids)
    (mem : Nat) (steps : List WStep3) (hw : Kids.wf kids 16=true)
    (h : nativeLookupSteps nid vid (.branch value kids mem) []=some steps) : lookupRows steps := by
  cases value with
  | none=>
    simp only [nativeLookupSteps,Option.some.injEq] at h
    rw [←h]
    have hb:=kidsBitmap_lt kids 16 hw
    constructor <;> simp [hb]
  | some v=>cases v with
    | ref l b=>cases h
    | val b=>
      simp only [nativeLookupSteps,Option.some.injEq] at h
      rw [←h]
      constructor <;> simp [lookupEdge]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
