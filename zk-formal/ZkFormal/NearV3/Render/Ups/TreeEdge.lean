import ZkFormal.NearV3.Render.Ups.TreeKidsTrace
import ZkFormal.NearV3.Render.Ups.TreeValueInput
import ZkFormal.NearV3.Render.Ups.RdbInput
import ZkFormal.NearV3.Render.Ups.RbiInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

def edgeSlot (sd : Nat) : Nat := if sd=1 then 15 else 0

def edgeRest (sd : Nat) (kids : List NKid) : List NKid :=
  if sd=1 then kids.take 15 else kids.drop 1

theorem edge_decompose (sd : Nat) (kids : List NKid) (hl : kids.length=16) :
    edgeKids sd (kids.getD (edgeSlot sd) .none) (edgeRest sd kids)=kids := by
  by_cases h : sd=1
  · simp only [edgeKids,edgeSlot,edgeRest,h,ite_true]
    have hn : 15<kids.length := by omega
    have ht := List.take_succ_eq_append_getElem hn
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
    rw [←ht]
    simpa only [hl] using (show kids.take kids.length=kids from List.take_length)
  · cases kids with
    | nil => simp at hl
    | cons k ks => simp [edgeKids,edgeSlot,edgeRest,h]

theorem edgeRest_length (sd : Nat) (kids : List NKid) (hl : kids.length=16) :
    (edgeRest sd kids).length=15 := by
  by_cases h : sd=1 <;> simp [edgeRest,h,hl]

theorem edge_set (sd : Nat) (kids : List NKid) (hl : kids.length=16) (new : NKid) :
    kids.set (edgeSlot sd) new=edgeKids sd new (edgeRest sd kids) := by
  have he := edge_decompose sd kids hl
  have hr := edgeRest_length sd kids hl
  conv => lhs; rw [←he]
  by_cases h : sd=1
  · subst sd
    simp [edgeKids,edgeSlot,List.set_append,hr]
  · simp [edgeKids,edgeSlot,h]

@[simp] theorem edgeRest_snapshot (sd : Nat) (cs : Kids) :
    (edgeRest sd (treeKids cs)).map snapshotKid=edgeRest sd (treeKids cs) := by
  by_cases h : sd=1 <;> simp [edgeRest,h]

@[simp] theorem treeOption_snapshot (sv : Option Slot) :
    (sv.map treeSlot).map snapshotValue=sv.map treeSlot := by cases sv <;> simp

theorem traceKids_output_wf {source : PTrie} {wholeKey : List Nat} {cs : Kids} {n : Nat}
    {key : List Nat} {v : Bytes} {run : KidsRun}
    (hr : traceKids source wholeKey cs n key v=some run) (hw : Kids.wf cs 16=true) :
    (treeKids run.output).length=16 ∧ ∀ k∈treeKids run.output,k.wf := by
  have hf := traceKids_effect source wholeKey cs n key v run hr
  have hs := treeKids_wf cs 16 hw
  rw [hf.2.1]
  refine ⟨by simpa using hs.1,?_⟩
  intro k hk
  rcases List.mem_or_eq_of_mem_set hk with hk|rfl
  · exact hs.2 k hk
  · simp [treeKid,NKid.wf,hashOf_eq_enc run.inner.output hf.2.2.2]

end ZkFormal.NearV3.Render.UpsGen
