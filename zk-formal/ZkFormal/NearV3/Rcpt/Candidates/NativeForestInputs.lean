import ZkFormal.NearV3.Rcpt.Candidates.NativeForestPayloads

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

structure ReplayTree where
  pre : PTrie
  post : PTrie
  writes : List (List Nat×Bytes)

def ReplayTree.Valid (r : ReplayTree) : Prop := SizedAccountRun r.pre r.writes r.post

def forestPostValue : List ReplayTree→Nat→Option Bytes
  | [],_=>none
  | r::rs,i=>if i<(valsOf r.pre).length then (oldTreeInputs r.pre r.post r.writes).value i
      else forestPostValue rs (i-(valsOf r.pre).length)

/-- One concrete global input map, using original occurrence offsets and
activating only real writes in each transition. -/
def forestOldInputs (rs : List ReplayTree) : Inputs where
  child := fun n=>(((rs.map ReplayTree.post).flatMap occs).map nodeEnc).getD n []
  value := forestPostValue rs

theorem forestOldInputs_children (rs : List ReplayTree) :
    ChildPayloads (forestOldInputs rs) 0 ((rs.map ReplayTree.post).flatMap occs) := by
  intro i t hi
  simp [forestOldInputs,List.getD_eq_getElem?_getD,List.getElem?_map,hi]

/-- Compact value arrays are read at the same global ordinal on both sides;
transition boundaries follow original prestate value counts. -/
theorem forestOldInputs_values (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid) :
    ValuePayloads (forestOldInputs rs) 0 (forestBytes (rs.map ReplayTree.pre))
      (forestBytes (rs.map ReplayTree.post)) := by
  induction rs with
  | nil=>intro i a b ha hb;simp [forestBytes] at ha
  | cons r rs ih=>
    have hr:=hv r (by simp)
    have ht:=ih (fun r hm=>hv r (by simp [hm]))
    have hl : (valsOf r.pre).length=(valsOf r.post).length :=
      write_vals_count hr.forget.skeleton
    intro i a b ha hb
    simp only [List.map_cons,forestBytes,List.flatMap_cons] at ha hb
    by_cases hi:i<(valsOf r.pre).length
    · have hi' : i<(valsOf r.post).length := by omega
      simp only [List.getElem?_append,hi,hi',↓reduceIte] at ha hb
      have hp:=oldTreeInputs_payload hr ha hb
      simpa only [ValuePayload,forestOldInputs,forestPostValue,hi,↓reduceIte,Nat.zero_add] using hp
    · have hi' : ¬i<(valsOf r.post).length := by omega
      simp only [List.getElem?_append,hi,hi',↓reduceIte] at ha hb
      rw [←hl] at hb
      have hp:=ht (i-(valsOf r.pre).length) a b ha hb
      simpa only [ValuePayload,forestOldInputs,forestPostValue,hi,↓reduceIte,Nat.zero_add] using hp

/-- Complete global old-record serialization from the concrete replay arrays;
all child/value payload hypotheses are discharged. -/
theorem forestOldInputs_all_bytes (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (tau : Nat) :
    (records (forestOldInputs rs) (forestNodes tau 0 0 (rs.map ReplayTree.pre))).map (fun s=>s.v.ser true)=
      ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  have hh:=forest_payload_post (forestOldInputs rs) tau 0 0 (rs.map (fun r=>(r.pre,r.post)))
    (by intro p hp;obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp;exact (hv r hr).forget.skeleton)
    (by intro p hp;obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp;exact SizedAccountRun.wf (hv r hr) (hw r hr))
  simp only [List.map_map,Function.comp_def] at hh
  exact hh (forestOldInputs_children rs) (forestOldInputs_values rs hv)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
