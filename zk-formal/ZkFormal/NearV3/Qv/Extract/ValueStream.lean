import ZkFormal.NearV3.Qv.Extract.ValueByteKeys

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private theorem filter_unique_stream {α β γ : Type} [DecidableEq γ]
    (id : α → γ) (key : β → γ) (f : α → List β) (l : List α)
    (hu : (l.map id).Nodup) (hf : ∀ e∈l, ∀ m∈f e, key m=id e)
    (e : α) (he : e∈l) :
    (l.flatMap f).filter (fun m => decide (key m=id e))=f e := by
  induction l with
  | nil => simp at he
  | cons a rest ih =>
    simp only [List.map_cons,List.nodup_cons] at hu
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · rw [List.flatMap_cons,List.filter_append]
      have ha : (f e).filter (fun m => decide (key m=id e))=f e := by
        apply List.filter_eq_self.mpr
        intro m hm
        simp [hf e (by simp) m hm]
      have hr : (rest.flatMap f).filter (fun m => decide (key m=id e))=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro m hm
        obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hm
        have hk := hf b (by simp [hb]) m hm
        have hn : id b≠id e := fun h => hu.1 (List.mem_map.mpr ⟨b,hb,h⟩)
        simp [hk,hn]
      rw [ha,hr,List.append_nil]
    · rw [List.flatMap_cons,List.filter_append]
      have ha : (f a).filter (fun m => decide (key m=id e))=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro m hm
        have hk := hf a (by simp) m hm
        have hn : id a≠id e := fun h => hu.1 (List.mem_map.mpr ⟨e,he,h.symm⟩)
        simp [hk,hn]
      rw [ha,List.nil_append]
      exact ih hu.2 (fun b hb => hf b (by simp [hb])) he

def valueRecordStream (e : ValE) : List (List Fp) :=
  if e.vz then [] else (List.range e.bytes.length).map
    (fun i => Msg.toFp [e.vid,i,e.bytes.getD i 0])

/-- Filtering the complete canonical demand by an existing value ID picks
exactly that record's byte stream, with no contribution from other records. -/
theorem value_stream_filter {es : List ValE} (hv : ValWf es) (e : ValE) (he : e∈es) :
    ((valRecvs es B_VBYTES).map Msg.toFp).filter
      (fun m => decide (m.getD 0 0=Fp.ofNat e.vid))=valueRecordStream e := by
  have hmap : (valRecvs es B_VBYTES).map Msg.toFp=es.flatMap valueRecordStream := by
    simp only [valRecvs,ite_true,List.map_flatMap]
    congr 1
    funext a
    cases hz : a.vz <;> simp [hz,valueRecordStream,List.map_map,Function.comp_def]
  rw [hmap]
  apply filter_unique_stream (fun a => Fp.ofNat a.vid) (fun m => m.getD 0 0)
    valueRecordStream es (value_ids_unique hv) _ e he
  intro a ha m hm
  cases hz : a.vz
  · simp only [valueRecordStream,hz,Bool.false_eq_true,ite_false] at hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    rfl
  · simp [valueRecordStream,hz] at hm

end ZkFormal.NearV3.Qv.Extract
