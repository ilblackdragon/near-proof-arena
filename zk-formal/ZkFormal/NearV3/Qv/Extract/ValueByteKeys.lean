import ZkFormal.NearV3.Qv.Extract.StreamOwnership
import ZkFormal.NearV3.Link.Compose3

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link

private def recordKeys (e : ValE) : List (Fp × Fp) :=
  if e.vz then [] else (List.range e.bytes.length).map (fun i => (Fp.ofNat e.vid,Fp.ofNat i))

private theorem flat_keys_nodup {α β γ : Type} (id : α → β) (keys : α → List (β × γ))
    (l : List α) (hi : (l.map id).Nodup)
    (hk : ∀ e∈l, (keys e).Nodup)
    (hf : ∀ e∈l, ∀ k∈keys e, k.1=id e) : (l.flatMap keys).Nodup := by
  induction l with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons,List.nodup_cons] at hi
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨hk e (by simp),ih hi.2 (fun a ha => hk a (by simp [ha]))
      (fun a ha => hf a (by simp [ha])),?_⟩
    intro x hx y hy he
    obtain ⟨a,ha,hya⟩ := List.mem_flatMap.mp hy
    have hxid := hf e (by simp) x hx
    have hyid := hf a (by simp [ha]) y hya
    have hid : id a=id e := by rw [←hyid,←he,hxid]
    exact hi.1 (List.mem_map.mpr ⟨a,ha,hid⟩)

theorem value_ids_unique {es : List ValE} (hv : ValWf es) :
    (es.map (fun e => Fp.ofNat e.vid)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij he
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at he
  have hc := hv.canon _ (List.getElem_mem hi)
  have hd := hv.canon _ (List.getElem_mem hj)
  have hn := Link.ofNat_inj hc.1 hd.1 he
  have hh := Link3.vid_inj hv (Link3.vlen_le hv) hi hj hn
  omega

/-- Canonical value IDs and bounded byte offsets make all demanded physical
(id,position) pairs unique, including across distinct value records. -/
theorem value_byte_keys_unique {es : List ValE} (hv : ValWf es) :
    (((valRecvs es B_VBYTES).map Msg.toFp).map
      (fun m => (m.getD 0 0,m.getD 1 0))).Nodup := by
  have hids := value_ids_unique hv
  have hk : ∀ e∈es, (recordKeys e).Nodup := by
    intro e he
    cases hz : e.vz
    · simp only [recordKeys,hz,Bool.false_eq_true,ite_false]
      apply nodup_map_of_inj_on _ List.nodup_range
      intro i hi j hj heq
      have hl := (hv.shape e he).2 hz
      have hc := (hv.canon e he).2.1
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp hj
      exact Link.ofNat_inj (by omega) (by omega) (congrArg Prod.snd heq)
    · simp [recordKeys,hz]
  have hf : ∀ e∈es, ∀ k∈recordKeys e, k.1=Fp.ofNat e.vid := by
    intro e he k hk
    cases hz : e.vz
    · simp only [recordKeys,hz,Bool.false_eq_true,ite_false] at hk
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
      rfl
    · simp [recordKeys,hz] at hk
  have hn := flat_keys_nodup (fun e => Fp.ofNat e.vid) recordKeys es hids hk hf
  have he : (((valRecvs es B_VBYTES).map Msg.toFp).map
      (fun m => (m.getD 0 0,m.getD 1 0)))=es.flatMap recordKeys := by
    simp only [valRecvs,ite_true,List.map_flatMap,List.map_map]
    congr 1
    funext e
    cases hz : e.vz <;> simp [hz,recordKeys,Msg.toFp,Function.comp_def]
  rw [he]
  exact hn

end ZkFormal.NearV3.Qv.Extract
