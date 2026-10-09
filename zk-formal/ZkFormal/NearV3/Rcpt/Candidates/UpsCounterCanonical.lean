import ZkFormal.NearV3.Rcpt.Candidates.UpsCounterSync

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra Render.UpsGen

theorem rankUpsList_member : ∀(Is : List Render.UpsInst)(p : List WStep3)(J : Render.UpsInst),
    J∈rankUpsList p Is → ∃q I,I∈Is ∧ J=rankUps q I ∧ q.length+4≤p.length+4*Is.length
  | [],_,_,h=>by simp [rankUpsList] at h
  | I::Is,p,J,h=>by
    simp only [rankUpsList,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨p,I,by simp,rfl,by simp;omega⟩
    · obtain ⟨q,I',hI,he,hb⟩:=rankUpsList_member Is (p++fourSteps I) J h
      refine ⟨q,I',by simp [hI],he,?_⟩
      simp only [List.length_append,fourSteps,List.length_ofFn,List.length_cons] at *
      omega

def physicalRankedUps (Is : List Render.UpsInst) : List Render.UpsInst :=
  (rankUpsList [] Is).map syncUps

theorem physical_counter_bound (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I)
    (J : Render.UpsInst) (hJ : J∈physicalRankedUps Is) (t : Nat) (ht : t<4) :
    (step J t).u<4*Is.length := by
  obtain ⟨K,hK,rfl⟩:=List.mem_map.mp hJ
  obtain ⟨p,I,hI,rfl,hb⟩:=rankUpsList_member Is [] K hK
  have hu:=physical_rank_counter_bound p I (ho I hI) t ht
  simp only [List.length_nil,Nat.zero_add] at hb
  omega

theorem physical_counter_canonical (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I)
    (hlen : Is.length≤32) (J : Render.UpsInst) (hJ : J∈physicalRankedUps Is)
    (t : Nat) (ht : t<4) : (step J t).u<P ∧ (step J t).u+1<P := by
  have hu:=physical_counter_bound Is ho J hJ t ht
  change (step J t).u<2013265921 ∧ (step J t).u+1<2013265921
  omega

theorem physical_counter_field (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I)
    (hlen : Is.length≤32) (J : Render.UpsInst) (hJ : J∈physicalRankedUps Is)
    (t : Nat) (ht : t<4) :
    (((wCell J t 105 : Int) : Fp)).toNat=(step J t).u := by
  have hu:=(physical_counter_canonical Is ho hlen J hJ t ht).1
  change (Fp.ofNat (step J t).u).toNat=(step J t).u
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hu]

theorem physicalRankedUps_instOk (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I) :
    ∀J∈physicalRankedUps Is,InstOk J := by
  intro J hJ;obtain ⟨I,hI,rfl⟩:=List.mem_map.mp hJ
  exact syncUps_instOk I (rankUpsList_instOk Is [] ho I hI)

theorem physicalRankedUps_parts (Is : List Render.UpsInst) (ho : ∀I∈Is,NativePartFamily I) :
    ∀J∈physicalRankedUps Is,NativePartFamily J := by
  intro J hJ;obtain ⟨I,hI,rfl⟩:=List.mem_map.mp hJ
  exact syncUps_parts I (rankUpsList_parts Is [] ho I hI)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
