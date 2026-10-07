import ZkFormal.NearV3.Assembly.WitnessSize
import ZkFormal.NearV3.Assembly.DecodedWitnessShape

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem storeCost_count (ws : List Bytes) : ws.length ≤ storeCost ws := by
  have h : ws.length ≤ (ws.map entryCost).sum := by
    induction ws with
    | nil => simp
    | cons a ws ih => simp only [List.length_cons,List.map_cons,List.sum_cons,entryCost]; omega
  unfold storeCost
  omega

theorem storeCost_value {v : Bytes} : ∀ {ws : List Bytes}, v ∈ ws → v.length ≤ storeCost ws
  | [], h => by simp at h
  | a::ws, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [storeCost,List.map_cons,List.sum_cons,entryCost]; omega
    · have ih := storeCost_value h
      simp only [storeCost,List.map_cons,List.sum_cons,entryCost] at *
      omega

theorem transitionWf_of_size {t : Transition}
    (hb : t.blockHash.length = 32) (hp : t.postStateRoot.length = 32)
    (hs : (V3.encodeTransition t).length < 4294967296) : V3.transitionWf t = true := by
  have hv : storeCost t.values < 4294967296 := by
    simp only [V3.encodeTransition,ReexecV3D0.encTr,List.length_append,encList_storeCost] at hs
    omega
  simp only [V3.transitionWf,V3.h32,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨⟨hb,Nat.lt_of_le_of_lt (storeCost_count _) hv⟩,?_⟩,hp⟩
  apply List.all_eq_true.mpr
  intro v hm
  exact decide_eq_true (Nat.lt_of_le_of_lt (storeCost_value hm) hv)

theorem encList_member_size {α : Type} (enc : α → Bytes) {x : α} {xs : List α}
    (hx : x ∈ xs) : (enc x).length ≤ (encList enc xs).length := by
  have h : (enc x).length ≤ (concatAll (xs.map enc)).length := by
    induction xs with
    | nil => simp at hx
    | cons a xs ih =>
      rcases List.mem_cons.mp hx with rfl | hm
      · simp only [List.map_cons,concatAll,List.length_append]; omega
      · have hh := ih hm
        simp only [List.map_cons,concatAll,List.length_append]
        omega
  simp only [encList,List.length_append]
  omega

theorem encodeSW_main_size (w : StateWitness) :
    (V3.encodeTransition w.main).length ≤ (V3.encodeSW w).length := by
  simp only [V3.encodeSW,List.length_append]
  omega

theorem encodeSW_implicit_size {w : StateWitness} {t : Transition} (ht : t ∈ w.implicit) :
    (V3.encodeTransition t).length ≤ (V3.encodeSW w).length := by
  have h := encList_member_size V3.encodeTransition ht
  simp only [V3.encodeSW,List.length_append]
  omega

theorem encodeSW_transition_shapes {w : StateWitness}
    (hs : (V3.encodeSW w).length ≤ 8388608)
    (hm : TransitionHashes w.main)
    (hi : ∀ t ∈ w.implicit, TransitionHashes t) :
    V3.transitionWf w.main = true ∧ w.implicit.all V3.transitionWf = true := by
  constructor
  · apply transitionWf_of_size hm.1 hm.2
    have hh := encodeSW_main_size w
    omega
  · apply List.all_eq_true.mpr
    intro t ht
    apply transitionWf_of_size (hi t ht).1 (hi t ht).2
    have hh := encodeSW_implicit_size ht
    omega

end ZkFormal.NearV3.Assembly
