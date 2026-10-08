import ZkFormal.NearV3.Qv.Extract.RepairedKeyLookup
import ZkFormal.NearV3.Link.Compose3

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- A trie walk whose actual requests belong to one native queue key has
exactly that native key, including its length. The ownership premise must come
from global KEYNIB balance plus walk-identifier separation. -/
theorem native_walk_key {ws : List WalkR} (hW : WalkWf3 ws) {w : WalkR} (hw : w∈ws)
    (id : Fp) (bs : NearSpec.Bytes) (hb : 2*bs.length<P)
    (hm : ∀ i, 1≤i → i<w.steps.length →
      [(w.w:Fp),((i-1:Nat):Fp),((w.step i).sym: Fp),
        if i+1=w.steps.length then 1 else 0]∈repairedKeyTraffic id bs) :
    w.steps.length=2*bs.length+2 ∧ w.key3=NearSpec.nibbles bs := by
  have hlen := hW.len w hw
  have htotal := Link3.wrows_lt hW
  have hsize : w.steps.length≤(ws.flatMap (·.steps)).length := by
    rw [List.length_flatMap]
    exact Link.le_sum_of_mem (fun w : WalkR => w.steps.length) hw
  have hlast := repaired_key_lookup id bs hb
    (j:=w.steps.length-1-1) (by omega)
    (hm (w.steps.length-1) (by omega) (by omega))
  have he : w.steps.length-1+1=w.steps.length := by omega
  simp only [he,ite_true] at hlast
  rcases hlast.2 with hf|hf
  · have hz : (1:Fp)≠0 := by decide
    exact False.elim (hz hf.2.2)
  · have hlength : w.steps.length=2*bs.length+2 := by omega
    refine ⟨hlength,?_⟩
    apply List.ext_getElem
    · simp only [WalkR.key3,List.length_map,List.length_range,native_nibbles_length]
      omega
    · intro j hj hj'
      have hjn : j<2*bs.length := by simpa only [native_nibbles_length] using hj'
      have hmj := hm (j+1) (by omega) (by omega)
      have hnj : ¬j+1+1=w.steps.length := by omega
      simp only [hnj,ite_false,Nat.add_sub_cancel] at hmj
      have hh := (repaired_key_lookup id bs hb (j:=j) (by omega) hmj).2
      rcases hh with hh|hh
      · have hsP : (w.step (j+1)).sym<P :=
          ((hW.canon w hw).2.2 _ (Walk3.row_mem (by omega))).1
        have hnP : (NearSpec.nibbles bs).getD j 0<P := by
          have := native_nibble_bound bs j
          have : 16<P := by decide
          omega
        have hsym := ofNat_inj hsP hnP hh.2.1
        simp only [WalkR.key3,List.getElem_map,List.getElem_range]
        rw [hsym]
        exact List.getElem_eq_getD (h:=hj') 0 |>.symm
      · omega

end ZkFormal.NearV3.Qv.Extract
