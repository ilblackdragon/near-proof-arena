import ZkFormal.NearV3.Qv.Extract.KeyOwnership
import ZkFormal.NearV3.Rcpt.Link.ListByteIds

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- Queue identifiers occupy their declared namespace as canonical naturals. -/
theorem queue_walk_id_range {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) :
    ∃ n, W_QV≤n ∧ n<P ∧ wid.eval tr tt q.segs[i].1 pub=(n:Fp) := by
  obtain ⟨last,hlast,hf⟩ := WalkChain.last_main_exists hL q
  by_cases hil : i≤last
  · have hm := WalkChain.main_prefix hL q i last hi hlast hil
      (WalkChain.last_main_shape hL q last hlast hf).1
    obtain ⟨he,hb⟩ := main_walk_id hL q i hi hm
    exact ⟨_,by omega,hb,he⟩
  · obtain ⟨he,hb⟩ := implicit_walk_id hL q last i hlast hf hi (by omega)
    exact ⟨_,by omega,hb,he⟩

private theorem keyMsgs_id (w : Nat) (syms : List Nat) {m : Msg}
    (hm : m∈RcptE.keyMsgs w syms) : m.getD 0 0=w := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
  rfl

/-- Both account and access-key senders are below the queue namespace when
receipt count fits its allocated walk-ID range. -/
theorem receipt_key_id_range {pub : List Fp} {ls : RcptV3Vs}
    (hn : (flatR ls).length≤W_AK) {m : Msg} (hm : m∈rcptSends3 pub ls B_KEYNIB) :
    m.getD 0 0<W_QV := by
  simp only [rcptSends3,show B_KEYNIB≠B_BYTES by decide,show B_KEYNIB≠B_RCL by decide,
    ite_false,List.nil_append] at hm
  obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  obtain ⟨⟨r,off,x⟩,hpos,hm⟩ := List.mem_flatMap.mp hm
  have hget : ls.getD j default=ls[j] := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  simp only [located,hget,List.mem_map,List.mem_range] at hpos
  obtain ⟨k,hk,hpos⟩ := hpos
  cases hpos
  have hr := RcptLink.located_index_bound ls hj
  simp only [rSends,show B_KEYNIB≠B_BYTES by decide,ite_false,ite_true,List.mem_append] at hm
  rcases hm with hm|hm
  · rw [keyMsgs_id _ _ hm]
    unfold W_AK W_QV at *
    omega
  · split at hm
    · rw [keyMsgs_id _ _ hm]
      unfold W_AK W_QV at *
      omega
    · simp at hm

/-- Receipt sends cannot masquerade as any actual queue request. -/
theorem receipt_queue_ids_disjoint {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) (ls : RcptV3Vs) (hn : (flatR ls).length≤W_AK)
    {m : Msg} (hm : m∈rcptSends3 pub ls B_KEYNIB) :
    (Msg.toFp m).getD 0 0≠wid.eval tr tt q.segs[i].1 pub := by
  intro he
  obtain ⟨n,hn0,hnP,hid⟩ := queue_walk_id_range hL q i hi
  have hr := receipt_key_id_range hn hm
  have hrP : m.getD 0 0<P := by
    have : W_QV<P := by decide
    omega
  rw [hid] at he
  change (m.map Fp.ofNat).getD 0 (Fp.ofNat 0)=_ at he
  rw [Link3.getD_map'] at he
  have hh := ofNat_inj hrP hnP he
  omega

end ZkFormal.NearV3.Qv.Extract
