import ZkFormal.NearV3.Rcpt.Candidates.NativeShaAmortization

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 ZkFormal.Near

theorem kid_post_length (k : NKid) (h : k.wf) :
    (k.bytes true).length=(k.bytes false).length := by
  cases k <;> simp_all [NKid.wf,NKid.bytes]

theorem slot_post_length (s : NSlot3) (h : s.wf) :
    (s.bytes true).length=(s.bytes false).length := by
  cases s <;> simp_all [NSlot3.wf,NSlot3.bytes]

private theorem kids_post_length (ks : List NKid) (h : ∀k∈ks,k.wf) :
    (ks.flatMap (NKid.bytes true)).length=(ks.flatMap (NKid.bytes false)).length := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.flatMap_cons,List.length_append]
    rw [kid_post_length k (h k (by simp)),ih (fun k hk => h k (by simp [hk]))]

/-- Updated digest windows cannot change a well-formed V3 node's encoded length.
This holds for arbitrary final views, not only the equal-pre/post seed. -/
theorem node_post_length (v : NodeV3) (h : v.wf) :
    (v.ser true).length=(v.ser false).length := by
  cases v with
  | leaf k s m =>
    simp only [NodeV3.wf] at h
    simp only [NodeV3.ser,List.length_append,slot_post_length s h.2.1]
  | ext k child m =>
    simp only [NodeV3.wf] at h
    simp only [NodeV3.ser,List.length_append,kid_post_length child h.2.2.1]
  | branch v ks m =>
    simp only [NodeV3.wf] at h
    have hk := kids_post_length ks h.2.2.1
    cases v with
    | none => simp only [NodeV3.ser,List.length_append,hk]
    | some s =>
      have hs := slot_post_length s (h.2.1 s rfl)
      simp only [NodeV3.ser,List.length_append,hk,hs]

def nodePairShaRows (ns : List NodeS3) : Nat :=
  (ns.map (fun s => ZkFormal.Near.Render.rowsOf (s.v.ser false).length+
    ZkFormal.Near.Render.rowsOf (s.v.ser true).length)).sum

theorem node_pair_rows (ns : List NodeS3) (h : NodeWf3 ns) :
    nodePairShaRows ns=2*hashRows (ns.map (fun s => (s.v.ser false).length)) := by
  have he : ns.map (fun s => ZkFormal.Near.Render.rowsOf (s.v.ser false).length+
      ZkFormal.Near.Render.rowsOf (s.v.ser true).length)=
      ns.map (fun s => 2*ZkFormal.Near.Render.rowsOf (s.v.ser false).length) := by
    apply List.map_congr_left
    intro s hs
    rw [node_post_length s.v (h.wf s hs)]
    omega
  unfold nodePairShaRows
  rw [he]
  simp only [hashRows,List.map_map,Function.comp_def]
  clear h he
  induction ns with
  | nil => simp
  | cons s ns ih =>
    simp only [List.map_cons,List.sum_cons]
    omega

end ZkFormal.NearV3.Rcpt.Candidates
