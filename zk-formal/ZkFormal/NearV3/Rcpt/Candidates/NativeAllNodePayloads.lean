import ZkFormal.NearV3.Rcpt.Candidates.NativePayloadSegments

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
/-- All original node records serialize their matching replayed post subtrees,
using the same global child/value input arrays and allocation offsets. -/
theorem nodes_payload_post : ∀(u : Inputs)(tau d n v : Nat){a b : PTrie},WriteTreePair a b→
    b.wf=true→ChildPayloads u n (occs b)→ValuePayloads u v (valsOf a) (valsOf b)→
    (records u (seedNodesT tau d n v a)).map (fun s=>s.v.ser true)=
      (occs b).map (fun t=>(nodeEnc t).map UInt8.toNat)
  | u,tau,d,n,v,_,_,.hash hh,hw,hc,hv=>rfl
  | u,tau,d,n,v,_,_,.leaf k m hs,hw,hc,hv=>by
      simp only [seedNodesT,records,List.map_cons,List.map_nil,record,seedNodeView,occs]
      rw [node_payload_post u n v (.leaf k m hs) hw rfl hc hv]
  | u,tau,d,n,v,_,_,.ext k m hp,hw,hc,hv=>by
      have hroot:=node_payload_post u n v (.ext k m hp) hw rfl hc hv
      have hchild : ChildPayloads u (n+1) (occs _) := hc.tail
      have hvchild:=hv
      simp only [valsOf_ext] at hvchild
      have hwchild := (wf_ext hw).2
      have hrest:=nodes_payload_post u tau (d+1) (n+1) v hp hwchild hchild hvchild
      simp only [seedNodesT,records,List.map_cons,record,seedNodeView,occs,hroot]
      simpa only [records] using congrArg (List.cons _) hrest
  | u,tau,d,n,v,_,_,.branch m hp hs,hw,hc,hv=>by
      have hroot:=node_payload_post u n v (.branch m hp hs) hw rfl hc hv
      have hchild : ChildPayloads u (n+1) (kOccs _) := hc.tail
      have hvchild : ValuePayloads u (v+(optSlotVal _).length) (kvals _) (kvals _) :=
        ValuePayloads.right (by simpa only [valsOf_branch] using hv) (write_opt_count hp)
      have hwchild:=hw
      simp only [PTrie.wf,Bool.and_eq_true] at hwchild
      have hrest:=kids_payload_records u tau (d+1) (n+1) _ hs 16 hwchild.1.2 hchild hvchild
      simp only [seedNodesT,records,List.map_cons,record,seedNodeView,occs,hroot]
      simpa only [records] using congrArg (List.cons _) hrest
theorem kids_payload_records : ∀(u : Inputs)(tau d n v : Nat){a b : Kids},WriteKidsPair a b→
    ∀width,Kids.wf b width=true→ChildPayloads u n (kOccs b)→ValuePayloads u v (kvals a) (kvals b)→
    (records u (seedKidsT tau d n v a)).map (fun s=>s.v.ser true)=
      (kOccs b).map (fun t=>(nodeEnc t).map UInt8.toNat)
  | u,tau,d,n,v,_,_,.nil,width,hw,hc,hv=>rfl
  | u,tau,d,n,v,_,_,.none hp,width,hw,hc,hv=>by
      simp only [Kids.wf,Bool.and_eq_true] at hw
      simpa only [seedKidsT,kOccs] using kids_payload_records u tau d n v hp (width-1) hw.2 hc hv
  | u,tau,d,n,v,_,_,.some hp hs,width,hw,hc,hv=>by
      simp only [Kids.wf,Bool.and_eq_true] at hw
      have hcc : ChildPayloads u n (occs _) := ChildPayloads.left hc
      have hcr:=ChildPayloads.right hc
      have hlen : (occs _).length=tsize _ := (paired_occurrences hp).length.symm
      rw [hlen] at hcr
      have hvc : ValuePayloads u v (valsOf _) (valsOf _) :=
        ValuePayloads.left (by simpa only [kvals_some] using hv)
      have hvr : ValuePayloads u (v+(valsOf _).length) (kvals _) (kvals _) :=
        ValuePayloads.right (by simpa only [kvals_some] using hv) (write_vals_count hp)
      have hh:=nodes_payload_post u tau d n v hp hw.1.2 hcc hvc
      have hr:=kids_payload_records u tau d (n+tsize _) _ hs (width-1) hw.2 hcr hvr
      simp only [seedKidsT,records,List.map_append,kOccs]
      simpa only [records] using (congrArg (fun x=>x++_) hh).trans (congrArg (List.append _) hr)
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
