import ZkFormal.NearV3.Rcpt.Candidates.NativeOldNodeBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- Global provider binding across every transition, preserving both node and
value offsets while each old tree keeps its own receipt replay. -/
theorem forest_payload_post : ∀(u : Inputs)(tau n v : Nat)(pairs : List (PTrie×PTrie)),
    (∀p∈pairs,WriteTreePair p.1 p.2)→(∀p∈pairs,p.2.wf=true)→
    ChildPayloads u n ((pairs.map Prod.snd).flatMap occs)→
    ValuePayloads u v (forestBytes (pairs.map Prod.fst)) (forestBytes (pairs.map Prod.snd))→
    (records u (forestNodes tau n v (pairs.map Prod.fst))).map (fun s=>s.v.ser true)=
      ((pairs.map Prod.snd).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat)
  | u,tau,n,v,[],hp,hw,hc,hv=>rfl
  | u,tau,n,v,(pre,post)::pairs,hp,hw,hc,hv=>by
    have hpair:=hp (pre,post) (by simp)
    have hwell:=hw (pre,post) (by simp)
    have hcc : ChildPayloads u n (occs post) := ChildPayloads.left hc
    have hcr:=ChildPayloads.right hc
    have hlen : (occs post).length=tsize pre := (paired_occurrences hpair).length.symm
    rw [hlen] at hcr
    have hvc : ValuePayloads u v (valsOf pre) (valsOf post) :=
      ValuePayloads.left (by simpa only [forestBytes,List.map_cons,List.flatMap_cons] using hv)
    have hvr : ValuePayloads u (v+(valsOf pre).length)
        (forestBytes (pairs.map Prod.fst)) (forestBytes (pairs.map Prod.snd)) :=
      ValuePayloads.right (by simpa only [forestBytes,List.map_cons,List.flatMap_cons] using hv)
        (write_vals_count hpair)
    have hh:=nodes_payload_post u tau 0 n v hpair hwell hcc hvc
    have hr:=forest_payload_post u (tau+1) (n+tsize pre) (v+(valsOf pre).length) pairs
      (fun p hm=>hp p (by simp [hm])) (fun p hm=>hw p (by simp [hm])) hcr hvr
    simp only [List.map_cons,forestNodes,records,List.map_append,List.flatMap_cons]
    simpa only [records] using (congrArg (fun x=>x++_) hh).trans (congrArg (List.append _) hr)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
