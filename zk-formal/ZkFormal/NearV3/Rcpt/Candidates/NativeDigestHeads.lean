import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestForest
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestInputs
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayHeadKeys

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem childPayload_root {u : Inputs} {n : Nat} {t : PTrie}
    (h : ChildPayloads u n (occs t)) (hn : isNode t=true) : u.child n=nodeEnc t := by
  have hi : (occs t)[0]?=some t:=by cases t <;> simp_all [occs,isNode]
  simpa only [Nat.add_zero] using h 0 t hi

theorem payload_root_digest {u : Inputs} {n : Nat} {t : PTrie}
    (h : ChildPayloads u n (occs t)) (hn : isNode t=true) :
    digest (u.child n)=t.hashOf.map UInt8.toNat := by
  rw [childPayload_root h hn,hashOf_eq_enc t hn]
  rfl

/-- Actual HEAD root digest records use the same concrete post-child payload
map as the original-node table, at the same global occurrence offsets. -/
theorem forest_head_digest_records (u : Inputs) : ∀(pairs : List (PTrie×PTrie))(tau n : Nat),
    (∀p∈pairs,WriteTreePair p.1 p.2)→(∀p∈pairs,isNode p.1=true)→
    ChildPayloads u n ((pairs.map Prod.snd).flatMap occs)→
    headRecvs (forestWalkHeads tau n pairs) B_DIGEST=
      (forestRootOwners n (pairs.map Prod.fst)).flatMap (ownerDigests u)
  | [],_,_,_,_,_=>rfl
  | (pre,post)::pairs,tau,n,hp,hn,hc=>by
    have hpair:=hp (pre,post) (by simp)
    have hpre:=hn (pre,post) (by simp)
    have hpost : isNode post=true := by rw [←write_isNode hpair];exact hpre
    have hcc : ChildPayloads u n (occs post):=ChildPayloads.left hc
    have hcr:=ChildPayloads.right hc
    have hlen : (occs post).length=tsize pre := (write_tsize hpair).symm
    rw [hlen] at hcr
    have hd:=payload_root_digest hcc hpost
    have ih:=forest_head_digest_records u pairs (tau+1) (n+tsize pre)
      (fun p hm=>hp p (by simp [hm])) (fun p hm=>hn p (by simp [hm])) hcr
    change headRecvs (forestWalkHeads tau n ((pre,post)::pairs)) B_DIGEST=_
    simp only [headRecvs,ite_true,forestWalkHeads,List.flatMap_cons,List.map_cons,forestRootOwners,
      rootOwner,hpre,ite_true,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      ownerDigests,hd]
    exact congrArg (List.append _) ih

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
