import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestOrder
import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def postChildBindings (u : Inputs) (n : Nat) (ss : List NodeS3) : Prop :=
  ∀i s,ss[i]?=some s→s.v.ser true=(u.child (n+i)).map UInt8.toNat

/-- SHA's emitted digest records are exactly the indexed native occurrence
records when supplied the already-bound original/post serializations. -/
theorem node_jobs_digests (u : Inputs) : ∀(ss : List NodeS3)(ts : List PTrie)(n : Nat),
    ss.map (fun s=>s.v.ser false)=ts.map (fun t=>(nodeEnc t).map UInt8.toNat)→
    postChildBindings u n ss→(∀s∈ss,(s.v.ser true).length=(s.v.ser false).length)→
    (∀t∈ts,isNode t=true)→
    Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom n ss))=
      (indexedOwners n ts).flatMap (ownerDigests u)
  | [],[],_,_,_,_,_=>rfl
  | [],_::_,_,he,_,_,_=>by simp at he
  | _::_,[],_,he,_,_,_=>by simp at he
  | s::ss,t::ts,n,he,hp,hl,hn=>by
    have hh:=List.cons.inj he
    have hs:=hp 0 s rfl
    simp only [Nat.add_zero] at hs
    have hlen:=hl s (by simp)
    have hhash : t.hashOf=sha256 (nodeEnc t):=hashOf_eq_enc t (hn t (by simp))
    have hi:=node_jobs_digests u ss ts (n+1) hh.2
      (by intro i x hx;simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp (i+1) x hx)
      (fun x hx=>hl x (by simp [hx])) (fun x hx=>hn x (by simp [hx]))
    simp only [nativeNodeShaJobsFrom,jobsToSha,List.map_cons,Sha.Gen.expectedDigests,
      List.filter_cons,ite_true,List.map_cons] at hi ⊢
    rw [hi]
    simp only [indexedOwners,List.flatMap_cons,ownerDigests,List.cons_append,List.nil_append,
      hh.1,hs,List.length_map,hhash,digest,digMsg]
    simp only [List.map_map,UInt8.ofNat_toNat,Function.comp_def,List.map_id]
    simp only [hh.1,hs,List.length_map] at hlen
    rw [hlen]
    simp

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
