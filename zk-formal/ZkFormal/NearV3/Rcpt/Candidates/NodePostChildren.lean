import ZkFormal.NearV3.Rcpt.Candidates.NodePostNative

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near NearSpec Render.UpsGen

theorem native_child_post (u : Inputs) (nid : Nat) (pre post : PTrie)
    (hp : isNode pre=true) (hq : isNode post=true) (hu : u.child nid=nodeEnc post) :
    (kid u (viewKid nid pre)).bytes true=post.hashOf.map UInt8.toNat := by
  simp only [viewKid,hp,ite_true,kid,NKid.bytes,digest,hu]
  rw [hashOf_eq_enc post hq]

theorem native_ext_post (u : Inputs) (nid vid : Nat) (key : List Nat) (mem : Nat)
    (pre post : PTrie) (hp : isNode pre=true) (hq : isNode post=true)
    (hu : u.child (nid+1)=nodeEnc post) :
    (node u (viewNode nid vid (.ext key pre mem))).ser true=
      (nodeEnc (.ext key post mem)).map UInt8.toNat := by
  simp only [viewNode,node,NodeV3.ser,native_child_post u (nid+1) pre post hp hq hu]
  simp [nodeEnc,u32Bytes,hpN,List.map_append]

theorem set_revealed {pre post : PTrie} {key : List Nat} {b : Bytes}
    (h : pre.set key b=some post) : isNode pre=true ∧ isNode post=true := by
  cases pre with
  | hash h => simp [PTrie.set] at h
  | leaf k s m =>
    simp only [PTrie.set] at h
    split at h
    · cases hs : s.get <;> simp [hs] at h
      subst post
      exact ⟨rfl,rfl⟩
    · cases h
  | ext k c m =>
    simp only [PTrie.set] at h
    split at h
    · cases hs : c.set (key.drop k.length) b <;> simp [hs] at h
      subst post
      exact ⟨rfl,rfl⟩
    · cases h
  | branch v cs m =>
    cases key with
    | nil =>
      simp only [PTrie.set] at h
      split at h <;> simp at h
      subst post
      exact ⟨rfl,rfl⟩
    | cons n rest =>
      simp only [PTrie.set] at h
      cases hs : Kids.set cs n rest b <;> simp [hs] at h
      subst post
      exact ⟨rfl,rfl⟩

/-- Successful native extension writes supply the actual replacement child
preimage. The constructor override is executable and imposes no hash premise. -/
theorem native_ext_set_post (u : Inputs) (nid vid : Nat) (key query : List Nat) (mem : Nat)
    (pre : PTrie) (b : Bytes) (out : PTrie)
    (h : (PTrie.ext key pre mem).set query b=some out) :
    ∃post, pre.set (query.drop key.length) b=some post ∧
      let u' := {u with child:=fun i => if i=nid+1 then nodeEnc post else u.child i}
      (node u' (viewNode nid vid (.ext key pre mem))).ser true=(nodeEnc out).map UInt8.toNat := by
  simp only [PTrie.set] at h
  split at h
  · cases hs : pre.set (query.drop key.length) b with
    | none => simp [hs] at h
    | some post =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst out
      refine ⟨post,rfl,?_⟩
      have hh := set_revealed hs
      exact native_ext_post _ nid vid key mem pre post hh.1 hh.2 (by simp)
  · cases h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
