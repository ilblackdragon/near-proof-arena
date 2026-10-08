import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeWf
import ZkFormal.Near.Link.Streams

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Near.Link ZkFormal.Algebra

def kidIds : NKid→List Nat
  | .none => []
  | .hash _ => List.replicate 32 0
  | .node c _ _ _ _ => List.replicate 32 c

def windowIds : NodeV3→List Nat
  | .leaf k s m => List.replicate ((NodeV3.leaf k s m).ser false).length 0
  | .ext k c _ => List.replicate (5+(hpN k false).length) 0++kidIds c++List.replicate 8 0
  | .branch v cs _ => List.replicate ((if v.isSome then 37 else 1)+2) 0++
      cs.flatMap kidIds++List.replicate 8 0

theorem kidIds_at : ∀(cs : List NKid)(j c l r : Nat)(pre post : List Nat),
    cs.getD j .none=.node c l r pre post →
    let p := 32*((cs.take j).filter (·.present)).length
    p<(cs.flatMap kidIds).length ∧ (cs.flatMap kidIds).getD p 0=c
  | [],_,_,_,_,_,_,h => by simp at h
  | k::cs,0,c,l,r,pre,post,h => by
    simp only [List.getD_cons_zero] at h
    subst k
    simp [kidIds]
  | k::cs,j+1,c,l,r,pre,post,h => by
    have ht := kidIds_at cs j c l r pre post (by simpa using h)
    dsimp only at ht ⊢
    cases k with
    | none => simpa [List.take_succ_cons,NKid.present,kidIds] using ht
    | hash hh =>
      have he := getD_append_right' (List.replicate 32 0) (cs.flatMap kidIds)
        (32*((cs.take j).filter (·.present)).length)
      simp only [List.length_replicate] at he
      constructor
      · simp only [List.take_succ_cons,List.filter_cons,NKid.present,ite_true,List.length_cons,
          List.flatMap_cons,kidIds,List.length_append,List.length_replicate] at *
        omega
      · simpa [kidIds,List.take_succ_cons,NKid.present,Nat.mul_add,Nat.add_comm] using he.trans ht.2
    | node cc ll rr pp po =>
      have he := getD_append_right' (List.replicate 32 cc) (cs.flatMap kidIds)
        (32*((cs.take j).filter (·.present)).length)
      simp only [List.length_replicate] at he
      constructor
      · simp only [List.take_succ_cons,List.filter_cons,NKid.present,ite_true,List.length_cons,
          List.flatMap_cons,kidIds,List.length_append,List.length_replicate] at *
        omega
      · simpa [kidIds,List.take_succ_cons,NKid.present,Nat.mul_add,Nat.add_comm] using he.trans ht.2

theorem windowIds_kidCid (v : NodeV3) : v.kidCidOk (windowIds v) := by
  cases v with
  | leaf k s m => trivial
  | ext k kid m =>
    intro c l r pre post h
    subst kid
    simp only [windowIds,kidIds]
    have he := getD_append_right' (List.replicate (5+(hpN k false).length) 0)
      (List.replicate 32 c++List.replicate 8 0) 0
    simpa using he
  | branch v cs m =>
    intro j c l r pre post h
    obtain ⟨hb,he⟩ := kidIds_at cs j c l r pre post h
    have hx := getD_append_right' (List.replicate ((if v.isSome then 37 else 1)+2) 0)
      (cs.flatMap kidIds++List.replicate 8 0) (32*((cs.take j).filter (·.present)).length)
    rw [getD_append_left' hb,he] at hx
    simpa [windowIds,List.append_assoc] using hx

theorem kidIds_length (k : NKid) (h : k.wf) : (kidIds k).length=(k.bytes false).length := by
  cases k <;> simp_all [kidIds,NKid.wf,NKid.bytes]

private theorem kidsIds_length (cs : List NKid) (h : ∀c∈cs,c.wf) :
    (cs.flatMap kidIds).length=(cs.flatMap (NKid.bytes false)).length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.length_append]
    rw [kidIds_length c (h c (by simp)),ih (fun c hc => h c (by simp [hc]))]

private theorem slot_pre_length (s : NSlot3) (h : s.wf) : (s.bytes false).length=36 := by
  cases s <;> simp_all [NSlot3.wf,NSlot3.bytes]

theorem windowIds_length (v : NodeV3) (h : v.wf) :
    (windowIds v).length=(v.ser false).length := by
  cases v with
  | leaf k s m => simp [windowIds]
  | ext k c m =>
    simp only [windowIds,NodeV3.ser,List.length_append,List.length_replicate,u32Bytes_length,
      List.length_cons,List.length_nil,kidIds_length c h.2.2.1,h.2.2.2]
  | branch v cs m =>
    have hh := kidsIds_length cs h.2.2.1
    cases v with
    | none => simp [windowIds,NodeV3.ser,hh,h.2.2.2]
    | some s =>
      have hs := slot_pre_length s (h.2.1 s rfl)
      simp only [windowIds,NodeV3.ser,Option.isSome_some,ite_true,List.length_append,
        List.length_replicate,List.length_cons,List.length_nil,hs,hh,h.2.2.2]

/-- Fill all initial local metadata arrays without altering the semantic view.
Use counts are initial zero values; global bus ownership later assigns them. -/
def initializeMetadata (nid : Nat) (s : NodeS3) : NodeS3 :=
  { s with
    uses := List.replicate (edgesOf3 nid s).length 0
    ucid := windowIds s.v
    mU := List.replicate (s.v.ser false).length 0 }

theorem initializeMetadata_arrays (nid : Nat) (s : NodeS3) (h : s.v.wf) :
    (initializeMetadata nid s).uses.length=(edgesOf3 nid (initializeMetadata nid s)).length ∧
    (initializeMetadata nid s).ucid.length=(s.v.ser false).length ∧
    (initializeMetadata nid s).mU.length=(s.v.ser false).length ∧
    (initializeMetadata nid s).v.kidCidOk (initializeMetadata nid s).ucid := by
  have he : edgesOf3 nid (initializeMetadata nid s)=edgesOf3 nid s := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (List.replicate (edgesOf3 nid s).length 0).length = _
    rw [he,List.length_replicate]
  · exact windowIds_length s.v h
  · exact List.length_replicate
  · exact windowIds_kidCid s.v

theorem kidIds_small (k : NKid) (h : ∀x∈k.raw,x<P) : ∀x∈kidIds k,x<P := by
  cases k <;> simp_all [kidIds,NKid.raw,P]

theorem windowIds_small (v : NodeV3) (h : ∀x∈v.raw,x<P) : ∀x∈windowIds v,x<P := by
  cases v with
  | leaf k s m => simp [windowIds,P]
  | ext k c m =>
    have hc : ∀x∈c.raw,x<P := by intro x hx; exact h x (by simp [NodeV3.raw,hx])
    intro x hx
    simp only [windowIds,List.mem_append,List.mem_replicate] at hx
    rcases hx with ((⟨_,rfl⟩|hx)|⟨_,rfl⟩)
    · decide
    · exact kidIds_small c hc x hx
    · decide
  | branch v cs m =>
    have hc : ∀c∈cs,∀x∈c.raw,x<P := by
      intro c hc x hx
      exact h x (by simp only [NodeV3.raw,List.mem_append,List.mem_flatMap]; exact Or.inl (Or.inr ⟨c,hc,hx⟩))
    intro x hx
    simp only [windowIds,List.mem_append,List.mem_replicate,List.mem_flatMap] at hx
    rcases hx with ((⟨_,rfl⟩|⟨c,hc',hx⟩)|⟨_,rfl⟩)
    · decide
    · exact kidIds_small c (hc c hc') x hx
    · decide

theorem initializeMetadata_small (nid : Nat) (s : NodeS3)
    (h : ∀x∈s.v.raw,x<P) :
    (∀x∈(initializeMetadata nid s).uses,x<P) ∧
    (∀x∈(initializeMetadata nid s).ucid,x<P) ∧
    (∀x∈(initializeMetadata nid s).mU,x<P) := by
  refine ⟨?_,windowIds_small s.v h,?_⟩ <;>
    simp [initializeMetadata,P]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
