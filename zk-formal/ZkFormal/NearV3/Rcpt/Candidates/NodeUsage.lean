import ZkFormal.NearV3.Rcpt.Candidates.NativeForestMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

structure UseRequests where
  edges : List Msg
  bmaps : List Msg
  windows : List Msg

def windowKey (n p : Nat) (s : NodeS3) : Msg :=
  [msgId K_NPOST n,p,(s.v.ser true).getD p 0,(s.v.ser false).length,s.depth,s.ucid.getD p 0]

/-- Set terminal provider counters from the exact request multiset on each bus. -/
def assignUses (q : UseRequests) (n : Nat) (s : NodeS3) : NodeS3 :=
  {s with
    uses := (edgesOf3 n s).map (fun e=>q.edges.count e)
    ubm := match s.v.bmap with | none=>0 | some (bm,hv)=>q.bmaps.count [n,bm,hv]
    mU := (List.range (s.v.ser false).length).map (fun p=>q.windows.count (windowKey n p s))}

theorem assignUses_arrays (q : UseRequests) (n : Nat) (s : NodeS3) :
    (assignUses q n s).uses.length=(edgesOf3 n (assignUses q n s)).length ∧
    (assignUses q n s).mU.length=(s.v.ser false).length := by
  have he : edgesOf3 n (assignUses q n s)=edgesOf3 n s := rfl
  rw [he]
  simp [assignUses]

theorem assignUses_small (q : UseRequests) (n : Nat) (s : NodeS3)
    (he : q.edges.length<P) (hb : q.bmaps.length<P) (hw : q.windows.length<P) :
    (∀u∈(assignUses q n s).uses,u<P) ∧ (assignUses q n s).ubm<P ∧
    ∀u∈(assignUses q n s).mU,u<P := by
  refine ⟨?_,?_,?_⟩
  · intro u hu
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp hu
    exact Nat.lt_of_le_of_lt (List.count_le_length) he
  · change (match s.v.bmap with | none=>0 | some (bm,hv)=>q.bmaps.count [n,bm,hv])<P
    split
    · decide
    · exact Nat.lt_of_le_of_lt (List.count_le_length) hb
  · intro u hu
    obtain ⟨p,_,rfl⟩:=List.mem_map.mp hu
    exact Nat.lt_of_le_of_lt (List.count_le_length) hw

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
