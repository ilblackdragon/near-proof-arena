import ZkFormal.NearV3.Render.Ups.TreeViews

/-! Initial NodeS3 views for the existing occurrence allocator. IDs, serialized node
payloads, depths and empty-extension targets are filled here. Traffic/use-count fields
are deliberately seeds; no NodeWf3 or AIR completeness claim is made about them. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

def seedNodeView (tau depth nid vid : Nat) (t : PTrie) : NodeS3 := {
  v := viewNode nid vid t, tau := tau, depth := depth, res := viewTarget nid t,
  uses := [], ubm := 0, dup := false, hd := false, repE := 0, ucid := [], mU := [] }

mutual
def seedNodesT (tau : Nat) : Nat → Nat → Nat → PTrie → List NodeS3
  | _,_,_,.hash _ => []
  | d,n,v,.leaf k s m => [seedNodeView tau d n v (.leaf k s m)]
  | d,n,v,.ext k c m => seedNodeView tau d n v (.ext k c m)::seedNodesT tau (d+1) (n+1) v c
  | d,n,v,.branch sv cs m => seedNodeView tau d n v (.branch sv cs m)::
      seedKidsT tau (d+1) (n+1) (v+(optSlotVal sv).length) cs
def seedKidsT (tau : Nat) : Nat → Nat → Nat → Kids → List NodeS3
  | _,_,_,.nil => []
  | d,n,v,.none rest => seedKidsT tau d n v rest
  | d,n,v,.some c rest => seedNodesT tau d n v c ++
      seedKidsT tau d (n+tsize c) (v+(valsOf c).length) rest
end

mutual
/-- Extracting the seeded views returns exactly the verified occurrence records. -/
theorem seedNodesT_records (tau : Nat) : ∀ d n v t, t.wf=true →
    Link3.recsOf id (seedNodesT tau d n v t)=recsT tau n v t
  | _,_,_,.hash _,_ => rfl
  | d,n,v,.leaf k s m,hw => by
    simp [seedNodesT,recsT,Link3.recsOf,seedNodeView,viewNode_toRec n v _ hw]
  | d,n,v,.ext k c m,hw => by
    have hc : c.wf=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.1.2
    have ih := seedNodesT_records tau (d+1) (n+1) v c hc
    simpa [seedNodesT,recsT,Link3.recsOf,seedNodeView,viewNode_toRec n v _ hw] using
      congrArg (List.cons (NodeRec3.mk tau (recT n v (.ext k c m)))) ih
  | d,n,v,.branch sv cs m,hw => by
    have hc : Kids.wf cs 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.2
    have ih := seedKidsT_records tau (d+1) (n+1) (v+(optSlotVal sv).length) cs 16 hc
    simpa [seedNodesT,recsT,Link3.recsOf,seedNodeView,viewNode_toRec n v _ hw] using
      congrArg (List.cons (NodeRec3.mk tau (recT n v (.branch sv cs m)))) ih
theorem seedKidsT_records (tau : Nat) : ∀ d n v cs width, Kids.wf cs width=true →
    Link3.recsOf id (seedKidsT tau d n v cs)=krecsT tau n v cs
  | _,_,_,.nil,_,_ => rfl
  | d,n,v,.none rest,width,hw => by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    exact seedKidsT_records tau d n v rest (width-1) hw.2
  | d,n,v,.some c rest,width,hw => by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    have ihc := seedNodesT_records tau d n v c hw.1.2
    have ihr := seedKidsT_records tau d (n+tsize c) (v+(valsOf c).length) rest (width-1) hw.2
    simp only [Link3.recsOf] at ihc ihr
    simp only [seedKidsT,krecsT,Link3.recsOf,List.map_append]
    rw [ihc,ihr]
end

mutual
theorem seedNodesT_depths (tau : Nat) : ∀ d n v t,
    (seedNodesT tau d n v t).map NodeS3.depth=depsT d t
  | _,_,_,.hash _ => rfl
  | _,_,_,.leaf .. => rfl
  | d,n,v,.ext k c m => by simp [seedNodesT,depsT,seedNodeView,seedNodesT_depths tau (d+1) (n+1) v c]
  | d,n,v,.branch sv cs m => by
    simp [seedNodesT,depsT,seedNodeView,seedKidsT_depths tau (d+1) (n+1) (v+(optSlotVal sv).length) cs]
theorem seedKidsT_depths (tau : Nat) : ∀ d n v cs,
    (seedKidsT tau d n v cs).map NodeS3.depth=kdepsT d cs
  | _,_,_,.nil => rfl
  | d,n,v,.none rest => seedKidsT_depths tau d n v rest
  | d,n,v,.some c rest => by
    simp [seedKidsT,kdepsT,seedNodesT_depths tau d n v c,
      seedKidsT_depths tau d (n+tsize c) (v+(valsOf c).length) rest]
end

theorem seedNodesT_length (tau d n v : Nat) (t : PTrie) :
    (seedNodesT tau d n v t).length=tsize t := by
  have h := congrArg List.length (seedNodesT_depths tau d n v t)
  simpa [depsT_length] using h

end ZkFormal.NearV3.Render.UpsGen
