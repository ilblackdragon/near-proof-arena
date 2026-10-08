import ZkFormal.NearV3.Rcpt.Candidates.NodeUsageList

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

theorem assignList_zip (q : UseRequests) (ss : List NodeS3) (n : Nat) :
    (assignList q n ss).zip (List.range' n ss.length)=
    (ss.zip (List.range' n ss.length)).map (fun (s,i)=>(assignUses q i s,i)) := by
  induction ss generalizing n with
  | nil => simp [assignList]
  | cons s ss ih => simp [assignList,List.range'_succ,ih]

theorem assigned_edge_terminal (q : UseRequests) (n : Nat) (s : NodeS3) :
    ((edgesOf3 n (assignUses q n s)).zip (assignUses q n s).uses).map (fun (e,u)=>e++[u])=
    (edgesOf3 n s).map (fun e=>e++[q.edges.count e]) := by
  have he : edgesOf3 n (assignUses q n s)=edgesOf3 n s := rfl
  rw [he]
  change ((edgesOf3 n s).zip ((edgesOf3 n s).map _)).map _=_
  induction edgesOf3 n s with
  | nil => rfl
  | cons e es ih => simp_all

theorem assigned_upb_terminal (q : UseRequests) (n : Nat) (s : NodeS3) :
    upbOf n (assignUses q n s) (fun p=>(assignUses q n s).mU.getD p 0)=
    (List.range (s.v.ser false).length).map (fun p=>windowKey n p s++[q.windows.count (windowKey n p s)]) := by
  unfold upbOf
  apply List.map_congr_left
  intro p hp
  have hp' : p<(s.v.ser false).length := List.mem_range.mp hp
  have hg : ((List.range (s.v.ser false).length).map (fun p=>q.windows.count (windowKey n p s))).getD p 0=
      q.windows.count (windowKey n p s) := by
    simp [List.getD_eq_getElem?_getD,hp']
  simpa [assignUses,windowKey] using congrArg (fun u=>
    [msgId K_NPOST n,p,(s.v.ser true).getD p 0,(s.v.ser false).length,s.depth,s.ucid.getD p 0,u]) hg

theorem assigned_edges (q : UseRequests) (ss : List NodeS3) :
    nodeRecvs3 (assignList q 0 ss) B_EDGE=
    (ss.zip (List.range ss.length)).flatMap (fun (s,n)=>
      (edgesOf3 n s).map (fun e=>e++[q.edges.count e])) := by
  simp only [nodeRecvs3]
  simp only [show B_EDGE≠B_DIGEST by decide,show B_EDGE≠B_PARENT by decide,ite_false,ite_true]
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  apply congrArg (List.flatMap · (ss.zip (List.range' 0 ss.length)))
  funext x
  exact assigned_edge_terminal q x.2 x.1

theorem assigned_bmaps (q : UseRequests) (ss : List NodeS3) :
    nodeRecvs3 (assignList q 0 ss) B_BMAP=
    (ss.zip (List.range ss.length)).flatMap (fun (s,n)=>
      match s.v.bmap with | none=>[] | some (bm,hv)=>[[n,bm,hv,q.bmaps.count [n,bm,hv]]]) := by
  simp only [nodeRecvs3]
  simp only [show B_BMAP≠B_DIGEST by decide,show B_BMAP≠B_PARENT by decide,
    show B_BMAP≠B_EDGE by decide,ite_false,ite_true]
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  apply congrArg (List.flatMap · (ss.zip (List.range' 0 ss.length)))
  funext x
  simp only [Function.comp_apply,assignUses]
  cases x.1.v.bmap with
  | none => rfl
  | some b => cases b;rfl

theorem assigned_windows (q : UseRequests) (ss : List NodeS3) :
    nodeRecvs3 (assignList q 0 ss) B_UPB=
    (ss.zip (List.range ss.length)).flatMap (fun (s,n)=>
      (List.range (s.v.ser false).length).map (fun p=>
        windowKey n p s++[q.windows.count (windowKey n p s)])) := by
  simp only [nodeRecvs3]
  simp only [show B_UPB≠B_DIGEST by decide,show B_UPB≠B_PARENT by decide,
    show B_UPB≠B_EDGE by decide,show B_UPB≠B_BMAP by decide,
    show B_UPB≠B_DUP by decide,show B_UPB≠B_ENT by decide,ite_false,ite_true]
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  apply congrArg (List.flatMap · (ss.zip (List.range' 0 ss.length)))
  funext x
  exact assigned_upb_terminal q x.2 x.1

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
