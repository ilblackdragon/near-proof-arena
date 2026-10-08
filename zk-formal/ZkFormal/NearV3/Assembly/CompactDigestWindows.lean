import ZkFormal.NearV3.Assembly.CompactDigestInventory

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- One concrete serialized-node position's request. -/
def nodeDigestMsgs (I : Render.UpsInst) (k p : Nat) : List Msg :=
  let Q:=part I k
  let f:=fieldAt Q.shape p
  if GdB I Q f.1 f.2.1 f.2.2.2=true then
    [digMsg ((dIV I Q f.1 f.2.1 f.2.2.2 k : Fp).toNat)
      ((dLV I Q f.1 f.2.1 f.2.2.2 : Fp).toNat)
      ((List.range 32).map fun i=>(Fp.ofNat (Q.q.getD (p+i) 0)).toNat)] else []

theorem digestRowMsgs_node (I : Render.UpsInst) (k p : Nat) :
    digestRowMsgs I (.q k p)=nodeDigestMsgs I k p := by
  unfold digestRowMsgs digestRowCell qRowCell nodeDigestMsgs
  exact node_row_digest I (part I k) k p _ _ _ _ 0 (fun _=>0)

theorem digestRowMsgs_walk (I : Render.UpsInst) (t : Nat) :
    digestRowMsgs I (.w t)=if t=3 then digestRowMsgs I (.w 3) else [] := by
  by_cases ht:t=3
  · simp [ht]
  · unfold digestRowMsgs digestRowCell
    rw [walk_digest]
    simp [ht]

/-- Complete physical demand inventory: one final root request per instance,
plus every actual fresh digest window in its serialized output parts. No
job or window multiplicity is removed. -/
theorem compactGeneratedDigests_windows (insts : List Render.UpsInst) :
    compactGeneratedDigests insts=(List.range insts.length).flatMap (fun i=>
      digestRowMsgs (inst insts i) (.w 3) ++
      (List.range (nQ (inst insts i))).flatMap (fun k=>
        (List.range (part (inst insts i) k).q.length).flatMap (nodeDigestMsgs (inst insts i) k))) := by
  rw [compactGeneratedDigests_recs]
  simp only [compactRecs,List.flatMap_assoc,List.flatMap_map]
  apply congrArg (fun f=>(List.range insts.length).flatMap f)
  funext i
  simp only [compactRecsI,List.flatMap_append,List.flatMap_map,List.flatMap_assoc]
  rw [show List.range 4=[0,1,2,3] from rfl]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [digestRowMsgs_walk _ 0,digestRowMsgs_walk _ 1,digestRowMsgs_walk _ 2]
  simp only [show ¬(0:Nat)=3 by decide,show ¬(1:Nat)=3 by decide,
    show ¬(2:Nat)=3 by decide,ite_false,List.nil_append]
  simp only [digestRowMsgs_node]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
