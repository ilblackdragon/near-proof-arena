import ZkFormal.NearV3.Rcpt.Candidates.UpsGeneratedTraffic
import ZkFormal.NearV3.Render.Ups.Traffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows

private theorem flat_congr {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.flatMap_cons];rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]

theorem walk_bus_row_congr (C C' D D' : URow) (h : ∀x<200,C x=C' x)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs C D bus sd=uMsgs C' D' bus sd := by
  have hs:=h 173 (by decide)
  have hk:=h 174 (by decide)
  have hb':=h 175 (by decide)
  have hn:=h 49 (by decide)
  have hi:=h 50 (by decide)
  have hnib:=h 51 (by decide)
  have hn2:=h 52 (by decide)
  have hi2:=h 53 (by decide)
  have hek:=h 54 (by decide)
  have hv:=h 56 (by decide)
  have hbm:=h 57 (by decide)
  have hu:=h 105 (by decide)
  rcases hb with rfl|rfl <;> cases sd <;>
    simp [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,
      Dsl.c,Dsl.k,UpsV3.edgeMsg,UpsV3.bmapMsg,
      UpsV3.mS,UpsV3.mK,UpsV3.mB,UpsV3.nN,UpsV3.nI,UpsV3.nib,UpsV3.nN2,
      UpsV3.nI2,UpsV3.ek,UpsV3.u,UpsV3.wbm,UpsV3.hv,
      B_BMAP,B_EDGE,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD,
      hs,hk,hb',hn,hi,hnib,hn2,hi2,hek,hv,hbm,hu]

theorem physical_segment_rows (Is : List UpsInst) (tr : Trace Fp) (t : Nat)
    (hlog : tr.log t=logOf (R Is+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell Is r x:Int):Fp))
    (i : Nat) (hi : i<Is.length) (d : Nat) (hd : d<(recsI (inst Is i)).length)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs ((segOf tr t (start Is i,(recsI (inst Is i)).length)).row d)
      ((segOf tr t (start Is i,(recsI (inst Is i)).length)).next d) bus sd=
    uMsgs (generatedRow Is (start Is i+d) (i,(recsI (inst Is i)).getD d default))
      (fun _=>0) bus sd := by
  apply walk_bus_row_congr _ _ _ _ ?_ bus hb sd
  intro x hx
  rw [segOf_row tr t _ hd]
  have hH:=height_ge hlog
  have hend : start Is i+(recsI (inst Is i)).length≤R Is := by
    rw [←start_succ,←start_len]
    exact sum_mono (by omega)
  rw [rowC_cell hcell (by omega) hx]
  simp only [cell,show start Is i+d<R Is by omega,ite_true,recs_seg hi hd]
  rfl

theorem generated_position_irrelevant (Is : List UpsInst) (i q q' : Nat) (r : RK)
    (D D' : URow) (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs (generatedRow Is q (i,r)) D bus sd=
      uMsgs (generatedRow Is q' (i,r)) D' bus sd := by
  cases r with
  | w n=>rw [walk_generated_interactions Is q i n D bus hb sd,
      walk_generated_interactions Is q' i n D' bus hb sd]
  | v p=>rw [value_interactions_silent Is q i p D bus hb sd,
      value_interactions_silent Is q' i p D' bus hb sd]
  | q k p=>rw [part_interactions_silent Is q i k p D bus hb sd,
      part_interactions_silent Is q' i k p D' bus hb sd]

private theorem map_range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i=>xs.getD i d)=xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]

theorem physical_segment_messages (Is : List UpsInst) (tr : Trace Fp) (t : Nat)
    (hlog : tr.log t=logOf (R Is+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell Is r x:Int):Fp))
    (i : Nat) (hi : i<Is.length) (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    (segOf tr t (start Is i,(recsI (inst Is i)).length)).msgs bus sd=
      upsWalkMessages [inst Is i] bus sd := by
  unfold UpsSeg.msgs
  rw [segOf_len]
  have hh : (List.range (recsI (inst Is i)).length).flatMap
      (fun d=>uMsgs ((segOf tr t (start Is i,(recsI (inst Is i)).length)).row d)
        ((segOf tr t (start Is i,(recsI (inst Is i)).length)).next d) bus sd)=
    (List.range (recsI (inst Is i)).length).flatMap
      (fun d=>uMsgs (generatedRow Is 0 (i,(recsI (inst Is i)).getD d default)) (fun _=>0) bus sd) := by
    apply flat_congr
    intro d hd
    rw [physical_segment_rows Is tr t hlog hcell i hi d (List.mem_range.mp hd) bus hb sd]
    exact generated_position_irrelevant Is i _ 0 _ _ _ bus hb sd
  rw [hh]
  have he:=congrArg (List.flatMap (fun r=>uMsgs (generatedRow Is 0 (i,r)) (fun _=>0) bus sd))
    (map_range_getD (recsI (inst Is i)) default)
  rw [List.flatMap_map] at he
  rw [he]
  exact generated_instance_traffic Is i (fun _=>0) (fun _ _=>0) bus hb sd

theorem physical_view_messages (Is : List UpsInst) (tr : Trace Fp) (t : Nat)
    (hlog : tr.log t=logOf (R Is+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell Is r x:Int):Fp))
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    (viewOf tr t (segsOf Is)).flatMap (fun s=>s.msgs bus sd)=upsWalkMessages Is bus sd := by
  simp only [viewOf,segsOf,List.flatMap_map]
  apply Eq.trans (b := (List.range Is.length).flatMap (fun i=>upsWalkMessages [inst Is i] bus sd))
  · apply flat_congr
    intro i hi
    exact physical_segment_messages Is tr t hlog hcell i (List.mem_range.mp hi) bus hb sd
  · have he:=congrArg (List.flatMap (fun I=>upsWalkMessages [I] bus sd))
      (map_range_getD Is default)
    simp only [List.flatMap_map] at he
    change _ = _ at he
    rw [show (List.range Is.length).flatMap (fun i=>upsWalkMessages [inst Is i] bus sd)=
      Is.flatMap (fun I=>upsWalkMessages [I] bus sd) from he]
    simp only [upsWalkMessages,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem physical_walk_bus_count (Is : List UpsInst) (hs : UpsShape Is) (tr : Trace Fp)
    (t : Nat) (pub : List Fp) (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R Is+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell Is r x:Int):Fp))
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) (m : List Fp) :
    tableBusCount UpsV3.interactions tr t pub bus sd m=
      ((upsWalkMessages Is bus sd).map Msg.toFp).count m := by
  have h:=ups_render_traffic Is hs tr t pub hL hlog hcell bus m
  cases sd
  · have hh:=h.2
    change _=((viewOf tr t (segsOf Is)).flatMap (fun s=>s.msgs bus false) |>.map Msg.toFp).count m at hh
    rwa [physical_view_messages Is tr t hlog hcell bus hb false] at hh
  · have hh:=h.1
    change _=((viewOf tr t (segsOf Is)).flatMap (fun s=>s.msgs bus true) |>.map Msg.toFp).count m at hh
    rwa [physical_view_messages Is tr t hlog hcell bus hb true] at hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
