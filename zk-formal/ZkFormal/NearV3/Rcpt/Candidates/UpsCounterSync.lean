import ZkFormal.NearV3.Rcpt.Candidates.UpsRankPhysical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen

/-- UPS has one physical counter column shared by EDGE and BMAP. -/
def syncStep (st : WStep3) : WStep3 := {st with u:=if st.mode=2 then st.ub else st.u}
def syncUps (I : Render.UpsInst) : Render.UpsInst := {I with walk:=I.walk.map syncStep}

private theorem sync_get : ∀(ss : List WStep3)(t : Nat),
    (ss.map syncStep).getD t default=syncStep (ss.getD t default)
  | [],_=>rfl
  | s::ss,0=>rfl
  | s::ss,t+1=>sync_get ss t

theorem syncUps_semantics (I : Render.UpsInst) (t : Nat) :
    (step (syncUps I) t).mode=(step I t).mode ∧
    (step (syncUps I) t).sym=(step I t).sym ∧
    (step (syncUps I) t).e=(step I t).e ∧
    (step (syncUps I) t).bm=(step I t).bm ∧
    (step (syncUps I) t).hv=(step I t).hv := by
  simp only [step,syncUps,sync_get,syncStep]
  trivial

@[simp] theorem syncUps_mode (I : Render.UpsInst) (t : Nat) :
    (step (syncUps I) t).mode=(step I t).mode := (syncUps_semantics I t).1
@[simp] theorem syncUps_edge (I : Render.UpsInst) (t : Nat) :
    (step (syncUps I) t).e=(step I t).e := (syncUps_semantics I t).2.2.1
@[simp] theorem syncUps_bitmap (I : Render.UpsInst) (t : Nat) :
    (step (syncUps I) t).bm=(step I t).bm := (syncUps_semantics I t).2.2.2.1
@[simp] theorem syncUps_hv (I : Render.UpsInst) (t : Nat) :
    (step (syncUps I) t).hv=(step I t).hv := (syncUps_semantics I t).2.2.2.2
@[simp] theorem syncUps_lv (I : Render.UpsInst) (t : Nat) :
    lv (syncUps I) t=lv I t := by simp [lv,ent]

@[simp] theorem syncUps_tau (I : Render.UpsInst) : (syncUps I).tau=I.tau := rfl
@[simp] theorem syncUps_N (I : Render.UpsInst) : (syncUps I).N=I.N := rfl
@[simp] theorem syncUps_ts (I : Render.UpsInst) : (syncUps I).ts=I.ts := rfl
@[simp] theorem syncUps_ti (I : Render.UpsInst) : (syncUps I).ti=I.ti := rfl
@[simp] theorem syncUps_D (I : Render.UpsInst) : (syncUps I).D=I.D := rfl
@[simp] theorem syncUps_ci (I : Render.UpsInst) : (syncUps I).ci=I.ci := rfl
@[simp] theorem syncUps_x (I : Render.UpsInst) : (syncUps I).x=I.x := rfl

theorem syncUps_walkOk (I : Render.UpsInst) (h : WalkOkU I) :
    WalkOkU (syncUps I) := by
  constructor
  · simpa using h.mode
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.w0
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.stepE
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.chain
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode] using h.drain
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.absK
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge,syncUps_bitmap,syncUps_hv] using h.absB
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.inRec
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge,syncUps_lv] using h.look
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode] using h.tsStep
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_edge] using h.termI
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_lv] using h.termD
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.termX
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode] using h.termCase
  · simpa only [syncUps_tau,syncUps_N,syncUps_ts,syncUps_ti,syncUps_D,syncUps_ci,syncUps_x,syncUps_mode,syncUps_edge] using h.termEk

theorem syncUps_instOk (I : Render.UpsInst) (h : InstOk I) :
    InstOk (syncUps I) :=
  {h with walk:=syncUps_walkOk I h.walk}

theorem syncUps_parts (I : Render.UpsInst) (h : NativePartFamily I) :
    NativePartFamily (syncUps I) := by
  intro k hk
  have hh:=h k hk
  refine ⟨?_,hh.2.1,?_,?_,?_,hh.2.2.2.2.2⟩
  · obtain ⟨b⟩:=hh.1
    exact ⟨{b with
      freshPrefix:={b.freshPrefix with}
      freshValue:={b.freshValue with}
      splitBitmap:={b.splitBitmap with}
      sourceHeader:=fun hh=>⟨(b.sourceHeader hh).val,{(b.sourceHeader hh).property with}⟩
      movedPrefix:=fun hk=>{b.movedPrefix hk with header:={(b.movedPrefix hk).header with}}
      sourceValue:=fun ht hv=>{b.sourceValue ht hv with}
      copyFields:={b.copyFields with}}⟩
  · have a:=hh.2.2.1
    cases a
    constructor <;> assumption
  · have a:=hh.2.2.2.1
    cases a
    constructor <;> assumption
  · have a:=hh.2.2.2.2.1
    cases a
    constructor <;> assumption


theorem syncUps_counter (I : Render.UpsInst) (t : Nat) :
    (step (syncUps I) t).u=if (step I t).mode=2 then (step I t).ub else (step I t).u := by
  simp only [step,syncUps,sync_get,syncStep]
  rfl

theorem syncUps_render_counter (I : Render.UpsInst) (t : Nat) :
    wCell (syncUps I) t 105=(if (step I t).mode=2 then (step I t).ub else (step I t).u : Nat) := by
  change ((step (syncUps I) t).u : Int)=_
  rw [syncUps_counter]

theorem rankUps_counter_bound (p : List WStep3) (I : Render.UpsInst) (h : InstOk I)
    (t : Nat) (ht : t<4) :
    (step (rankUps p I) t).u<p.length+4 ∧ (step (rankUps p I) t).ub<p.length+4 := by
  have hl : t<I.walk.length := by have hh:=instOk_walk_length I h;omega
  have he : step (rankUps p I) t=rankWalkStep (p++I.walk.take t) I.walk[t] := by
    simp only [rankUps,rankWalk,step,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
      dite_eq_left hl,Option.getD_some,Fin.getElem_fin]
  rw [he]
  have hb:=rankWalkStep_bounds (p++I.walk.take t) I.walk[t]
  simp only [List.length_append,List.length_take] at hb
  omega

theorem physical_rank_counter_bound (p : List WStep3) (I : Render.UpsInst) (h : InstOk I)
    (t : Nat) (ht : t<4) : (step (syncUps (rankUps p I)) t).u<p.length+4 := by
  rw [syncUps_counter]
  have hb:=rankUps_counter_bound p I h t ht
  split <;> omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
