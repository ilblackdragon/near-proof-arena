import ZkFormal.NearV3.Rcpt.Candidates.UpsRequestInventory
import ZkFormal.NearV3.Rcpt.Candidates.WalkRanksWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen

def rankUps (previous : List WStep3) (I : Render.UpsInst) : Render.UpsInst :=
  {I with walk:=(rankWalk previous {w:=I.tau,tau:=I.tau,steps:=I.walk}).steps}

theorem rankUps_semantics (previous : List WStep3) (I : Render.UpsInst) (t : Nat) :
    (step (rankUps previous I) t).mode=(step I t).mode ∧
    (step (rankUps previous I) t).sym=(step I t).sym ∧
    (step (rankUps previous I) t).e=(step I t).e ∧
    (step (rankUps previous I) t).bm=(step I t).bm ∧
    (step (rankUps previous I) t).hv=(step I t).hv :=
  rankWalk_semantics previous {w:=I.tau,tau:=I.tau,steps:=I.walk} t

@[simp] theorem rankUps_mode (p : List WStep3) (I : Render.UpsInst) (t : Nat) :
    (step (rankUps p I) t).mode=(step I t).mode := (rankUps_semantics p I t).1
@[simp] theorem rankUps_edge (p : List WStep3) (I : Render.UpsInst) (t : Nat) :
    (step (rankUps p I) t).e=(step I t).e := (rankUps_semantics p I t).2.2.1
@[simp] theorem rankUps_bitmap (p : List WStep3) (I : Render.UpsInst) (t : Nat) :
    (step (rankUps p I) t).bm=(step I t).bm := (rankUps_semantics p I t).2.2.2.1
@[simp] theorem rankUps_hv (p : List WStep3) (I : Render.UpsInst) (t : Nat) :
    (step (rankUps p I) t).hv=(step I t).hv := (rankUps_semantics p I t).2.2.2.2
@[simp] theorem rankUps_lv (p : List WStep3) (I : Render.UpsInst) (t : Nat) :
    lv (rankUps p I) t=lv I t := by simp [lv,ent]

@[simp] theorem rankUps_tau (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).tau=I.tau := rfl
@[simp] theorem rankUps_N (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).N=I.N := rfl
@[simp] theorem rankUps_ts (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).ts=I.ts := rfl
@[simp] theorem rankUps_ti (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).ti=I.ti := rfl
@[simp] theorem rankUps_D (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).D=I.D := rfl
@[simp] theorem rankUps_ci (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).ci=I.ci := rfl
@[simp] theorem rankUps_x (p : List WStep3) (I : Render.UpsInst) : (rankUps p I).x=I.x := rfl

theorem rankUps_walkOk (p : List WStep3) (I : Render.UpsInst) (h : WalkOkU I) :
    WalkOkU (rankUps p I) := by
  constructor
  · simpa using h.mode
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.w0
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.stepE
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.chain
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode] using h.drain
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.absK
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge,rankUps_bitmap,rankUps_hv] using h.absB
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.inRec
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge,rankUps_lv] using h.look
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode] using h.tsStep
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_edge] using h.termI
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_lv] using h.termD
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.termX
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode] using h.termCase
  · simpa only [rankUps_tau,rankUps_N,rankUps_ts,rankUps_ti,rankUps_D,rankUps_ci,rankUps_x,rankUps_mode,rankUps_edge] using h.termEk

theorem rankUps_instOk (p : List WStep3) (I : Render.UpsInst) (h : InstOk I) :
    InstOk (rankUps p I) :=
  {h with walk:=rankUps_walkOk p I h.walk}

theorem rankUps_parts (p : List WStep3) (I : Render.UpsInst) (h : NativePartFamily I) :
    NativePartFamily (rankUps p I) := by
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

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
