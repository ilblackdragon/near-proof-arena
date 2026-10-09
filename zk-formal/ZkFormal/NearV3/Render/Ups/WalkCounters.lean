import ZkFormal.NearV3.Render.Ups.Ok

namespace ZkFormal.NearV3.Render.UpsGen

/-- Assign global EDGE/BMAP occurrence counters after constructing the semantic walk. -/
def withWalkCounters (I : UpsInst) (edgeUse bitmapUse : Nat→Nat) : UpsInst :=
  {I with walk:=I.walk.mapIdx fun t s => {s with u:=edgeUse t,ub:=bitmapUse t}}

@[simp] theorem counter_tau (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).tau=I.tau := rfl
@[simp] theorem counter_N (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).N=I.N := rfl
@[simp] theorem counter_D (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).D=I.D := rfl
@[simp] theorem counter_ts (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).ts=I.ts := rfl
@[simp] theorem counter_ti (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).ti=I.ti := rfl
@[simp] theorem counter_ci (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).ci=I.ci := rfl
@[simp] theorem counter_x (I : UpsInst) (eu bu : Nat→Nat) :
    (withWalkCounters I eu bu).x=I.x := rfl

@[simp] theorem counter_step_mode (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) :
    (step (withWalkCounters I eu bu) t).mode=(step I t).mode := by
  cases h : I.walk[t]? <;> simp [step,withWalkCounters,List.getD_eq_getElem?_getD,h]
@[simp] theorem counter_step_e (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) :
    (step (withWalkCounters I eu bu) t).e=(step I t).e := by
  cases h : I.walk[t]? <;> simp [step,withWalkCounters,List.getD_eq_getElem?_getD,h]
@[simp] theorem counter_step_bm (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) :
    (step (withWalkCounters I eu bu) t).bm=(step I t).bm := by
  cases h : I.walk[t]? <;> simp [step,withWalkCounters,List.getD_eq_getElem?_getD,h]
@[simp] theorem counter_step_hv (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) :
    (step (withWalkCounters I eu bu) t).hv=(step I t).hv := by
  cases h : I.walk[t]? <;> simp [step,withWalkCounters,List.getD_eq_getElem?_getD,h]
@[simp] theorem counter_ent (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) :
    ent (withWalkCounters I eu bu) t=ent I t := by simp only [ent,counter_step_mode,counter_step_e]
@[simp] theorem counter_lv (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) :
    lv (withWalkCounters I eu bu) t=lv I t := by simp only [lv,counter_ent]

theorem counter_step_uses (I : UpsInst) (eu bu : Nat→Nat) (t : Nat) (ht : t<I.walk.length) :
    (step (withWalkCounters I eu bu) t).u=eu t ∧ (step (withWalkCounters I eu bu) t).ub=bu t := by
  simp [step,withWalkCounters,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht]

/-- Global use-counter assignment preserves all local walk constraints. Counter traffic
balance and field-size bounds remain the separate global occurrence allocator's duties. -/
theorem WalkOkU.withCounters {I : UpsInst} (h : WalkOkU I) (eu bu : Nat→Nat) :
    WalkOkU (withWalkCounters I eu bu) := by
  constructor
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode] using h.mode
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.w0
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.stepE
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.chain
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode] using h.drain
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.absK
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e,counter_step_hv,counter_step_bm] using h.absB
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.inRec
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e,counter_lv] using h.look
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode] using h.tsStep
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_e] using h.termI
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_lv] using h.termD
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.termX
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode] using h.termCase
  · simpa only [counter_tau,counter_N,counter_D,counter_ts,counter_ti,counter_ci,counter_x,counter_step_mode,counter_step_e] using h.termEk

theorem InstOk.withCounters {I : UpsInst} (h : InstOk I) (eu bu : Nat→Nat) :
    InstOk (withWalkCounters I eu bu) := by
  exact {h with walk:=h.walk.withCounters eu bu}
end ZkFormal.NearV3.Render.UpsGen
