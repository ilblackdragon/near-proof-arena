import ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficEval
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorOverlayCuts ProcPriorOverlayGeometry

theorem mult_zero (en : Env Fp) (es : List Expr) (k : Nat)
    (h:∀e∈es,e.evalWith en=0) : multWith en es k=0 := by
  induction es generalizing k with
  | nil=>rfl
  | cons e es ih=>
    simp only [multWith,h e (by simp),ih (k+1) (fun q hq=>h q (by simp [hq]))]
    rfl

theorem traffic_zero (is : List Interaction) (en : Env Fp) (bus : Nat) (sd : Bool)
    (h:∀a∈is,∀e∈a.mult,e.evalWith en=0) : trafficWith is en bus sd=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro a ha
  simp only [mult_zero en a.mult 0 (h a ha),List.replicate_zero,ite_self]

/-- Exact active-stage traffic at every interior row; no constraint or bus
ownership assumption is needed for this executable relocation identity. -/
theorem interior (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i r t : Nat) (hi4:i<4) (hlog:(source i).log 0=22)
    (hr:r<2^22) (hi:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=i)
    (hend:r+1<stop bs i) (pub : List Fp) (is : List Interaction)
    (hb:∀a∈is,∀e∈a.mult++a.msg,e.colBound≤23 ∧ e.pubBound=0)
    (bus : Nat) (sd : Bool) :
    rowTraffic (is.map (interaction i)) (trace bs (fun n=>(source n).cell 0)) t r pub bus sd=
      rowTraffic is (source i) 0 (r-start bs i) [] bus sd := by
  rw [traffic_row,traffic_row]
  have hm:(rowEnv (trace bs (fun n=>(source n).cell 0)) t r pub).col (stage i) false=1:=by
    have hh:=ProcPriorOverlayLocal.stage_eval bs source t r i hi4 pub
    rw [hi,ite_eq_left rfl] at hh
    exact hh
  rw [active_traffic is _ i bus sd hm rfl]
  apply ProcPriorOverlayTrafficEval.traffic_congr
  intro a ha e he
  rw [←expression_eval]
  exact ProcPriorOverlayTrafficEval.interior bs hc source i r t hlog hr hi hend pub e
    (hb a ha e he).1 (hb a ha e he).2

/-- Inactive stages produce no traffic, including at physical wrap. -/
theorem inactive (bs : List NativeBlock) (source : Nat→Trace Fp)
    (i r t : Nat) (hi4:i<4)
    (hi:i≠stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r)
    (pub : List Fp) (is : List Interaction) (bus : Nat) (sd : Bool) :
    rowTraffic (is.map (interaction i)) (trace bs (fun n=>(source n).cell 0)) t r pub bus sd=[] := by
  rw [traffic_row]
  apply inactive_traffic is _ i bus sd ?_ rfl
  have hh:=ProcPriorOverlayLocal.stage_eval bs source t r i hi4 pub
  rw [ite_eq_right hi] at hh
  exact hh
/-- Each relocated final padding row is silent even though its successor
belongs to another stage (or wraps to the first physical row). -/
theorem boundary (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i r t : Nat) (hi4:i<4)
    (hr:r<2^22) (hi:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=i)
    (hend:r+1=stop bs i) (hz:(source i).cell 0 (r-start bs i)=fun _=>0)
    (pub : List Fp) (T : Air.Table) (hT:T∈components) (bus : Nat) (sd : Bool) :
    rowTraffic (T.interactions.map (interaction i))
      (trace bs (fun n=>(source n).cell 0)) t r pub bus sd=[] := by
  rw [traffic_row]
  have hm:(rowEnv (trace bs (fun n=>(source n).cell 0)) t r pub).col (stage i) false=1:=by
    have hh:=ProcPriorOverlayLocal.stage_eval bs source t r i hi4 pub
    rw [hi,ite_eq_left rfl] at hh
    exact hh
  rw [active_traffic T.interactions _ i bus sd hm rfl]
  apply traffic_zero
  intro a ha e he
  rw [←expression_eval]
  have hem:e∈T.exprs:=List.mem_append_right _
    (List.mem_flatMap.mpr ⟨a,ha,List.mem_append_left _ he⟩)
  have hc0:=ProcPriorVertical4DataEval.component_columns T hT e hem
  have hp0:=ProcPriorOverlayDataTransport.component_pub T hT e hem
  change (expression e).eval (trace bs (fun n=>(source n).cell 0)) t r pub=0
  rw [ProcPriorOverlayDataTransport.translated bs _ t r pub e hc0 hp0]
  have hg:=position bs hc (fun n=>(source n).cell 0) r hr
  dsimp only at hg
  rw [hi] at hg
  obtain ⟨hstart,hstop,hmax,hd,hf,hl,hn⟩:=hg
  rw [hd,hf,hl,hz]
  exact ProcPriorOverlayPadding.multiplicity T hT _ _ _ _ a ha e he
end ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficRows
