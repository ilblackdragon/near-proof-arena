import ZkFormal.NearV3.Candidates.ProcPriorOverlayLocal
import ZkFormal.NearV3.Candidates.ProcPriorVertical4Traffic
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficEval
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorVertical4DataEval ProcPriorVertical4ClockCases
open ProcPriorOverlayCuts ProcPriorOverlayGeometry

theorem mult_congr (en fn : Env Fp) (es : List Expr) (k : Nat)
    (h:∀e∈es,e.evalWith en=e.evalWith fn) : multWith en es k=multWith fn es k := by
  induction es generalizing k with
  | nil=>rfl
  | cons e es ih=>
    simp only [multWith,h e (by simp)]
    rw [ih (k+1) (fun q hq=>h q (by simp [hq]))]

theorem traffic_congr (is : List Interaction) (en fn : Env Fp) (bus : Nat) (sd : Bool)
    (h:∀a∈is,∀e∈a.mult++a.msg,e.evalWith en=e.evalWith fn) :
    trafficWith is en bus sd=trafficWith is fn bus sd := by
  unfold trafficWith
  apply flatMap_congr'
  intro a ha
  rw [mult_congr en fn a.mult 0 (fun e he=>h a ha e (List.mem_append_left _ he))]
  have hm:a.msg.map (fun e=>e.evalWith en)=a.msg.map (fun e=>e.evalWith fn):=
    List.map_congr_left (fun e he=>h a ha e (List.mem_append_right _ he))
  rw [hm]

/-- Every interior component expression sees exactly its original physical
row, including next-row comparator operands and relocated first selectors. -/
theorem interior (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i r t : Nat) (hlog:(source i).log 0=22)
    (hr:r<2^22) (hi:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=i)
    (hend:r+1<stop bs i) (pub : List Fp) (e : Expr)
    (hcol:e.colBound≤23) (hpub:e.pubBound=0) :
    (expression e).eval (trace bs (fun n=>(source n).cell 0)) t r pub=
      e.eval (source i) 0 (r-start bs i) [] := by
  rw [ProcPriorOverlayDataTransport.translated bs _ t r pub e hcol hpub]
  have hg:=position bs hc (fun n=>(source n).cell 0) r hr
  dsimp only at hg
  rw [hi] at hg
  obtain ⟨hstart,hstop,hmax,hd,hf,hl,hn⟩:=hg
  rw [hd,hf,hl,hn hend]
  have hlast:¬r-start bs i+1=stop bs i-start bs i:=by omega
  have hlt:r-start bs i+1<2^22:=by omega
  have he:logicalEnv ((source i).cell 0 (r-start bs i)) ((source i).cell 0 (r-start bs i+1))
      (decide (r-start bs i=0)) (decide (r-start bs i+1=stop bs i-start bs i))=
      rowEnv (source i) 0 (r-start bs i) [] := by
    simp only [logicalEnv,ProcPriorCells.env,rowEnv,Trace.height,hlog,
      Nat.mod_eq_of_lt hlt,flag,decide_eq_true_eq,hlast,ite_false]
    have hne:r-start bs i+1≠2^22:=by omega
    simp only [hne,ite_false]
    congr 1
    funext c nx
    cases nx <;> rfl
  exact congrArg (e.evalWith) he
end ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficEval
