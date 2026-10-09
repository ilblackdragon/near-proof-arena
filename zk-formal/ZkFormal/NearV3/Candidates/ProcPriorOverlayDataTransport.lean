import ZkFormal.NearV3.Candidates.ProcPriorOverlayGeometry
import ZkFormal.NearV3.Candidates.ProcPriorOverlayWindowLocal
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayDataTransport
open ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorVertical4ClockCases
open ProcPriorVertical4DataEval ProcPriorOverlayCuts

theorem expression_pub (e : Expr) : (expression e).pubBound=e.pubBound := by
  induction e <;> simp_all [expression,Expr.pubBound,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub]

theorem component_pub : ∀T∈components,∀e∈T.exprs,e.pubBound=0 := by
  have hh:components.all (fun T=>T.exprs.all (fun e=>decide (e.pubBound=0)))=true:=by decide +kernel
  exact fun T ht e he=>of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hh T ht) e he)

/-- Installed expression evaluation sees the actual current and next stage
cells, including a foreign successor at each padding boundary. -/
theorem translated (bs : List NativeBlock) (component : Nat→Nat→Nat→Fp)
    (tt j : Nat) (pub : List Fp) (e : Expr) (hc:e.colBound≤23) (hp:e.pubBound=0) :
    (expression e).eval (trace bs component) tt j pub=
      e.evalWith (logicalEnv (data bs component j) (data bs component ((j+1)%2^22))
        (firstAt (cutMemory bs) (cutIds bs) (cutRaw bs) j)
        (lastAt (cutMemory bs) (cutIds bs) (cutRaw bs) (2^22) j)) := by
  let a:=cutMemory bs
  let b:=cutIds bs
  let c:=cutRaw bs
  let d:=data bs component
  let en:=overlayEnv (d j) (d ((j+1)%2^22)) (stageAt a b c j) (stageAt a b c ((j+1)%2^22))
    (firstAt a b c j) (lastAt a b c (2^22) j)
    (firstAt a b c ((j+1)%2^22)) (lastAt a b c (2^22) ((j+1)%2^22))
    (decide (j=0)) (decide (j+1=2^22))
  have hr:rowEnv (trace bs component) tt j pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,ProcPriorVertical4ClockTrace.trace,Trace.height,en,overlayEnv,
      ProcPriorCells.env,a,b,c,d,flag,decide_eq_true_eq]
    congr 1
    · funext col nx
      cases nx <;> rfl
    · by_cases h:j+1=2^22 <;> simp [h]
  change (expression e).evalWith (rowEnv (trace bs component) tt j pub)=_
  rw [hr,ProcPriorTrace.eval_pub _ (by rw [expression_pub,hp]) en (fun i=>pub.getD i 0)]
  exact translated_data _ _ _ _ _ _ _ _ _ _ e hc
end ZkFormal.NearV3.Candidates.ProcPriorOverlayDataTransport
