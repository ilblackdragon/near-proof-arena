import ZkFormal.NearV3.Candidates.ProcPriorOverlayLocal
import ZkFormal.NearV3.Assembly.SchedulerPriorCore
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayNativeSources
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorOverlayCuts ProcPriorOverlayGeometry

def memory (bs : List NativeBlock) : Trace Fp :=
  ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) 0 []
def raw (bs : List NativeBlock) : Trace Fp :=ProcRawConcatGeometry.trace bs
def records (bs : List NativeBlock) : Trace Fp :=ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs

def used (bs : List NativeBlock) (i : Nat) : Nat :=
  if i=0 then (ProcPriorNativeMemory.allRows bs).length
  else if i=1 then (ProcPriorOverlayBudget.idRows bs).length
  else if i=2 then (ProcRawConcatGeometry.rows bs).length
  else (ProcRecordConcatTraffic.rows (fun b=>b.pub.ids) bs).length

theorem memory_padding (bs : List NativeBlock) (r : Nat)
    (hr:(ProcPriorNativeMemory.allRows bs).length≤r) : (memory bs).cell 0 r=fun _=>0 := by
  have hc:ProcPriorNativeMemory.cells (ProcPriorNativeMemory.allRows bs) r=fun _=>0:=
    ProcPriorNativeMemory.cells_none _ _ (List.getElem?_eq_none hr)
  funext x
  simp only [memory,ProcPriorMemoryGated.liftTrace]
  by_cases hx:x=ProcPriorMemoryGated.stampGate
  · simp only [hx,ite_true,true_and]
    simp only [ProcPriorMemoryGated.gateExpr,ProcPriorMemoryTable.adjacent,
      ProcPriorMemoryTable.notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.eval,Expr.evalWith,rowEnv,
      ProcPriorNativeMemory.trace,hc,Bool.false_eq_true,ite_false,ite_true]
    grind
  · simp only [hx,ite_false,true_and,ProcPriorNativeMemory.trace,hc]

theorem raw_padding (bs : List NativeBlock) (r : Nat)
    (hr:(ProcRawConcatGeometry.rows bs).length≤r) : (raw bs).cell 0 r=fun _=>0 :=
  ProcRawConcatGeometry.padding bs r hr

theorem record_padding (bs : List NativeBlock) (r : Nat)
    (hr:(ProcRecordConcatTraffic.rows (fun b=>b.pub.ids) bs).length≤r) : (records bs).cell 0 r=fun _=>0 := by
  simp [records,ProcRecordConcatTraffic.trace,List.getD_eq_getElem?_getD,List.getElem?_eq_none hr]

theorem room (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (i : Nat) (hi:i<4) : used bs i<stop bs i-start bs i := by
  have hc:=(cuts bs hn hlen hraw).2.2.2.2
  have cases:i=0∨i=1∨i=2∨i=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl
  all_goals simp [used,start,stop,cutIds,cutMemory,cutRaw] at *
  all_goals omega
end ZkFormal.NearV3.Candidates.ProcPriorOverlayNativeSources
