import ZkFormal.NearV3.Candidates.ProcPriorTraceLocal
import ZkFormal.NearV3.Candidates.ProcCodecPriorReadNative
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorRows ProcPriorEvents
open ZkFormal.NearV3.Assembly.CodecDigest

structure Tagged where
  tau : Nat
  row : Row

instance : Inhabited Tagged := ⟨⟨0,⟨⟨0,0,false,0,false⟩,(0,false)⟩⟩⟩

def address (a : Tagged) : Nat :=4096*a.tau+a.row.event.link

def tagged (b : NativeBlock) : List Tagged :=
  (rows b.pub.ids b.old.links).map (fun r=>⟨b.run.tau,r⟩)
def allRows (bs : List NativeBlock) : List Tagged :=bs.flatMap tagged

def nextSame (xs : List Tagged) (j : Nat) (a : Tagged) : Bool :=
  match xs[j+1]? with | none=>false | some b=>decide (address a=address b)
def nextInverse (xs : List Tagged) (j : Nat) (a : Tagged) : Fp :=
  match xs[j+1]? with | none=>0 | some b=>(Fp.ofNat (address b)-Fp.ofNat (address a))⁻¹
def cells (xs : List Tagged) (j : Nat) : Nat→Fp :=
  match xs[j]? with
  | none=>fun _=>0
  | some a=>ProcPriorCells.cell a.row a.tau (nextSame xs j a) (nextInverse xs j a)
def trace (xs : List Tagged) : Trace Fp :=⟨fun _=>22,fun _ j=>cells xs j⟩
def queryMessage (a : Tagged) : List Fp :=
  [Fp.ofNat a.tau,Fp.ofNat a.row.event.link,Fp.ofNat a.row.event.lo,ProcPriorCells.bit a.row.event.hi]
def queryMessages (xs : List Tagged) : List (List Fp) :=
  xs.flatMap (fun a=>if a.row.event.query then [queryMessage a] else [])

/-- This executable tagged trace uses packed address differences also across
instance boundaries. Local legality and comparator ownership are separate. -/
theorem row_query (xs : List Tagged) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorMemoryTable.interactions 67 68 69) (trace xs) t r pub 68 true=
      match xs[r]? with | none=>[] | some a=>if a.row.event.query then [queryMessage a] else [] := by
  cases ha:xs[r]? with
  | none =>
    simp [rowTraffic,ProcPriorMemoryTable.interactions,Interaction.multNat,Interaction.multNat.go,
      Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,trace,cells,ha,ZkFormal.Chacha.Table.E.c,
      ProcPriorMemoryTable.act,ProcPriorMemoryTable.query]
    decide +kernel
  | some a =>
    cases hq:a.row.event.query <;>
      simp [rowTraffic,ProcPriorMemoryTable.interactions,Interaction.multNat,Interaction.multNat.go,
        Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,trace,cells,ha,ZkFormal.Chacha.Table.E.c,
        ProcPriorMemoryTable.act,ProcPriorMemoryTable.query,ProcPriorCells.cell,ProcPriorCells.bit,hq,
        ProcPriorMemoryTable.tau,ProcPriorMemoryTable.link,ProcPriorMemoryTable.lo,ProcPriorMemoryTable.hi,queryMessage]
    all_goals simp only [show (1:Fp)*0=0 from by decide +kernel,show (1:Fp)*1=1 from by decide +kernel,
      show (0:Fp)≠1 from by decide +kernel,ite_true,ite_false,List.replicate_one,List.replicate_zero,not_false_eq_true]

theorem physical_queries (xs : List Tagged) (hc:xs.length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic (ProcPriorMemoryTable.interactions 67 68 69)
      (trace xs) t r pub 68 true)=queryMessages xs := by
  simp only [row_query]
  rw [show 2^22=xs.length+(2^22-xs.length) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-xs.length)).flatMap (fun j=>match xs[xs.length+j]? with
      | none=>[] | some a=>if a.row.event.query then [queryMessage a] else [])=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [List.getElem?_eq_none (by omega)]
  rw [hz,List.append_nil]
  have hi:(List.range xs.length).map (fun r=>xs[r]!)=xs := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact getElem!_pos xs i hj
  unfold queryMessages
  conv => rhs; rw [←hi,List.flatMap_map]
  apply ProcCodecPublicIdEnumeration.flat_congr
  intro j hj
  rw [List.getElem?_eq_getElem (List.mem_range.mp hj),getElem!_pos xs j (List.mem_range.mp hj)]

end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory

