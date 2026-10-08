import ZkFormal.NearV3.Candidates.ProcPriorMemoryTable
import ZkFormal.Near.Extract.BusCount
import ZkFormal.Near.Extract.Eval
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E ZkFormal.Near

def stampGate : Nat := 11
def gateExpr : Expr := .mul ProcPriorMemoryTable.adjacent (.mul (c ProcPriorMemoryTable.same) (ProcPriorMemoryTable.notE (n ProcPriorMemoryTable.query)))
def gateEq : Expr := sub (c stampGate) gateExpr

def interactions (writeBus readBus cmpBus : Nat) : List Interaction :=
  (ProcPriorMemoryTable.interactions writeBus readBus cmpBus).take 3 ++
    [{bus:=cmpBus,mult:=[c stampGate],send:=true,msg:=[n ProcPriorMemoryTable.stamp,.add (c ProcPriorMemoryTable.stamp) (k 1),k 1]}]

def table (writeBus readBus cmpBus : Nat) : Air.Table :=
  {(ProcPriorMemoryTable.table writeBus readBus cmpBus) with
    width := 12
    constraints := ProcPriorMemoryTable.constraints++[ZkFormal.Chacha.Table.boolC stampGate,gateEq]
    interactions:=interactions writeBus readBus cmpBus}

set_option maxRecDepth 32768 in
theorem standalone_wf : (table 0 1 2).wf ⟨[table 0 1 2],3,0⟩ 8=true := by decide +kernel

theorem measured_shape : ZkFormal.Size.shapeOf 2 (table 0 1 2)=⟨12,3,7,3,22⟩ := by decide +kernel

theorem gate_value (wb rb cb : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (h:TableLocal (table wb rb cb) tr tt pub) (r : Nat) (hr:r<tr.height tt) :
    (c stampGate).eval tr tt r pub=gateExpr.eval tr tt r pub := by
  have hz:=h.constr r hr gateEq (by simp [table])
  simp only [gateEq,sub,eval_add,eval_neg] at hz
  grind

theorem row_traffic (wb rb cb : Nat) (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (hg:(c stampGate).eval tr tt r pub=gateExpr.eval tr tt r pub) (bus : Nat) (sd : Bool) :
    rowTraffic (interactions wb rb cb) tr tt r pub bus sd=
      rowTraffic (ProcPriorMemoryTable.interactions wb rb cb) tr tt r pub bus sd := by
  simp only [interactions,ProcPriorMemoryTable.interactions,List.take,List.append_nil,List.nil_append,List.cons_append,
    rowTraffic,List.flatMap_cons,List.flatMap_nil,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,
    hg,gateExpr]

theorem local_row_traffic (wb rb cb : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (h:TableLocal (table wb rb cb) tr tt pub) (r : Nat) (hr:r<tr.height tt) (bus : Nat) (sd : Bool) :
    rowTraffic (table wb rb cb).interactions tr tt r pub bus sd=
      rowTraffic (ProcPriorMemoryTable.table wb rb cb).interactions tr tt r pub bus sd :=
  row_traffic wb rb cb tr tt r pub (gate_value wb rb cb tr tt pub h r hr) bus sd

end ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
