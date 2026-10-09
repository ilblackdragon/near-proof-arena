import ZkFormal.NearV3.Tables.NodeUpb
import ZkFormal.NearV3.Tables.Val
import ZkFormal.NearV3.Rcpt.Tables.Size
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
import ZkFormal.Size.V3Synth

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- Candidate-only SIZE tuple extension; every non-SIZE interaction is identical. -/
def withCount (count : Expr) (i : Interaction) : Interaction  := 
  if i.bus=B_SIZE then {i with msg := i.msg++[count]} else i

def nodeCount : Nat  :=  NodeV3.tableU.width
def valCount : Nat  :=  ValV3.table.width

def nodeIncrement : Expr  :=  .mul (c NodeV3.nf) (not (c NodeV3.dup))
/-- Empty values still contain a native four-byte record-length prefix. -/
def valIncrement : Expr  :=  .mul (c ValV3.vf) (not (c ValV3.dup))

def countConstraints (col : Nat) (inc : Expr) : List Expr  := 
  [.mul .isFirst (c col), .mul .isTransition (sub (n col) (.add (c col) inc))]

def nodeTable : ZkFormal.Air.Table  := 
  { NodeV3.tableU with
    width := NodeV3.tableU.width + 1
    constraints := NodeV3.tableU.constraints++countConstraints nodeCount nodeIncrement
    interactions := NodeV3.tableU.interactions.map (withCount (c nodeCount))}

def valTable : ZkFormal.Air.Table  := 
  { ValV3.table with
    width := ValV3.table.width + 1
    constraints := ValV3.constraints++countConstraints valCount valIncrement
    interactions := ValV3.interactions.map (withCount (c valCount))}

/-- Source SIZE already pays receipt/path payload and contributes no store records. -/
def sourceTable (T : ZkFormal.Air.Table) : ZkFormal.Air.Table  := 
  { T with interactions := T.interactions.map (withCount (k 0))}

def count : Nat  :=  SizeV3.width
def countTotal : Nat  :=  SizeV3.width + 1

def oldTotalBound : Expr  := 
  .mul (c SizeV3.la) (sub SizeV3.bitsE
    (sub (sub (k 8388608) SizeV3.ovhE) (c SizeV3.tot)))

def newTotalBound : Expr  := 
  .mul (c SizeV3.la) (sub SizeV3.bitsE
    (sub (sub (sub (k 8388608) SizeV3.ovhE) (c SizeV3.tot)) (smul 4 (c countTotal))))

/-- Payload-base bound stays EXACTLY the old three-million-byte constraint.
Only the total-witness bound charges the separately authenticated record counts. -/
def sizeTable : ZkFormal.Air.Table  := 
  { SizeV3.table with
    width := SizeV3.width + 2
    constraints := SizeV3.constraints.filter (fun e => e != oldTotalBound) ++
      [.mul .isFirst (sub (c countTotal) (c count)),
       mul3 .isTransition (n SizeV3.act)
         (sub (n countTotal) (.add (c countTotal) (n count))),
       newTotalBound]
    interactions := SizeV3.interactions.map (withCount (c count))}

theorem untouched_interaction (e : Expr) (i : Interaction) (h : i.bus≠B_SIZE) :
    withCount e i=i  :=  by simp [withCount,h]

theorem empty_value_count : valIncrement=
    .mul (c ValV3.vf) (not (c ValV3.dup))  :=  rfl

set_option maxRecDepth 32768 in
theorem candidate_shapes :
    ZkFormal.Size.shapeOf 2 nodeTable=ZkFormal.Size.V3.sh 187 11 6 11 22 ∧
    ZkFormal.Size.shapeOf 2 valTable=ZkFormal.Size.V3.sh 16 4 5 4 22 ∧
    ZkFormal.Size.shapeOf 2 sizeTable=ZkFormal.Size.V3.sh 33 1 3 1 2  :=  by
  decide +kernel

set_option maxRecDepth 32768 in
theorem wellformed :
    nodeTable.wf ⟨[nodeTable],65,202⟩ 4=true ∧
    valTable.wf ⟨[valTable],65,202⟩ 4=true ∧
    sizeTable.wf ⟨[sizeTable],65,202⟩ 4=true := by decide +kernel

set_option maxRecDepth 32768 in
theorem payload_bound_preserved :
    .mul (c SizeV3.lb) (sub SizeV3.bitsE (sub (k 3000000) (c SizeV3.base)))∈
      sizeTable.constraints := by
  simp only [sizeTable,SizeV3.constraints,List.mem_append,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false]
  simp [oldTotalBound]
  exact Or.inl (by decide +kernel)

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
