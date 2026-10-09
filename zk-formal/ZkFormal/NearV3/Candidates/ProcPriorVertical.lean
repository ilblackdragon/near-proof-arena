import ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
import ZkFormal.NearV3.Candidates.ProcPriorIdTable
import ZkFormal.NearV3.Candidates.ProcPriorRawFrame

/-! Isolated three-stage overlay. Component columns share the first 23 slots;
three one-hot stage columns and first/last markers delimit contiguous windows.
This is not installed in the active family. Complete trace extraction and
assembly remain obligations, as do raw record limb/lookup joins. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical
open ZkFormal.Air ZkFormal.Chacha.Table.E ZkFormal.Size
open ZkFormal.Chacha.Table (boolC)

def stage (i : Nat) : Nat:=23+i
def first : Nat:=26
def last : Nat:=27
def width : Nat:=28

def expression : Expr→Expr
  | .isFirst=>c first
  | .isLast=>c last
  | .isTransition=>sub (k 1) (c last)
  | .add a b=>.add (expression a) (expression b)
  | .mul a b=>.mul (expression a) (expression b)
  | .neg a=>.neg (expression a)
  | e=>e

def interaction (i : Nat) (x : Interaction) : Interaction:=
  {x with mult:=x.mult.map (fun e=>.mul (c (stage i)) (expression e)),msg:=x.msg.map expression}

def component (i : Nat) (T : Air.Table) : Air.Table:=
  {T with
    constraints:=T.constraints.map (fun e=>.mul (c (stage i)) (expression e))
    interactions:=T.interactions.map (interaction i)}

def components : List Air.Table:=
  [ProcPriorMemoryGated.table 67 68 69,ProcPriorIdTable.table 70 71 72 69,
   ProcPriorRawFrame.table 59 73 B_VBYTES 74 75]

def windows : List Expr:=
  [stage 0,stage 1,stage 2,first,last].map boolC ++
  [sub (.add (c (stage 0)) (.add (c (stage 1)) (c (stage 2)))) (k 1),
   .mul .isFirst (sub (c first) (k 1)), .mul .isLast (sub (c last) (k 1)),
   .mul .isFirst (sub (c (stage 0)) (k 1)),.mul .isLast (sub (c (stage 2)) (k 1)),
   .mul .isTransition (sub (n first) (c last)),
   .mul (.mul .isTransition (c last)) (n (stage 0)),
   .mul (.mul .isTransition (c last)) (sub (n (stage 1)) (c (stage 0))),
   .mul (.mul .isTransition (c last)) (sub (n (stage 2)) (c (stage 1))),
   .mul (.mul .isTransition (c last)) (c (stage 2))] ++
  (List.range 3).map (fun i=>.mul (.mul .isTransition (sub (k 1) (c last))) (sub (n (stage i)) (c (stage i))))

def table : Air.Table:=
  {width:=width,maxLog:=22,
   constraints:=windows++(components.zipIdx.flatMap fun (T,i)=>(component i T).constraints),
   interactions:=components.zipIdx.flatMap fun (T,i)=>(component i T).interactions}

set_option maxRecDepth 32768 in
theorem standalone_wf : table.wf ⟨[table],76,202⟩ 8=true := by decide +kernel

/-- This isolated ordering has degree10. The fused family must pair phi4
interactions with phi≤2, not assume this ordering is admissible. -/
theorem standalone_shape : shapeOf 2 table=⟨28,9,9,9,22⟩ := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorVertical
