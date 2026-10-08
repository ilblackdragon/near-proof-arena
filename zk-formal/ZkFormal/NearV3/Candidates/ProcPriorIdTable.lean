import ZkFormal.NearV3.Candidates.ProcPriorMemoryTable

/-! Isolated first-public-index lookup. Keys use three limbs, never a field
encoding of an entire u64. Public records and original-record requests are
separate authenticated inventories. Bus IDs remain parameters. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorIdTable
open ZkFormal.Air ZkFormal.Chacha.Table.E ZkFormal.Size
open ZkFormal.Chacha.Table (boolC)

def act : Nat:=0
def tau : Nat:=1
def keyLo : Nat:=2
def keyMid : Nat:=3
def keyHi : Nat:=4
def ordinal : Nat:=5
def isPublic : Nat:=6
def found : Nat:=7
def index : Nat:=8
def take : Nat:=9
def eqTop : Nat:=10
def eqMid : Nat:=11
def eqLo : Nat:=12
def invTop : Nat:=13
def invMid : Nat:=14
def invLo : Nat:=15
def gTop : Nat:=16
def gMid : Nat:=17
def gAll : Nat:=18
def gPublic : Nat:=19
def width : Nat:=20

def notE (e : Expr) : Expr:=sub (k 1) e
def adjacent : Expr:=.mul (c act) (n act)
def top (nx : Bool) : Expr:=.add (.mul (k 65536) (.col tau nx)) (.col keyHi nx)
def dTop : Expr:=sub (top true) (top false)
def dMid : Expr:=sub (n keyMid) (c keyMid)
def dLo : Expr:=sub (n keyLo) (c keyLo)
def eqs (d : Expr) (eq iv : Nat) : List Expr :=
  [.mul adjacent (sub (.mul d (c iv)) (notE (c eq))),.mul adjacent (.mul d (c eq))]

def constraints : List Expr :=
  [act,isPublic,found,take,eqTop,eqMid,eqLo,gTop,gMid,gAll,gPublic].map boolC ++
  [.mul .isLast (c act),
   .mul (.mul .isTransition (notE (c act))) (n act),
   .mul .isFirst (c found),.mul .isFirst (c index),
   .mul (c act) (sub (c take) (.mul (c isPublic) (notE (c found)))),
   .mul (notE (c found)) (c index),
   sub (c gTop) (.mul adjacent (c eqTop)),
   sub (c gMid) (.mul (c gTop) (c eqMid)),
   sub (c gAll) (.mul (c gMid) (c eqLo)),
   sub (c gPublic) (.mul (.mul (c gAll) (c isPublic)) (n isPublic)),
   -- A public row cannot follow a query within the same key group.
   .mul (.mul (c gAll) (notE (c isPublic))) (n isPublic),
   .mul adjacent (sub (n found) (.mul (c gAll) (.add (c found) (c take)))),
   .mul adjacent (sub (n index) (.mul (c gAll) (.add (c index) (.mul (c take) (c ordinal)))))] ++
  eqs dTop eqTop invTop ++ eqs dMid eqMid invMid ++ eqs dLo eqLo invLo

def interactions (publicBus requestBus resultBus cmpBus : Nat) : List Interaction :=
  [{bus:=publicBus,send:=false,mult:=[.mul (c act) (c isPublic)],
    msg:=[c tau,c ordinal,c keyLo,c keyMid,c keyHi]},
   {bus:=requestBus,send:=false,mult:=[.mul (c act) (notE (c isPublic))],
    msg:=[c tau,c ordinal,c keyLo,c keyMid,c keyHi]},
   {bus:=resultBus,send:=true,mult:=[.mul (c act) (notE (c isPublic))],
    msg:=[c tau,c ordinal,c found,c index]},
   {bus:=cmpBus,send:=true,mult:=[adjacent],msg:=[top true,top false,k 1]},
   {bus:=cmpBus,send:=true,mult:=[c gTop],msg:=[n keyMid,c keyMid,k 1]},
   {bus:=cmpBus,send:=true,mult:=[c gMid],msg:=[n keyLo,c keyLo,k 1]},
   {bus:=cmpBus,send:=true,mult:=[c gPublic],msg:=[n ordinal,.add (c ordinal) (k 1),k 1]}]

def table (publicBus requestBus resultBus cmpBus : Nat) : Air.Table :=
  {width:=width,constraints:=constraints,interactions:=interactions publicBus requestBus resultBus cmpBus,maxLog:=22}

set_option maxRecDepth 32768 in
theorem standalone_wf : (table 0 1 2 3).wf ⟨[table 0 1 2 3],4,0⟩ 8=true := by decide +kernel

theorem measured_shape : shapeOf 2 (table 0 1 2 3)=⟨20,4,7,4,22⟩ := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorIdTable
