import ZkFormal.NearV3.Candidates.ProcPriorRawFrame

/-! Isolated original-record join. Three 24/24/16-bit limb rows decode each
u64 word, preserving all original records and both original ID queries.
Parameter and byte buses must be authenticated by the enclosing assembly. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordTable
open ZkFormal.Air ZkFormal.Chacha.Table.E ZkFormal.Size
open ZkFormal.Chacha.Table (boolC)

def act : Nat:=0
def tau : Nat:=1
def record : Nat:=2
def shards : Nat:=3
def sender : Nat:=4
def receiver : Nat:=5
def amount : Nat:=6
def firstLimb : Nat:=7
def midLimb : Nat:=8
def topLimb : Nat:=9
def byte0 : Nat:=10
def byte1 : Nat:=11
def byte2 : Nat:=12
def lo : Nat:=13
def mid : Nat:=14
def hi : Nat:=15
def senderFound : Nat:=16
def senderIndex : Nat:=17
def receiverFound : Nat:=18
def receiverIndex : Nat:=19
def big : Nat:=20
def bigInv : Nat:=21
def writeGate : Nat:=22
def width : Nat:=23

def notE (x : Expr) : Expr:=sub (k 1) x
def words (nx : Bool) : Expr:=.add (.add (.col sender nx) (.col receiver nx)) (.col amount nx)
def limbs (nx : Bool) : Expr:=.add (.add (.col firstLimb nx) (.col midLimb nx)) (.col topLimb nx)
def header (nx : Bool) : Expr:=sub (.col act nx) (words nx)
def packed : Expr:=.add (.add (c byte0) (.mul (k 256) (c byte1))) (.mul (k 65536) (c byte2))
def adjacent : Expr:=.mul (c act) (n act)
def sameRecord : Expr:=.mul (words false) (notE (.mul (c amount) (c topLimb)))
def sameWord : Expr:=.mul (words false) (notE (c topLimb))
def offset : Expr:=.add (.mul (k 8) (.add (c receiver) (.mul (k 2) (c amount))))
  (.mul (k 3) (.add (c midLimb) (.mul (k 2) (c topLimb))))
def queryGate : Expr:=.mul (c topLimb) (.add (c sender) (c receiver))
def queryOrdinal : Expr:=.add (.mul (k 2) (c record)) (c receiver)
def selected (s r : Nat) : Expr:=.add (.mul (c sender) (c s)) (.mul (c receiver) (c r))
def link : Expr:=.add (.mul (c senderIndex) (c shards)) (c receiverIndex)

def constraints : List Expr:=
  [act,sender,receiver,amount,firstLimb,midLimb,topLimb,senderFound,receiverFound,big,writeGate].map boolC ++
  [.mul (header false) (sub (header false) (k 1)),
   sub (limbs false) (words false),
   .mul .isLast (c act),
   .mul (.mul .isTransition (notE (c act))) (n act),
   .mul .isFirst (sub (c act) (header false)),
   .mul .isFirst (c tau),
   .mul (header false) (c record),
   .mul (header false) (c senderFound),.mul (header false) (c senderIndex),
   .mul (header false) (c receiverFound),.mul (header false) (c receiverIndex),
   .mul (c firstLimb) (sub (c lo) packed),
   .mul (c midLimb) (sub (c mid) packed),
   .mul (c topLimb) (sub (c hi) packed),
   .mul (c topLimb) (c byte2),
   .mul (words false) (sub (.mul (.add (c mid) (c hi)) (c bigInv)) (c big)),
   .mul (words false) (.mul (.add (c mid) (c hi)) (notE (c big))),
   .mul (notE (c senderFound)) (c senderIndex),
   .mul (notE (c receiverFound)) (c receiverIndex),
   sub (c writeGate) (.mul (.mul (.mul (c amount) (c topLimb)) (c senderFound)) (c receiverFound)),
   .mul sameRecord (notE (n act)),
   .mul sameWord (sub (n firstLimb) (k 0)),
   .mul (c firstLimb) (sub (n midLimb) (k 1)),
   .mul (c midLimb) (sub (n topLimb) (k 1)),
   .mul (.mul (c sender) (c topLimb)) (sub (n receiver) (k 1)),
   .mul (.mul (c receiver) (c topLimb)) (sub (n amount) (k 1)),
   .mul (.mul (.add (c sender) (c receiver)) (c topLimb)) (sub (n firstLimb) (k 1)),
   .mul (.mul (header false) (n act)) (sub (words true) (n sender)),
   .mul (.mul (header false) (words true)) (sub (n firstLimb) (k 1)),
   .mul (.mul (header false) (words true)) (n record),
   .mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n sender) (k 1)),
   .mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n firstLimb) (k 1)),
   .mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n record) (.add (c record) (k 1))),
   .mul (.mul adjacent (header true)) (sub (n tau) (.add (c tau) (k 1))),
   .mul (.mul adjacent (words true)) (sub (n tau) (c tau)),
   .mul (.mul adjacent (words true)) (sub (n shards) (c shards))] ++
  [sender,receiver,amount,lo,mid,hi].map (fun x=>.mul sameWord (sub (n x) (c x))) ++
  [record,senderFound,senderIndex,receiverFound,receiverIndex].map
    (fun x=>.mul sameRecord (sub (n x) (c x)))

def interactions (recordBus requestBus resultBus writeBus parameterBus : Nat) : List Interaction:=
  [ {bus:=recordBus,send:=false,mult:=[words false],msg:=[c tau,c record,offset,c byte0]},
    {bus:=recordBus,send:=false,mult:=[words false],msg:=[c tau,c record,.add offset (k 1),c byte1]},
    {bus:=recordBus,send:=false,mult:=[sub (words false) (c topLimb)],msg:=[c tau,c record,.add offset (k 2),c byte2]},
    {bus:=requestBus,send:=true,mult:=[queryGate],msg:=[c tau,queryOrdinal,c lo,c mid,c hi]},
    {bus:=resultBus,send:=false,mult:=[queryGate],
      msg:=[c tau,queryOrdinal,selected senderFound receiverFound,selected senderIndex receiverIndex]},
    {bus:=writeBus,send:=true,mult:=[c writeGate],msg:=[c tau,link,c record,c lo,c big]},
    {bus:=parameterBus,send:=false,mult:=[header false],msg:=[c tau,c shards]} ]

def table (recordBus requestBus resultBus writeBus parameterBus : Nat) : Air.Table:=
  {width:=width,constraints:=constraints,interactions:=interactions recordBus requestBus resultBus writeBus parameterBus,maxLog:=22}

set_option maxRecDepth 32768 in
theorem standalone_wf : (table 0 1 2 3 4).wf ⟨[table 0 1 2 3 4],5,0⟩ 8=true := by decide +kernel

theorem measured_shape : shapeOf 2 (table 0 1 2 3 4)=⟨23,4,7,4,22⟩ := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorRecordTable
