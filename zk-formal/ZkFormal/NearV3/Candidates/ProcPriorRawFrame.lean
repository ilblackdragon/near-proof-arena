import ZkFormal.NearV3.Candidates.ProcPriorMemoryTable

/-! Candidate raw-byte framing only. Record-byte limb assembly and lookup
joins are deliberately a separate unfinished extension; this is not the full
prior-state parser. No active table is changed. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorRawFrame
open ZkFormal.Air ZkFormal.Chacha.Table.E ZkFormal.Size
open ZkFormal.Chacha.Table (boolC)
def act : Nat:=0
def tau : Nat:=1
def vid : Nat:=2
def present : Nat:=3
def pos : Nat:=4
def byte : Nat:=5
def hdr : Nat:=6
def rec : Nat:=7
def hash : Nat:=8
def offset : Nat:=9
def record : Nat:=10
def count : Nat:=11
def phaseEnd : Nat:=12
def endInv : Nat:=13
def recordEnd : Nat:=14
def recordInv : Nat:=15
def empty : Nat:=16
def emptyInv : Nat:=17
def first : Nat:=18
def acc : Nat:=19
def byteGate : Nat:=20
def firstInv : Nat:=21
def lengthGate : Nat:=22
def width : Nat:=23

def notE (x : Expr) : Expr:=sub (k 1) x
def mul3 (a b c : Expr) : Expr:=.mul (.mul a b) c
def endAt : Expr:=.add (.mul (k 4) (c hdr)) (.add (.mul (k 23) (c rec)) (.mul (k 31) (c hash)))
def done : Expr:=.mul (c hash) (c phaseEnd)
def nextWithin : Expr:=sub (c act) done

def isZero (g x : Expr) (iv flag : Nat) : List Expr:=
  [.mul g (sub (.mul x (c iv)) (notE (c flag))),.mul g (.mul x (c flag)),
   .mul (notE g) (c flag)]

def constraints : List Expr:=
  [act,present,hdr,rec,hash,phaseEnd,recordEnd,empty,first,byteGate,lengthGate].map boolC ++
  [sub (c act) (.add (c hdr) (.add (c rec) (c hash))),
   .mul .isLast (c act),
   mul3 .isTransition (notE (c act)) (n act),
   .mul .isFirst (sub (c act) (c first)),
   .mul .isFirst (c tau),
   .mul (c first) (c pos),
   .mul (c first) (sub (c acc) (c count)),
   .mul (c first) (c byte),
   .mul (c first) (c record),
   sub (c byteGate) (.mul (c act) (c present)),
   sub (c lengthGate) (.mul (c first) (c present)),
   .mul (notE (c present)) (c byte),
   -- Original, arbitrary record count is retained; missing prior state is empty.
   .mul (notE (c present)) (c count),
   .mul nextWithin (notE (n act)),
   .mul nextWithin (sub (n pos) (.add (c pos) (k 1))),
   mul3 done (n act) (notE (n first)),
   mul3 done (n act) (sub (n tau) (.add (c tau) (k 1))),
   mul3 (c act) (notE (c phaseEnd)) (sub (n offset) (.add (c offset) (k 1))),
   .mul (c phaseEnd) (n offset),
   -- Header tag, three count bytes, then a zero high byte.
   .mul (c first) (sub (n acc) (c count)),
   mul3 (c hdr) (notE (.add (c first) (c phaseEnd)))
     (sub (c acc) (.add (c byte) (.mul (k 256) (n acc)))),
   mul3 (c hdr) (c phaseEnd) (c acc),
   mul3 (c hdr) (c phaseEnd) (c byte),
   mul3 (c hdr) (c phaseEnd) (sub (n rec) (notE (c empty))),
   mul3 (c hdr) (c phaseEnd) (sub (n hash) (c empty)),
   mul3 (c hdr) (c phaseEnd) (n record),
   mul3 (c rec) (c phaseEnd) (sub (n rec) (notE (c recordEnd))),
   mul3 (c rec) (c phaseEnd) (sub (n hash) (c recordEnd)),
   mul3 (c rec) (c phaseEnd) (sub (n record) (.add (c record) (k 1))),
   .mul (sub nextWithin (.mul (c rec) (c phaseEnd))) (sub (n record) (c record))] ++
  [tau,vid,present,count].map (fun x=>.mul nextWithin (sub (n x) (c x))) ++
  [hdr,rec,hash].map (fun x=>mul3 (c act) (notE (c phaseEnd)) (sub (n x) (c x))) ++
  isZero (c act) (sub (c offset) endAt) endInv phaseEnd ++
  isZero (c rec) (sub (.add (c record) (k 1)) (c count)) recordInv recordEnd ++
  isZero (c act) (c count) emptyInv empty ++
  isZero (c hdr) (c offset) firstInv first

/-- The five inventories are original-value presence, exact value length,
original bytes, prior sanity bytes, and unchanged original record bytes. -/
def interactions (presenceBus lengthBus bytesBus sanityBus recordBus : Nat) : List Interaction:=
  [{bus:=presenceBus,send:=false,mult:=[c first],msg:=[c tau,c present,c vid]},
   {bus:=lengthBus,send:=false,mult:=[c lengthGate],msg:=[c vid,.add (k 37) (.mul (k 24) (c count))]},
   {bus:=bytesBus,send:=true,mult:=[c byteGate],msg:=[c vid,c pos,c byte]},
   {bus:=sanityBus,send:=true,mult:=[c hash],msg:=[c tau,c offset,c byte]},
   {bus:=recordBus,send:=true,mult:=[c rec],msg:=[c tau,c record,c offset,c byte]}]

def table (presenceBus lengthBus bytesBus sanityBus recordBus : Nat) : Air.Table:=
  {width:=width,constraints:=constraints,interactions:=interactions presenceBus lengthBus bytesBus sanityBus recordBus,maxLog:=22}

set_option maxRecDepth 32768 in
theorem standalone_wf : (table 0 1 2 3 4).wf ⟨[table 0 1 2 3 4],5,0⟩ 8=true := by decide +kernel

theorem measured_shape : shapeOf 2 (table 0 1 2 3 4)=⟨23,3,5,3,22⟩ := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorRawFrame
