import ZkFormal.NearV3.Sched.Tables.Mem
import ZkFormal.Size.V3Synth

/-! Isolated prior-allowance memory candidate. The bus IDs are parameters;
this table is not installed in the active or admitted family. Raw writes and
canonical queries must be bound to the authenticated parser/post codec. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryTable
open ZkFormal.Air ZkFormal.Chacha.Table.E ZkFormal.Size
open ZkFormal.Chacha.Table (boolC)

def act : Nat := 0
def tau : Nat := 1
def link : Nat := 2
def stamp : Nat := 3
def query : Nat := 4
def lo : Nat := 5
def hi : Nat := 6
def beforeLo : Nat := 7
def beforeHi : Nat := 8
def same : Nat := 9
def inverse : Nat := 10
def width : Nat := 11

def notE (e : Expr) : Expr := sub (k 1) e
def addr : Expr := .add (.mul (k 4096) (c tau)) (c link)
def nextAddr : Expr := .add (.mul (k 4096) (n tau)) (n link)
def delta : Expr := sub nextAddr addr
def adjacent : Expr := .mul (c act) (n act)

def constraints : List Expr :=
  [act,query,hi,beforeHi,same].map boolC ++
  [ .mul .isLast (c act),
    .mul (.mul .isTransition (notE (c act))) (n act),
    .mul .isFirst (c beforeLo),
    .mul .isFirst (c beforeHi),
    .mul adjacent (sub (.mul delta (c inverse)) (notE (c same))),
    .mul adjacent (.mul delta (c same)),
    .mul adjacent (sub (n beforeLo) (.mul (c same) (c lo))),
    .mul adjacent (sub (n beforeHi) (.mul (c same) (c hi))),
    .mul (.mul (c act) (c query)) (sub (c lo) (c beforeLo)),
    .mul (.mul (c act) (c query)) (sub (c hi) (c beforeHi)),
    -- Queries end their link group; their ordinal need not be trusted.
    .mul adjacent (.mul (c query) (c same)) ]

def interactions (writeBus readBus cmpBus : Nat) : List Interaction :=
  [ {bus:=writeBus,mult:=[.mul (c act) (notE (c query))],send:=false,
      msg:=[c tau,c link,c stamp,c lo,c hi]},
    {bus:=readBus,mult:=[.mul (c act) (c query)],send:=true,
      msg:=[c tau,c link,c lo,c hi]},
    {bus:=cmpBus,mult:=[adjacent],send:=true,msg:=[nextAddr,addr,k 1]},
    {bus:=cmpBus,mult:=[.mul adjacent (.mul (c same) (notE (n query)))],send:=true,
      msg:=[n stamp,.add (c stamp) (k 1),k 1]} ]

def table (writeBus readBus cmpBus : Nat) : Air.Table :=
  {width:=width,constraints:=constraints,interactions:=interactions writeBus readBus cmpBus,maxLog:=22}

set_option maxRecDepth 32768 in
theorem standalone_wf : (table 0 1 2).wf ⟨[table 0 1 2],3,0⟩ 8=true := by decide +kernel

theorem measured_shape : shapeOf 2 (table 0 1 2)=⟨11,3,7,3,22⟩ := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorMemoryTable
