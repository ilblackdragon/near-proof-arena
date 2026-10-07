import ZkFormal.NearV3.Qv.Candidates.ValueTable
import ZkFormal.NearV3.Qv.ByteBuffers
import ZkFormal.Algebra.Fp

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

structure Config where
  vid : Nat
  tau : Nat
  users : Nat
  mode : Nat
  length : Nat
  count : Nat := 0

/-- Natural row encoding; phase0=header,1=shard,2=first,3=next,4=raw. -/
def row (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) : List Nat :=
  let last := decide (cfg.length=0 ∨ pos+1=cfg.length)
  let zero := decide (cfg.length=0)
  [1,(decide (pos=0)).toNat,last.toNat,cfg.vid,cfg.length,pos,byte,cfg.users,cfg.tau,entry,
   cfg.count,zero.toNat,(!zero).toNat,(!last).toNat,
   (decide (cfg.mode=0)).toNat,(decide (cfg.mode=1)).toNat,(decide (cfg.mode=2)).toNat,
   (decide (phase=0)).toNat,(decide (phase=1)).toNat,
   (decide (phase=2)).toNat,(decide (phase=3)).toNat] ++
  (List.range 8).map (fun i => (decide (phase≠4 ∧ subpos=i)).toNat) ++
  (List.range 8).map (fun i => (regs.getD i 0).toNat)

theorem row_width (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).length = ValueTable.width := by
  simp [row,ValueTable.width]

def wordRows (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes) : List (List Nat) :=
  bytes.zipIdx.map fun (b,i) => row cfg (offset+i) b.toNat phase i entry regs

def emptyRows (vid tau users : Nat) (index : Bytes) : List (List Nat) :=
  let cfg : Config := ⟨vid,tau,users,0,16,0⟩
  wordRows cfg 0 2 0 index index ++ wordRows cfg 8 3 0 index index

def bufferRows (vid tau users : Nat) (entries : List ByteBuffer) : List (List Nat) :=
  let cfg : Config := ⟨vid,tau,users,1,4+24*entries.length,entries.length⟩
  let head := u32 entries.length
  wordRows cfg 0 0 0 head head ++
  entries.zipIdx.flatMap (fun (e,i) =>
    wordRows cfg (4+24*i) 1 i e.shard e.index ++
    wordRows cfg (12+24*i) 2 i e.index e.index ++
    wordRows cfg (20+24*i) 3 i e.index e.index)

def rawRows (vid tau users : Nat) (bytes : Bytes) : List (List Nat) :=
  let cfg : Config := ⟨vid,tau,users,2,bytes.length,0⟩
  if bytes.isEmpty then [row cfg 0 0 4 0 0 []]
  else bytes.zipIdx.map fun (b,i) => row cfg i b.toNat 4 0 0 []

/-- Diagnostic integer evaluation. This checks examples of local polynomials
and multiplicity bits; it is not a field-level soundness/completeness theorem. -/
def checkRows (rows : List (List Nat)) (log : Nat) : Bool :=
  let height := 2^log
  rows.length ≤ height && (List.range height).all fun r =>
    let env : ZkFormal.Air.Env Int :=
      { ofNat := Int.ofNat, add := (·+·), mul := (·*·), neg := (- ·),
        col := fun c next => Int.ofNat ((rows.getD (if next then (r+1)%height else r) []).getD c 0),
        pub := fun _ => 0, isFirst := if r=0 then 1 else 0,
        isLast := if r+1=height then 1 else 0, isTransition := if r+1=height then 0 else 1 }
    ValueTable.table.allConstraints.all fun e => decide (e.evalWith env=0)

/-- The same diagnostic evaluated in the actual protocol field. -/
def checkFieldRows (rows : List (List Nat)) (log : Nat) : Bool :=
  let trace : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
    { log := fun _ => log,
      cell := fun _ r c => ZkFormal.Algebra.Fp.ofNat ((rows.getD r []).getD c 0) }
  rows.length ≤ 2^log && (List.range (2^log)).all fun r =>
    ValueTable.table.allConstraints.all fun e => decide (e.eval trace 0 r []=0)

end ZkFormal.NearV3.Qv.Candidates.ValueGen
