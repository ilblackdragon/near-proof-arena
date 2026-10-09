import ZkFormal.NearV3.Candidates.CurrentFamily
import ZkFormal.NearV3.Candidates.ShaCarryPairs

/-! Executable feasibility study of exact-expression pair substitution.
These are candidate definitions, not admitted tables or honest allocation proofs. -/
namespace ZkFormal.NearV3.Candidates.PairPackingStudy
open ZkFormal.Air

def before (pairs : List Nat) (i : Nat) : Nat := pairs.countP (fun j => j<i)
def column (pairs : List Nat) (i : Nat) (nx : Bool) : Expr :=
  match pairs.find? (fun p => i=p || i=p+1) with
  | none => .col (i-before pairs i) nx
  | some p =>
    let x:=Expr.col (p-before pairs p) nx
    if i=p then ShaCarryPairs.low x else ShaCarryPairs.high x

def expression (pairs : List Nat) : Expr → Expr
  | .col i nx => column pairs i nx
  | .add a b => .add (expression pairs a) (expression pairs b)
  | .mul a b => .mul (expression pairs a) (expression pairs b)
  | .neg a => .neg (expression pairs a)
  | e => e

def table (pairs : List Nat) (t : Air.Table) : Air.Table :=
  {t with
    width:=t.width - pairs.length,
    constraints:=t.constraints.map (expression pairs),
    interactions:=t.interactions.map (fun i => {i with
      mult:=i.mult.map (expression pairs),
      msg:=i.msg.map (expression pairs)})}

def pairsAt (start count : Nat) : List Nat := (List.range count).map (fun j => start+2*j)
def rngPairs := pairsAt 17 2 ++ pairsAt 23 7 ++ pairsAt 51 38 ++ pairsAt 130 3
def chachaPairs := pairsAt 32 64
def receiptPairs := pairsAt 138 33
def nodePairs := pairsAt 29 12 ++ pairsAt 54 8
def shufflePairs := pairsAt 30 21

def shaPairs : List Nat :=
  ((List.range 4).flatMap fun j => pairsAt (32*j + if j%2=0 then 0 else 16) 8) ++
  ((List.range 4).flatMap fun j => pairsAt (128+32*j) 9) ++
  ((List.range 4).flatMap fun j => pairsAt (256+32*j) 9)

def cases : List (String × Air.Table) :=
  [("rng",table rngPairs CurrentFamily.chachaTables[1]!),
   ("chacha",table chachaPairs CurrentFamily.chachaTables[0]!),
   ("receipt",table receiptPairs CurrentFamily.receiptTables[0]!),
   ("node",table nodePairs CurrentFamily.trieTables[0]!),
   ("shuffle",table shufflePairs CurrentFamily.chachaTables[2]!),
   ("sha-partial",table shaPairs (ShaCarryPairs.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST))]
end ZkFormal.NearV3.Candidates.PairPackingStudy
