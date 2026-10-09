import ZkFormal.Size.Model
import ZkFormal.V2.G.Defs
import ZkFormal.Near.Air
import ZkFormal.NearV3.BudgetUps
import ZkFormal.NearV3.Sched.Budget
import ZkFormal.Chacha.Table
import ZkFormal.Chacha.Rng.Table
import ZkFormal.Chacha.Shuffle.Table

namespace ZkFormal.Size.V3

open ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Size

def sh (w aux quot fin maxLog : Nat) : TShape := ⟨w, aux, quot, fin, maxLog⟩

/-! ## Table shapes (`w, aux, quot, fin, maxLog`) per `auxGroup` -/

/-- One SHA-256 table (v1 L5, `Sha.Table.table`): real table. -/
def shaT : Air.Table := Sha.Table.table Near.B_BYTES Near.B_DIGEST

/-- Trie after M7e root binding (`trieTablesU`: nodeV3 with `UPB` delta, headV3,
valV3, walkV3, uniqV3, upsV3). Root binding and full-range memory carries make upsV3 width 200;
`weqTrieU 1 = 1215`, `weqTrieU 3 = 1095`. `V3Eval.trie_shapes_check` checks
all six transcribed shapes against the integrated tables. -/
def trieS : Nat → List TShape
  | 1 => [sh 186 21 4 21 22, sh 73 8 3 8 11, sh 15 7 3 7 22, sh 56 6 3 6 21, sh 53 2 4 2 22, sh 200 15 3 15 22]
  | 2 => [sh 186 11 6 11 22, sh 73 4 5 4 11, sh 15 4 5 4 22, sh 56 4 5 4 21, sh 53 2 4 2 22, sh 200 8 5 8 22]
  | _ => [sh 186 8 7 8 22, sh 73 4 7 4 11, sh 15 3 7 3 22, sh 56 2 7 2 21, sh 53 2 4 2 22, sh 200 6 7 6 22]

/-- ChaCha (in tree, lane `v3-chacha`): `chachaV3`, `genV3`, `shufV3` (real tables). -/
def chachaT : List Air.Table :=
  [Chacha.Table.table 1, Chacha.Rng.Table.table 1 2, Chacha.Shuffle.Table.table 3 4 5 2 6]

/-- Scheduler, lane `v3-sched` head `f9bbf2f5` after cuts B, D and the source map
(`schV3, ssdV3, sprV3, smmV3, scpV3`; kernel-checked there `weqSched 1 = 781`, `3 = 709`). -/
def schedS : Nat → List TShape
  | 1 => [sh 91 16 3 16 22, sh 119 10 3 10 22, sh 64 11 3 11 22, sh 18 4 3 4 22, sh 33 1 3 1 22]
  | 2 => [sh 91 8 5 8 22, sh 119 6 5 6 22, sh 64 6 5 6 22, sh 18 3 5 3 22, sh 33 1 3 1 22]
  | _ => [sh 91 6 7 6 22, sh 119 4 7 4 22, sh 64 4 7 4 22, sh 18 2 7 2 22, sh 33 1 3 1 22]

/-- Receipt side, lane `v3-rcpt` head `fad713e5` (`rcptV3, acctV3, akeyV3, bndV3, srcpV3, sizeV3`;
kernel-checked there `weqRcpt 1 = 867`, `3 = 795`). -/
def rcptS : Nat → List TShape
  | 1 => [sh 263 18 3 18 22, sh 16 13 3 13 17, sh 7 3 3 3 16, sh 6 3 3 3 13, sh 56 5 3 5 20, sh 31 1 3 1 2]
  | 2 => [sh 263 9 5 9 22, sh 16 7 5 7 17, sh 7 2 5 2 16, sh 6 2 5 2 13, sh 56 3 5 3 20, sh 31 1 3 1 2]
  | _ => [sh 263 6 7 6 22, sh 16 5 7 5 17, sh 7 2 5 2 16, sh 6 2 5 2 13, sh 56 2 7 2 20, sh 31 1 3 1 2]

/-- `mrk`, `sort`: v1 tables (real) with the v3 heights (`maxLog` 19, 18; V3-D0-DESIGN §3.1). -/
def v1S (g : Nat) : List TShape :=
  [{ shapeOf g Near.Mrk.table with maxLog := 19 }, { shapeOf g Near.Sort.table with maxLog := 18 }]

/-- **The synthetic v3 AIR** (23 tables): one SHA, trie 6, ChaCha 3, scheduler 5, receipt 6,
`mrk`, `sort`. -/
def v3S (g : Nat) : List TShape :=
  [shapeOf g shaT] ++ trieS g ++ chachaT.map (shapeOf g) ++ schedS g ++ rcptS g ++ v1S g

def weqS (ts : List TShape) : Nat := (ts.map TShape.weq).sum

end ZkFormal.Size.V3
