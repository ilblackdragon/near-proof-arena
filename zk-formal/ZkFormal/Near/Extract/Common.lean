import ZkFormal.Near.Air

/-!
# ZkFormal.Near.Extract.Common — table traffic

Soundness (`ExtractStmt`) is split into

1. **per-table views** (`Extract/<Table>View.lean`): from the local
   constraints of one table, its rows decompose into a *view* (the semantic
   content, values as naturals `< p`), and the table's traffic on every bus is
   exactly the message list the view determines (`TableTraffic`);
2. **linking** (`Extract/Link*.lean`): from the views of all tables and bus
   balance, the relational spec `Good`.

Messages are lists of naturals; the trace sees them through `Fp.ofNat`.
Message layouts per bus: NEAR-AIR.md §2.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra

/-- A bus message as naturals. -/
abbrev Msg := List Nat

def Msg.toFp (m : Msg) : List Fp := m.map Fp.ofNat

/-- The messages a table sends / receives on each bus (with multiplicity one each). -/
structure Traffic where
  sends : Nat → List Msg
  recvs : Nat → List Msg

/-- Table `t` of `tr` (interactions `is`) has exactly the traffic `tf`. -/
def TableTraffic (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) (tf : Traffic) :
    Prop :=
  ∀ b m, tableBusCount is tr t pub b true m = ((tf.sends b).map Msg.toFp).count m ∧
    tableBusCount is tr t pub b false m = ((tf.recvs b).map Msg.toFp).count m

/-- Local legality of table `t`: height within `[2, 2^maxLog]`, every
constraint on every row, every multiplicity bit boolean (what `Holds` gives
about one table). -/
structure TableLocal (T : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop where
  log_ge : 1 ≤ tr.log t
  log_le : tr.log t ≤ T.maxLog
  constr : ∀ r, r < tr.height t → ∀ e ∈ T.constraints, e.eval tr t r pub = 0
  bits : ∀ r, r < tr.height t → ∀ i ∈ T.interactions, ∀ b ∈ i.mult,
    b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1

/-- The public inputs as naturals (`< 256` for `publicOf`). -/
def pubNat (pub : List Fp) (i : Nat) : Nat := (pub.getD i 0).toNat

/-! ## Byte-message helpers -/

/-- `[(Id, i, bytes[i]) | i < |bytes|]` with positions from `off`. -/
def emitAt (id off : Nat) (bytes : List Nat) : List Msg :=
  (List.range bytes.length).map fun i => [id, off + i, bytes.getD i 0]

/-- Digest message `(Id, len, d[32])`. -/
def digMsg (id len : Nat) (d : List Nat) : Msg := [id, len] ++ d

/-- `u32` of a small value as raw bytes `[x, 0, 0, 0]`. -/
def u32r (x : Nat) : List Nat := [x, 0, 0, 0]

end ZkFormal.Near
