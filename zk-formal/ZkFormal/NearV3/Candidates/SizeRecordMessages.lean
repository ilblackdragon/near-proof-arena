import ZkFormal.NearV3.Candidates.NodeRecordCount
import ZkFormal.NearV3.Candidates.ValueRecordCount

namespace ZkFormal.NearV3.Candidates.SizeRecordMessages
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open Rcpt.Candidates.SizeCount
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

def nodeInteraction : Interaction := withCount (Dsl.c nodeCount)
  (Dsl.send B_SIZE (Dsl.c NodeV3.sumr) [Dsl.k 0,Dsl.c NodeV3.sz])
def valueInteraction : Interaction := withCount (Dsl.c valCount)
  (Dsl.send B_SIZE (Dsl.c ValV3.sumr) [Dsl.k 1,Dsl.c ValV3.sz])

theorem node_member : nodeInteraction ∈ nodeTable.interactions := by
  apply List.mem_map.mpr
  exact ⟨_, by simp [NodeV3.tableU, NodeV3.table, NodeV3.interactions], rfl⟩
theorem value_member : valueInteraction ∈ valTable.interactions := by
  apply List.mem_map.mpr
  exact ⟨_, by simp [ValV3.table, ValV3.interactions], rfl⟩

/-- The actual node SUM interaction carries payload bytes and stored record count
as separate authenticated fields. Duplicate records contribute to neither. -/
theorem node_message (es : List NodeS3) (t : Nat) (pub : List Fp) :
    nodeInteraction.msgVal (TrieCountHeight.node es pub) t (NodeGen3.R es) pub =
      [Fp.ofNat 0,
       Fp.ofNat (((es.filter fun e=>!e.dup).map fun e=>(e.v.ser false).length).sum),
       Fp.ofNat (es.filter fun e=>!e.dup).length] := by
  change [Fp.ofNat 0,(TrieCountHeight.node es pub).cell t (NodeGen3.R es) NodeV3.sz,
    (TrieCountHeight.node es pub).cell t (NodeGen3.R es) nodeCount]=_
  rw [NodeRecordCount.node_counter]
  have hs : (TrieCountHeight.node es pub).cell t (NodeGen3.R es) NodeV3.sz=
      Fp.ofNat (NodeGen3.total es) := by
    change (if NodeV3.sz=nodeCount then CountLift.tally (TrieHeight.node es) nodeIncrement t (NodeGen3.R es) pub else Fp.ofNat (NodeGen3.cell es (2^22) (NodeGen3.R es) NodeV3.sz))=_
    rw [if_neg (by decide),NodeGen3.cell_sum]
    rfl
  rw [hs,NodeGen3.total_eq]

/-- Empty value records still contribute one record header, even though their
payload length contributes zero. -/
theorem value_message (es : List ValE) (ok : ValOk es) (t : Nat) (pub : List Fp) :
    valueInteraction.msgVal (TrieCountHeight.value es pub) t (ValGen.R es) pub =
      [Fp.ofNat 1,
       Fp.ofNat (((es.filter fun e=>!e.vz && !e.dup).map ValE.len).sum),
       Fp.ofNat (es.filter fun e=>!e.dup).length] := by
  change [Fp.ofNat 1,(TrieCountHeight.value es pub).cell t (ValGen.R es) ValV3.sz,
    (TrieCountHeight.value es pub).cell t (ValGen.R es) valCount]=_
  rw [ValueRecordCount.value_counter es ok]
  have hs : (TrieCountHeight.value es pub).cell t (ValGen.R es) ValV3.sz=
      Fp.ofNat (ValGen.szAt es (ValGen.R es)) := by
    change (if ValV3.sz=valCount then CountLift.tally (TrieHeight.value es) valIncrement t (ValGen.R es) pub else Fp.ofNat (ValGen.cell es (2^22) (ValGen.R es) ValV3.sz))=_
    rw [if_neg (by decide)]
    rfl
  rw [hs,ValGen.szAt_R ok]

theorem node_multiplicity (es : List NodeS3) (t : Nat) (pub : List Fp) :
    nodeInteraction.multNat (TrieCountHeight.node es pub) t (NodeGen3.R es) pub=1 := by
  have h : (TrieCountHeight.node es pub).cell t (NodeGen3.R es) NodeV3.sumr=1 := by
    change (if NodeV3.sumr=nodeCount then CountLift.tally (TrieHeight.node es) nodeIncrement t (NodeGen3.R es) pub else Fp.ofNat (NodeGen3.cell es (2^22) (NodeGen3.R es) NodeV3.sumr))=1
    rw [if_neg (by decide),NodeGen3.cell_sum]
    rfl
  change (if (TrieCountHeight.node es pub).cell t (NodeGen3.R es) NodeV3.sumr=1 then 1 else 0)+0=1
  rw [h]; decide

theorem value_multiplicity (es : List ValE) (t : Nat) (pub : List Fp) :
    valueInteraction.multNat (TrieCountHeight.value es pub) t (ValGen.R es) pub=1 := by
  have h : (TrieCountHeight.value es pub).cell t (ValGen.R es) ValV3.sumr=1 := by
    change (if ValV3.sumr=valCount then CountLift.tally (TrieHeight.value es) valIncrement t (ValGen.R es) pub else Fp.ofNat (ValGen.cell es (2^22) (ValGen.R es) ValV3.sumr))=1
    rw [if_neg (by decide)]
    simp [ValGen.cell,ValV3.sumr]
    rfl
  change (if (TrieCountHeight.value es pub).cell t (ValGen.R es) ValV3.sumr=1 then 1 else 0)+0=1
  rw [h]; decide
end ZkFormal.NearV3.Candidates.SizeRecordMessages
