import ZkFormal.NearV3.Assembly.WitnessStore
import ZkFormal.NearV3.Render.Ups.TreeViewStore

/-! Executable single-instance view allocation. Stable store dedup makes its
encoded byte cost nonexpanding even when occurrence records repeat shared bytes.
This module does not assert AIR traffic, a complete transition witness, or the
value-id capacity premise from native acceptance. -/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- Only store views are populated; head/source/execution assembly is separate. -/
def treeStoreViews (tau : Nat) (t : PTrie) : ExtV3 :=
  { nodes := seedNodesT tau 0 0 0 t
    values := seedValuesFrom 0 (valsOf t)
    heads := []
    receipts := []
    dictionary := [] }

theorem treeStoreViews_rawStore (tau : Nat) (t : PTrie) (hw : t.wf = true)
    (hn : isNode t = true) (hc : (valsOf t).length ≤ ZkFormal.Algebra.P) :
    (treeStoreViews tau t).rawStore tau = (occs t).map nodeEnc ++ valsOf t :=
  seedViews_modular_store tau t hw hn hc

theorem treeStoreViews_store (tau : Nat) (t : PTrie) (hw : t.wf = true)
    (hn : isNode t = true) (hc : (valsOf t).length ≤ ZkFormal.Algebra.P) :
    (treeStoreViews tau t).store tau = normalStore t := by
  simp only [ExtV3.store, treeStoreViews_rawStore tau t hw hn hc, normalStore]

/-- Actual native partial-trie bytes determine a nonexpanding serialized store.
No encoded-size bound is assumed as a conclusion or hidden in the view type. -/
theorem treeStoreViews_native_cost (tau : Nat) (ws : List Bytes) (root : Bytes)
    (keys : List (List Nat)) (hr : root.length = 32)
    (hn : isNode (partialTrie ws root keys) = true)
    (hc : (valsOf (partialTrie ws root keys)).length ≤ ZkFormal.Algebra.P) :
    storeCost ((treeStoreViews tau (partialTrie ws root keys)).store tau) ≤ storeCost ws := by
  have hb := built_spec ws trieFuel root keys hr
  have hw : (partialTrie ws root keys).wf = true := hb.2.1
  rw [treeStoreViews_store tau _ hw hn hc]
  exact normalStore_cost hb.2.2.1

end ZkFormal.NearV3.Assembly
