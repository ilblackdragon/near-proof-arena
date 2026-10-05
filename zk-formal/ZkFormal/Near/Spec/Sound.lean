import ZkFormal.Near.Spec.SoundRun
import ZkFormal.Near.Statements

/-!
# ZkFormal.Near.Spec.Sound — `good_sound : GoodSoundStmt`

The relational spec implies `NearRelation` for the witness it denotes:

* `DomainStatic` — claim-level and receipt facts are fields of `Good`; the
  trie is `wf` (`treeOf_wf`) and its revealed size is at most `revealedOf`
  (`revealed_le`);
* `runBatch` ends in `accAt n` (`runBatch_eq`), whose outputs are the claim's.
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1

theorem good_sound : GoodSoundStmt := by
  intro c e hwf hg
  obtain ⟨d, hd0, hd⟩ := hg.shape.depth
  refine ⟨⟨hwf, hg.pv, hg.chain, hg.len, hg.n_pos, hg.n_le, hg.gas_limit, hg.inSlice, hg.nodup,
    ?_, ?_⟩, hg.rcCommit, hg.preRoot, ?_⟩
  · exact Sound.treeOf_wf hg.shape d hd0 hd hg.nodes_wf hg.vals_len e.ns.length 0 .refl
      (by rw [hd0, Nat.zero_add])
  · exact Nat.le_trans (Sound.revealed_le hg.shape d hd hg.nodes_wf hg.vals_len) hg.size
  · show (runBatch c.ctx (trieOf e.ns e.vals0) e.rs).map Outputs.ofAcc = _
    rw [Sound.runBatch_eq hg]
    simp only [Option.map_some, Option.some.injEq, Outputs.ofAcc, Outputs.ofClaim,
      Sound.accAt]
    have hgas : e.rs.length * Params.G = c.gasBurntTotal := by rw [hg.gas_total, hg.len]
    rw [hg.postRoot, hgas, hg.tokens]
    have h1 := hg.outRoot
    have h2 := hg.refundCount
    have h3 := hg.rfCommit
    simp only [Ext.outcomes, Ext.refunds] at h1 h2 h3
    rw [h1, h2, h3]

end ZkFormal.Near
