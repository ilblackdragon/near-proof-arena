import NearSpecV3.Examples.RealCaseD3SplitK0
import NearSpecV3.Examples.RealCaseD3SplitK1
import NearSpecV3.Examples.RealCaseD3SplitK2
import NearSpecV3.Examples.RealCaseD3SplitK3

/-!
# Kernel non-vacuity of `RelD3` and of the `allFeatures` successor relation (wider cases)

`decide +kernel` evaluates the whole checker (witness decoding, trie reveal, receipt proofs,
WASM preparation, instantiation and execution, storage, roots, Reed–Solomon) on real
chunks, and the bridges in `RealCaseD3Bridge` transport the Bool verdict to the `Prop`.
No `native_decide`.

* `docs/evidence/lean-chunk-completion/resharding-fixtures-2/cases/seed37-00-h10085-s7` — honest split case; shape split.right; implicit transitions: apply_old_chunk, resharding; nearcore: "ok"
* `docs/evidence/lean-chunk-completion/resharding-fixtures-2/cases/seed37-00-h10085-s7-w.split_child_post_root` — mutant `w.split_child_post_root`; shape split.right; implicit transitions: —; nearcore: "validate: InvalidChunkStateWitness('Post state root 3X6xv6q1N6cMHGEtpi"
-/
