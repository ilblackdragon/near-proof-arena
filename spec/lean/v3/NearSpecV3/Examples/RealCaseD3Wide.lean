import NearSpecV3.Examples.RealCaseD3WideK0
import NearSpecV3.Examples.RealCaseD3WideK1
import NearSpecV3.Examples.RealCaseD3WideK2
import NearSpecV3.Examples.RealCaseD3WideK3
import NearSpecV3.Examples.RealCaseD3WideK4
import NearSpecV3.Examples.RealCaseD3WideK5
import NearSpecV3.Examples.RealCaseD3WideK6
import NearSpecV3.Examples.RealCaseD3WideK7

/-!
# Kernel non-vacuity of `RelD3` and of the `allFeatures` successor relation (wider cases)

`decide +kernel` evaluates the whole checker (witness decoding, trie reveal, receipt proofs,
WASM preparation, instantiation and execution, storage, roots, Reed–Solomon) on real
chunks, and the bridges in `RealCaseD3Bridge` transport the Bool verdict to the `Prop`.
No `native_decide`.

* `d3c10/d3/00-h10050-s1` — honest D3-only case; contracts run: d3rich; receipts: incoming:[FunctionCall] => ok; incoming:[FunctionCall] => ok; nearcore: "ok"
* `d3c10/mutants/00-h10050-s1-w.main_post_root` — mutant `w.main_post_root`; contracts run: —; receipts: —; nearcore: "validate: InvalidChunkStateWitness('Post state root 4maVfPD8cqrYenBc6z"
* `docs/evidence/lean-chunk-completion/resharding-fixtures-2/cases/seed37-00-h10085-s7` — honest split case; shape split.right; implicit transitions: apply_old_chunk, resharding; nearcore: "ok"
* `docs/evidence/lean-chunk-completion/resharding-fixtures-2/cases/seed37-00-h10085-s7-w.split_child_post_root` — mutant `w.split_child_post_root`; shape split.right; implicit transitions: —; nearcore: "validate: InvalidChunkStateWitness('Post state root 3X6xv6q1N6cMHGEtpi"
-/
