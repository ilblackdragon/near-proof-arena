import NearSpecV3.Examples.RealCaseD3StoreK0
import NearSpecV3.Examples.RealCaseD3StoreK1
import NearSpecV3.Examples.RealCaseD3StoreK2
import NearSpecV3.Examples.RealCaseD3StoreK3

/-!
# Kernel non-vacuity of `RelD3` and of the `allFeatures` successor relation (wider cases)

`decide +kernel` evaluates the whole checker (witness decoding, trie reveal, receipt proofs,
WASM preparation, instantiation and execution, storage, roots, Reed–Solomon) on real
chunks, and the bridges in `RealCaseD3Bridge` transport the Bool verdict to the `Prop`.
No `native_decide`.

* `d3c9/d3/02-h10008-s1` — honest D3-only case; contracts run: d3tiny; receipts: incoming(refund):[Transfer] => ok; incoming:[FunctionCall] => ok; incoming(refund):[Transfer] => ok; nearcore: "ok"
* `d3c9/mutants/02-h10008-s1-w.main_post_root` — mutant `w.main_post_root`; contracts run: —; receipts: —; nearcore: "validate: InvalidChunkStateWitness('Post state root F1Sby4ovW7FxVozHVL"
-/
