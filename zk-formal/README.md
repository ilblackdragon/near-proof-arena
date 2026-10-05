# zk-formal (Lake package `ZkFormal`)

Lean development for the formally admitted STARK backend `np-udr-stark`
(`examples/np-udr-stark`). Design, formats and lane status are in
[`docs/zk-formal/`](../docs/zk-formal/DESIGN.md).

**The "zk" in the name is historical.** This development proves **succinct
validity**: soundness of the STARK verifier for the challenge's
`NearRelation` under `validity-classical-128`. It does **not** prove zero
knowledge. np-udr-stark has no blinding or hiding, its challenges are
`privacy: validity_only` with `FORMAL_ZK` not applicable, and formal-core has
no zero-knowledge predicate. The directory and module names are kept so that
pinned digests and paths stay stable.
