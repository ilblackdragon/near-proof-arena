# `near-transfer-receipt-v1-zk.draft.json`: superseded by v1-6, never signed

This draft (`chl_bdbfc808…`) was the statement the closed NEAR STARK certificate
(`examples/np-udr-stark`) was first checked against. It pins trusted tree
`sha256:35fbd260…` (formal-core with `ArenaCore.SHA256Fast`; reproduced by
commit `e4088761`) and `allowed_packages` at `e4088761`, but it predates the
R-L7-5 checker (`checker_image` `b6391b38…`) and carries v1-3's baseline.

Governance did not sign it. Its content was folded into
**`near-transfer-receipt-v1-6`** (`chl_7c0456cb2d1a36f8601863ac206cfcc9`,
supersedes v1-5): same trusted tree and `allowed_packages`, the fixed checker
`66b014d4…`, and a baseline re-measured with judge-secret sampling
(docs/PROTOCOL_UPGRADES.md §7.7). Kept for history; do not sign or register.
