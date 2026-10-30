"""UQ-010 item 6(c) changes to the near-chunk-v3 v3.1 draft (user decision 2026-10-30).

Applied by spec/tools/build_challenge_draft_v3_chunk_r.py (the item-11 builder of
challenges/drafts/near-chunk-v3-1.draft.json), so one v3.1 draft carries both lanes' changes:

* `claim_encoding.max_witness_bytes` = 75,497,501 = `ChallengeChunkV3.maxWitnessChunk` (the clear
  `near-arena-witness-v3` tag field 4 + 21, an 8 MiB state witness 4 + 8,388,608, and one 64 MiB
  `ContractCodeResponse`), the completeness-domain witness bound since the UQ-010 hand-over;
* the restrictions that no longer restrict `D3.RelD3` are dropped: `c.same_layout`, `c.no_split_gate`
  (the hand-over decides resharding), `e.secp` (SECP256K1 delegates verified since 2026-10-26); `w.size`
  keeps the 8 MiB state-witness bound and the code-response cap and drops the storage-proof clause;
  `e.g_alpha` applies to the legacy core only (the hand-over path decides over-`G_α` chunks);
* the matching `excludes` (`resharding`, `dynamic_resharding_split_search`) are dropped.

Evidence: docs/evidence/lean-chunk-completion/signed-completeness/README.md.
"""

MAX_WITNESS_BYTES = (4 + 21) + (4 + 8388608) + 67108864  # = 75,497,501
DROP_RESTRICTIONS = {"c.same_layout", "c.no_split_gate", "e.secp"}
DROP_EXCLUDES = {"resharding", "dynamic_resharding_split_search"}
RESTRICTION_TEXT = {
    "w.size": "state witness (near-arena-witness-v3 state_witness field) <= 8 MiB; the cold-fetched "
              "contract code fits one ContractCodeResponse (MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE "
              "= 64 MiB); the storage-proof limits are decided (legacy core below 4,000,000 bytes of "
              "values and code, the recorder engine above it, D3/Signed.lean)",
    "e.g_alpha": "on claims the legacy core decides: the chunk's sum of gas_burnt_for_function_call (incl. "
                 "host gas) <= G_alpha = 2^22 x 822,756 gas (NearSpecV3.D3.gAlpha), checked after the main "
                 "transition; not applied to claims decided by the hand-over (resharding, storage-proof "
                 "limits; D3/Signed.lean)",
}


def apply(d):
    """Apply the UQ-010 6(c) changes to a near-chunk-v3 draft dict in place; return it."""
    sc = d["semantic_scope"]
    rs = []
    for r in sc["restrictions"]:
        if r["id"] in DROP_RESTRICTIONS:
            continue
        rs.append({**r, "text": RESTRICTION_TEXT[r["id"]]} if r["id"] in RESTRICTION_TEXT else r)
    assert len(rs) == len(sc["restrictions"]) - len(DROP_RESTRICTIONS), "restriction ids changed"
    sc["restrictions"] = rs
    sc["excludes"] = [e for e in sc["excludes"] if e not in DROP_EXCLUDES]
    d["claim_encoding"]["max_witness_bytes"] = MAX_WITNESS_BYTES
    return d
