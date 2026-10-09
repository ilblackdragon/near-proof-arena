# Same-native-block physical ID71/72 conservation

Four additive modules strictly compile, and AuditProcNativeIdBalance passes19 exact standard-axiom guards.

The selected RecordLinear trace sends exactly two native ID requests per original record on71 and receives their exact found/index results on72. The executable ID data trace uses the actual sorted native ID rows, including duplicate public IDs and unknown or repeated requests. Native carry correctness derives first-match results; sorting is handled as a permutation, preserving all multiplicities. Full physical counts on71/72 match on the SAME IDs and NativeBlock list, including padding.

The ID row bound is derived as <=raw rows+64*blockcount. Accepted rawrows<=2001184, blockcount<=32 and each prepared ID list<=64 imply log22 capacity. The balance theorem keeps explicit physical capacity arguments for reuse.

Important remaining obligation: this concatenated ID *data* trace has not been claimed TableLocal. Existing single-block cells encode next=None at the endpoint, so crossing to the next tau requires recomputed eqTop/invTop and comparator metadata. That endpoint repair must preserve the proved data traffic. Full vertical overlay placement and comparator69 conservation remain separate. No new distinctness, prior-order, or accepted-domain restriction is introduced.

Checks: Lean4.34.1 -j1, autoImplicit=false, relaxedAutoImplicit=false, bounded address space, prebuilt checked dependency overlays. No new axioms or sorry.
