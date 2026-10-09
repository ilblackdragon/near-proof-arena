# Corrected Codec comparison charge

Three modules strictly compile; ten exact axiom guards pass.

The actual record-step function appends comparisons only at byte positions2 and7. Each eight-byte phase therefore contributes at most2, each record at most6 across its three phases. Exact successful coreLayout/codecRows execution preserves the comparator list through metadata installation, yielding output.cmps.length≤6*n². For the same valid native blocks with n≤64 and at most32 instances, this is≤786432 comparisons.

This intentionally conservative bound includes forwarding comparisons. It does not substitute generated row count for comparator count. Run.cmps and ScanDist.cmps still require their own actual execution counts and CmpOk proofs. A possible aggregate old40 target2,936,832 fits allowance3,090,136, but its remaining loop bounds are not yet established and no combined capacity theorem is claimed.
