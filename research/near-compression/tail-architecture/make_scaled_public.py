#!/usr/bin/env python3
"""Emit the expected public statement for a scaled run: same root words +
table (with recomputed finals) + per-list context/count/root words. The
root words for lists are the SHA256 of each list serialization — but the
scaled fixture's big list has a DIFFERENT serialization, so its root wire
is unknown to the host; the CIRCUIT computes it and the packet binds it.
For the NEAR_EXPECTED_PUBLIC file we need the exact bytes... which requires
hashing the list exactly as the circuit does. For a geometry/scaling run we
use the prove path's in-process verify (which needs no external public
file) and fresh-verify only for the ORIGINAL packet. So this script is NOT
needed for scaling runs — the driver's prove path self-verifies. Kept as
documentation of what fresh-verify would need.
"""
