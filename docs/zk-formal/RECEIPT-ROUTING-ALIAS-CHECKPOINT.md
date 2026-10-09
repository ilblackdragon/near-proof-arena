# Receipt routing packed-index alias

The current receipt routing bus key is `65*q + position`, evaluated in BabyBear
with modulus 2013265921. The field value `q=1796452668` makes position zero
address public boundary row two, because `65*q = 2` in that field.

`Rcpt/Link/RoutingAlias.lean` kernel-checks a concrete subsystem example. A
native layout with boundary `zz` and shard IDs `[0,1]` gives shard 1 the ownership
interval `[zz,infinity)`. Receiver `aa` belongs to shard 0. Boundary row two is
`[lo=0,hi=0,hiAbsent=1]`; treating it as the first routing position allows the
receiver routing comparison to pass. The example checks all actual `cRoute`
constraints at both receiver bytes and the end marker, the actual `bndMsg`, all
65 public boundary records, full BND table local validity and balanced chained
BND counter messages.

`RoutingQFreedom.lean` checks the dependency of every actual receipt local
constraint. The only q-dependent polynomial is the receipt carry constraint.
It proves uniform replacement of q by any field element preserves **all receipt
TableLocal obligations**, including multiplicity bits and height bounds. Thus an
unextracted local q range is not available to justify interpreting the packed key
as a natural interval index. Cross-table bus messages can change under replacement.

This is a checked local/routing-bus obstruction to the intended semantic link,
not a claimed complete malicious transition proof: full receipt trace construction,
all remaining cross-table buses and final protocol acceptance are not established
by this fixture. Thirteen exact axiom guards pass under bounded strict Lean.

The native interval semantics themselves are now proved in `OwnIntervals.lean`:
`inIntervals (ownIntervals L own) account = true` iff `L.shardOf account = own`,
without sorted-boundary or unique-shard assumptions. Ten exact guards cover this.
`NativeRouting.lean` composes RouteOk with correctly authenticated interval bytes;
it explicitly requires the interval-index binding that the packed-key alias defeats.

An independent assembly lane is evaluating a candidate first-receiver-row q
range check using existing scratch bits. No frozen table, native domain or public
pin has been changed here. Honest range coverage must be proved from the real
public/BND capacity; decoded layout shard count alone does not bound the boundary
array in the native model.

## Checked native routing composition

`Rcpt/Link/PreparedNativeRouting.lean` now proves `candidate_native_routing`:
actual candidate receipt `TableLocal`, the SAME complete physical `ListChain`,
`ReceiptPublicRanges`, `BndWf`, exact BND counter balance and exact public boundary
record counts, together with successful native `prepD0` and `walkD0`, imply every
receipt in that physical view routes under `k.L` to `k.H.shardId`.

The proof uses exact natural public record decoding (`BndDecode`), complete-view
request authentication (`BndAuthenticated`), actual preparation's interval identity
(`PreparedRoutingIntervals`), and decoded boundary validity
(`DecodedRoutingBoundaries`, `BoundaryValidity`). Both endpoints are valid account
IDs whenever present; prefix maxima preserve that property even for unsorted
boundary lists. No bound on native boundary count, ordering requirement, relation
between boundary count and shard count, or assumed native routing is introduced.
The seven-bit index bound comes from the separately checked candidate receipt
constraint, not the frozen table.

All six latest theorem guards in `test/AuditRcptPreparedNativeRouting.lean` pass
under strict Lean settings, bounded to 16 GiB and `-j1`. Dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`. The preceding interval/public
composition contributes five further checked guards. Receipt scratch checkpoint
now totals 93 exact guards. No frozen AIR file or active protocol pin was modified.

Remaining assembly obligations include obtaining these exact global BND balances
from the full certificate, transporting physical receipt routing to selected
source dictionary entries, binding actual remaining witness bytes to WOVH, and
completing the global protocol soundness/admission composition.
