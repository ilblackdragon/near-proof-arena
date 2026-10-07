# NEAR Proof Arena — handover (2026-10-07)

This is for the next lead agent. Read this first, then the two lane status files named in §3 and §4.

## Resumption plan (2026-10-07)

### Latest continuation checkpoint


Root ParserView CHECKED: parser_chain_exists from TableLocal+extracted WalkChain
handles active/inactive/exhausted suffix and yields physical-coordinate consecutive
records, fit, valid segments and padding. parser_chain_lengths lifts exact empty/
nonempty natural length semantics to all members. Target192 jobs+2 exact guards
PASS (/tmp/nearproof-qv-parser-view.log,/tmp/nearproof-qv-parser-view-audit-checked.log).
No root live process. Next mode-specific semantics and per-record parser QVC/
VBYTES traffic, then provider-chain soundness. Last aggregate b7002160 older.
Pending checked agent integrations: D2 source-list seed identity3ebdc6a8 and
trace-local coherent occurrence IDs b8f3ce3c (strict tsize descent/Nodup,9guards),
ups e6ec6714 physical prefix provider family+global use assignment preserving
InstOk (7guards). Receipt6d183280 SREC whole-table traffic complete; only
KEYNIB/DIGEST/FINAL/BND remain in receipt channel work. Full correctness certificate,
admission/reference checker, prover/judge and general NEAR coverage still open.


Root ParserStart/ParserSegments checked: every walk row is a parser-last marker;
length-free next-record constraint holds across final walk boundary, so active
suffix starts with vf. Shifted suffix SegFacts and complete active record list+
padding derived; initially inactive suffix remains entirely inactive. Target191
jobs+6 exact guards PASS (/tmp/nearproof-qv-parser-segments.log,
/tmp/nearproof-qv-parser-segments-audit-checked.log). No root live process.
Next unify active/empty branches into physical record view, derive modes/bytes
and QVC provider no-cycle linking. D2 trace-local coherent IDs under strict
path descent/Nodup underway; full source seed identity3ebdc6a8 checked externally.
Receipt72192363 AKC full physical traffic checked, remaining channels active.
Latest aggregate b7002160 older than newtargets; full AIR correctness/admission/
prover/judge/general NEAR replacement remains incomplete.


Root ParserRecord checked: given actual suffix record segment, position=row
 offset,8 metadata fields constant, vz marker forces one-row zero-length record,
otherwise declared natural length=physical segment rows. length_cases complete;
existing height rules out field wrap. Target189 jobs+5 exact guards PASS,
/tmp/nearproof-qv-parser-record.log,/tmp/nearproof-qv-parser-record-audit-checked.log.
No root job live. Next derive actual suffix segment list/start after walk prefix,
then byte/mode semantics and QVC provider soundness (these remain open).
Integrated D2f6fec709 actual complete nativePathNodes occurrence-address list
with every address authenticated in global records; two guards, no recordId
oracle. Ups wires occurrence-sensitive path levels. Receipt remaining channels
active. Latest aggregate b7002160 older than newest individual targets. Complete
correctness certificate/admission/prover/judge/broader NEAR scope remain open.


Root ParserFacts CHECKED: suffix parser boolean flags, act/first/last relations,
raw-empty single marker, continuation byte increment and8 constant metadata
fields, next-record first flag, padding persistence and physical-last termination.
Target188 jobs+9 exact guards PASS (/tmp/nearproof-qv-parser-facts.log,
/tmp/nearproof-qv-parser-facts-audit-checked.log). Root session64499 terminal0;
no root live job. Next record decomposition (including start after walk prefix),
length/byte/mode semantics and QVC provider-backed chain soundness.
Integrated c8e6f366 exact forest_located_seed NodeS3 identity at occurrence IDs;
db27790a physical native prefix W1/W2 edges exactly match resolved traversal.
Global allocated provider families/use counts/windows remain agent-owned.
Latest fullaggregate b7002160:1904jobs/115audits/924axiomguards/15behavior guards,
older than newest modules. Full end-to-end correctness/admission/prover/judge
and general NEAR coverage remain incomplete; goal active.


New aggregate PASS:1904 jobs,115 selected audits,924 axiom guards,15behavior
guards. Report docs/e2e-results/v3-queue-traffic-integration/report.json;
logs /data/illia/nearproof-deps/validation/v3-queue-traffic-20261007/.
Root session79290 terminal0. After aggregate, ParserRows derives original parser
constraints and exact parser traffic on every non-walk row, including cyclic
wrap via derived first_mode_zero. Target187 jobs+3 exact guards PASS;
/tmp/nearproof-qv-parser-rows.log,/tmp/nearproof-qv-parser-audit-checked.log.
No root job live. Next parser record decomposition/value semantics and QVC
provider no-cycle linking. Integrated D2 actual adjacent native path address
34edd879 and empty-extension resolved occurrence address ebe4c14a. These latest
modules not in aggregate. Receipt remaining channel extraction and update global
occurrence-bound traversal continue. Full AIR correctness, admission/reference
checker, prover/judge and broader NEAR replacement remain incomplete.


Root CounterAggregate CHECKED: each segment yields exactly one QVC step iff
present, using invariant tuple; whole request prefix exactly ordered flatMap;
full physical traffic split into extracted request messages plus explicit parser
suffix for both directions. Target130 jobs+4 exact guards PASS;
/tmp/nearproof-qv-counter-aggregate.log and
/tmp/nearproof-qv-counter-aggregate-audit-checked.log. Generic range_last_only
now public/reused (FinalAggregate changed only helper name/visibility).
Root session10232 terminal0; no live root process. Next parser suffix local
extraction/QVC provider chains, then full queue soundness and fresh aggregate.
Integrated D2beac822a global forest path locator to actual NodeS3/recT/tau;
upsbe0ed6d8 explicit native prefix EDGE list exact original query content and
length. Receipt e60e16b2 full B_MEM sends now joins receives, six guards; RIDS
next via generic IndexedTraffic. Latest aggregate191ea6da is older; end-to-end
certificate, admission, prover/judge and general NEAR coverage still incomplete.


Root CounterTraffic checked: actual walk-row QVC both sides equals singleton
counter tuple iff present=1; present iff terminal+absent0; absent walk forces
vid0; read-mode equation and complete tuple constant through segment. Terminal
step condition tied to actual segment end. Target129 jobs +6 exact guards PASS;
/tmp/nearproof-qv-counter-traffic.log,/tmp/nearproof-qv-counter-audit-checked.log.
No root process. Next aggregate request QVC prefix, extract parser suffix and
prove provider-backed counter chains/no-cycle soundness; full soundness open.
D2 occurrence path locator2b43e0a9 integrated: nid/vid/depth and exact Seg/
record/fullTree correspondence,3guards+3 identical-sibling fixtures. Actual
upsert occurrence-path linkage still agent-owned. Receipt0878f521 whole B_MEM
receives matches rcptRecvs3 including padding,8guards; reusable ReceiptSpans
physical decomposition, sends/RIDS next. Fullaggregate191ea6da predates recent
modules; complete certificate/admission/prover/judge/broad coverage still open.


Root KeyTraffic checked: exact KEYNIB row sends/zero receives, silence on all
non-walk rows, physical range equals concatenated extracted walk traffic.
key_segment_row fixes wid per segment, positions2offset+1/2/3, high/low nibble
order, start/end only at actual boundaries. Target128 jobs +5 exact guards PASS;
/tmp/nearproof-qv-key-traffic.log,/tmp/nearproof-qv-key-traffic-audit-checked.log.
No root live job. Next QVC/parser extraction and link encoded keys to natural
lookup views; full queue soundness still open. Integrated D2b1a7afcf occurrence
pre-node payload+1≤2^22 from accepted A7 (no unnecessary shared-node dedup);
ups02bef78f executable empty-extension resolver/source-level linkage.
Occurrence allocator must refine only consumed edges/source shape, not demand
full node equality under a single PTrie→Nat map for duplicated subtrees.
Receipt32663e8a closes full Wf extraction from actual successful prepD0 and actual
prepared byte length<P, with n≤5000/root widths/body bounds discharged. Other
receipt traffic remains. Last aggregate191ea6da older; complete objective open.


Root FinalAggregate now CHECKED: whole physical FINAL receives equal exactly
one extracted lookup tuple per walk, in order; sends zero; final_counts gives
standard tableBusCount characterization. Generic opaque last_only list lemma
avoids prior segment elaboration growth. Target127 jobs +3 exact guards PASS;
/tmp/nearproof-qv-final-aggregate.log and
/tmp/nearproof-qv-final-aggregate-audit-checked.log. No root process remains.
Next KEYNIB/QVC traffic and parser/provider soundness, exact natural tuple binding.
D2d42ff186 original serialized blob IDs integrated; pre-node occurrence budget
may already follow A7 per-path copies, so agent quantifies before unnecessary
compact union design. Receipt26e09b29 now derives successful prepD0 header n≤5000
and<P in1.2sec using selective gas/compute guard retention; public packing/body
range next. Latest aggregate191ea6da predates these targets. End-to-end correctness,
admission, succinct prover, real judge and general NEAR coverage remain open.


Root FinalTraffic checked: FINAL sends empty, receives exact one lookup tuple
only at each segment terminal; tuple metadata constant over segment, arbitrary
accepted trace. Target126 jobs +4 exact guards PASS (/tmp/nearproof-qv-final-row.log,
/tmp/nearproof-qv-final-audit-checked.log). Wholephysical aggregation NOT checked.
Attempt retained /tmp/nearproof-finaltraffic-full.lean and
/tmp/nearproof-final-segment-attempt.lean; segment aggregation alone caused large
elaboration memory growth. Root stopped exact FinalTraffic PID3053879 (session95373
terminal1), removed unproved aggregation. Earlier generic process query led to
mistaken TERM of receipt PID3051435; receipt agent notified, records external
termination rather than OOM and retries smaller PrepCount proof. Track exact
file/PID, never identify processes merely by executable. No root live job.
Next root use opaque generic finite-list aggregation to avoid unfolding full
traffic term, then KEYNIB/QVC/parser linking. Integrated cfe4f99d→7af45349 actual
write-site revelation,638f179e→1d237ff2 proper ancestor edge providers. Receipt
78a208e2 completes Wf from TableLocal+explicit public ranges; native range discharge
active. D2d42ff186 original serialized blob IDs checked, compact nid dedup still
requires union/refinement of differing revealed child views. Latest aggregate
191ea6da older; full certificate/prover/judge/general coverage still open.


Root WalkCount proves final main request exists in every accepted walk chain,
its index≥2 and cv(count)=index−2, count constant across main prefix and initial
count<physical height. Existence derived from no early termination/phase
transitions, no witness or count-range assumption. Target124 jobs +5 exact
guards PASS. Logs /tmp/nearproof-qv-walk-count.log,/tmp/nearproof-qv-count-audit-final.log.
Root session64412 terminal success, no root live job. Next exact canonical
queue traffic and parser/provider soundness; indexed phase/count groundwork done.
Integrated D2c3002bdc and089d903f: minimal shape/known lookup preservation through
actual receipts, scheduler, full main execution; initial builder domain and
write-event binding still active. Upscc22470a earlier terminal-record key edges
from actual consumed prefix (no wf); ancestor traversal/allocated IDs still open.
Receipt86261ff7 derives extracted count/refund byte total<P from physical rows;
natural public total theorem/native Prep admissibility next. Last aggregate
191ea6da older than these targets. Full certificate/prover/judge and broad NEAR
replacement remain incomplete; no protocol/domain changes authorized or made.


Root WalkMain now derives main-request prefix, no lastMain before another main,
slot=i both Fp and Nat (using physical bound), exact kind bits by index:
0delayed,1buffered,2yielded,≥3group. Arbitrary accepted chain; no renderer premise.
Target123 jobs +7 exact guards PASS. Logs /tmp/nearproof-qv-walk-main.log,
/tmp/nearproof-qv-main-audit-final.log. Root no live job. Next main count/final
bounds and exact KEYNIB/FINAL/QVC traffic, then parser/provider soundness.
Integrated ups8ca262c8 ancestor branch/extension symbols+terminal suffix
concatenate exactly to original query; source wf unnecessary. Receipt88c2cb98
closes complete RcptV3Wf token field with actual zero-start sequence/global
receipt Wf/final bytewise public burnt. Public count/body range still active.
Last aggregate191ea6da predates newest modules; global admission/certificate,
prover/judge and broader NEAR goal remain incomplete.


AIR `9959d92c` WalkPhase proves indexed adjacent request transitions, implicit
suffix cannot re-enter main, and exact implicit tau=index distance from entry.
When entry tau=1, natural cv decoding follows from physical height<P, without
caller wrap bounds. Target122 jobs;4 exact phase guards PASS after correcting
an accidental nested guard from prefix-name replacement in followup commit.
Logs /tmp/nearproof-qv-walk-phase.log,/tmp/nearproof-qv-phase-audit-final.log.
Root no live job. Next root main prefix/slot/kind ordinal characterization and
exact queue traffic/parser/provider linking. Last fullaggregate191ea6da predates
newphase/agent imports. Agent5bceef6c integrated as9d28d417 shape-only native
lookup and known-query preservation through writes,17guards+4overflow fixtures;
ab342dc5 as5dce8f1a all11 native terminal EDGE/BMAP providers without source wf,
10new/7recheckedguards. Global allocated IDs, earlier edges/pcid and full multi-
write source-memory assembly remain open. Receipt public ranges/token table
composition active. Complete certificate/admission/prover/judge/broad coverage
still incomplete; goal remains active.


AIR aggregate `191ea6da`:1859 jobs,81 selected audits,752 exact axiom guards,
15 behavior guards PASS. Report docs/e2e-results/v3-queue-extraction-integration/
report.json; external logs /data/illia/nearproof-deps/validation/
v3-queue-extraction-20261007/. Includes committed extraction throughWalkChain,
physical QSH/VBYTES, native terminal edge and receipt token/public-alias work.
Root aggregate session90121 terminal success; no root process remains.
After aggregate, `8bb422e8` WalkIndex proves request ordinal≤segment start,
chain length≤physical height and every index<P directly from TableLocal.
Target121 jobs and3 exact guards PASS; /tmp/nearproof-qv-walk-index.log,
/tmp/nearproof-qv-index-audit-final.log. Separate audit preserves report hashes.
Next root: global indexed ordering and canonical queue traffic/parser soundness.
Material update composition gap from ups agent: native InstOk/ByteInput/MemOk
still requires source root.wf, which may fail after earlier writes with exact
memory overflow. Shape-only read preservation closes revelation only; multi-write
memory assembly needs checked refinement/modulo normalization or generalized
source-memory lemmas. Do not silently assume post.wf. Terminal provider package
itself avoids source wf. Full objective and admission/reference-checker/prover/
judge/broad NEAR coverage obligations remain open.


AIR `fc35da1c`: WalkSegments lifts full main/implicit transition equations
between whole extracted walks, with metadata transported from segment starts.
WalkChain packages nonempty consecutive complete segments plus bounded suffix;
TableLocal alone yields a chain. All nonfinal segment terminals have wend=0;
final chain terminal has wend=1, including physical-last boundary. No canonical
renderer assumptions. Target120 jobs and24 exact extraction guards PASS.
Logs /tmp/nearproof-qv-walk-chain.log,/tmp/nearproof-qv-chain-audit-final.log.
Root no live job. Next indexed main/implicit metadata, canonical KEYNIB/FINAL
traffic and parser/provider soundness; aggregate newer integrated checkpoints.
Ups a408a949 cherry-picked: actual absent-key terminal EDGE shape membership
for seven cases from executable byte-preserving annotations. Global allocated
IDs/resolutions and other edges remain obligations. Receipt and D2 continue
public-range/total and shape-only write determinacy respectively. Last full
aggregate dc4c12d4 remains older; complete objective still open.


AIR `3d37a7b8`: arbitrary accepted WalkOrder now derives initial main/tau/slot/
kind fields, full main advance equations, main→implicit switch, implicit tau
increment, implicit fixed shape, public K termination binding, and exact wend
iff walk-prefix end (including physical final row). These are row-level facts;
indexed whole-list ordering/canonical traffic and provider linking still open.
Target118 jobs and19 exact extraction axiom guards PASS. Logs
/tmp/nearproof-qv-walk-order.log,/tmp/nearproof-qv-order-audit-final.log.
Root no live process. Next: lift row transitions through extracted segment list,
then key/FINAL/QVC traffic and parser soundness; integrate latest agents in a
new aggregate after interfaces settle. Last aggregate remains dc4c12d4.
Receipt8274e0a1 now has actual global token run from zero through empty/nonempty
lists and final16-byte public burnt binding;17 guards. PublicAlias checked
count/body field alias regressions; ReceiptPublicRanges records N/body<P.
Correctly scoped Prep range derivation remains agent-owned, no domain narrowing.
D2 structural shape-only find preservation through upserts compiles, proving
shape preserved and chaining write-key determinacy next; avoids post-memory wf
assumption. Ups remaining edge/pcid authentication continues. Full objective open.


AIR `91be9ea8`: WalkMetadata derives all ten constant walk fields from arbitrary
TableLocal+extracted segment; first tag=7+6lo+3hi and exact group/non-group
length. WalkBytes derives all8 key bits, canonical byte<256 and exact four
(tag,length) alternatives (7,1),(13,1),(10,1),(16,9). No generated trace premise.
Target117 jobs and12 exact standard-axiom guards PASS; logs
/tmp/nearproof-qv-walk-bytes.log and /tmp/nearproof-qv-key-audit-final.log.
Next root: main/implicit ordering, exact key traffic, parser/provider extraction.
Newest integrations: edbc5969→8e779507 ordered VBYTES seed/supply sublist incl
complete physical sends (not yet whole global balance);3e39c91c→5348e4e3 native
value terminal edge membership from byte-preserving source annotations.
D2 now owns structural-shape find preservation through prior writes: full wf
may not survive output memory overflow, so do not assume it. Ups continues
remaining generated edge/pcid authentication. Receipt agent found exact statement
issue: four byte bounds alone do not prevent public count/body+P aliases when
AIR checks only field-compressed values. Agent will formalize regression and
scope natural extraction with actual Prep admissibility, without frozen table
changes or native domain narrowing. TokenSequence/TokenValues agent WIP.
No root job live. Last full aggregate remains dc4c12d4; newer targets separately
checked. End-to-end certificate/admission/prover/judge/broad coverage remain open.


AIR `bcc619ca`: arbitrary accepted QV trace extraction starts in
Qv/Extract/WalkRows and WalkLength. TableLocal alone gives boolean flags,
SegFacts and full consecutive walk-prefix decomposition with inactive suffix.
For every extracted segment, wp is exactly row offset and length is 1 or9;
physical height≤2^22<P discharges wrap exclusion. No generated/canonical trace
premise. Target115 jobs and5 exact standard-axiom guards PASS. Logs
/tmp/nearproof-qv-walk-length.log and /tmp/nearproof-qv-walk-audit-final.log.
Root next: constant metadata/key shape, main/implicit ordering, parser extraction,
and FINAL/provider linking. This is not yet complete QV soundness.
New shared AIR integrations after dc4c12d4 aggregate: D2 physical QSH469c3bd6
as33360fd9; update node-local edgescde397c4 aseac906cf and native determinate-read
terminal revelationbfa26ba3 as6bd04af9. Receipt86b2f633 removes entering-token and
global-index premises for per-receipt Wf via ListChain.indexed_wf;984dd0d1 adds
all token endpoint carry equalities. These newer imports are not covered by the
older1832-job aggregate. Receipt TokenValues WIP agent-owned; root no live job.
All previous global capacity, soundness, admission/reference-checker, prover,
real judge and broad NEAR coverage obligations remain active.


AIR `dc4c12d4`: accepted-input `Assembly.QueueRender.checkD0a_queue_render`
constructs corrected per-use-rank queue trace with full TableLocal, canonical
TableTraffic and physical QVC send/receive permutation over all 2^22 rows.
Parser validity and fit derived from checkD0a B0 (B0 stays 2,000,000 bytes);
request Holds derived from native main reads and implicit missing requests.
Prepared header roots/K and native execution witnesses remain explicit inputs.
Integrated update `280a90c3` as `d9df3669` (complete native InstOk, stored edge
IDs/authentication and capacity still separate); D2 QSH payload `b0deede2` as
`99867de7`; receipt `31c82f2a` closes all per-receipt Wf including RouteOk.sem,
with global index/canonicity and entering-token invariants still premises.
Aggregate PASS: 1832 jobs,71 audits,651 exact axiom guards,15 behavior guards.
Report: shared AIR docs/e2e-results/v3-queue-render-integration/report.json;
logs /data/illia/nearproof-deps/validation/v3-queue-render-20261007/.
Root aggregate session70947 terminal success; no root build left running.
Next root: arbitrary accepted combined QV trace extraction, then AIR-to-Good.
D2 owns physical QSH and VBYTES balance; receipt agent owns whole-list token
propagation/totals; update agent owns actual stored edge/pcid/window auth.
Additional update dependency: accepted write-key value revelation through
preceding writes (generic upsert permits replacing Slot.ref); do not strengthen
source wf or assume authenticated edges to bypass this.
Shared AIR receipt IndexedWellformed/TokenBytes and test WIP are agent-owned,
excluded from this checkpoint. Global honest capacity/SHA/post-shadow ownership,
reference lean4lean failure, complete admission/correctness certificate, succinct
prover, real judge and broader NEAR coverage remain open. Goal stays active.


Root QV `cb198504`: complete canonical mixed TableTraffic all buses/both
sides+silence, paired with TableLocal. CombinedPrepared derives public K binding
from actual prepared bytes, rootsSized, K<u32, implicit-list length equality.
Target398 jobs;197 exact axiom guards+15 fixtures PASS. Logs
`/tmp/nearproof-prepared-queue.log`, `/tmp/nearproof-prepared-queue-audit-final.log`.
No root process. SharedAIR receives cherry-pick. Next root: aggregate integrate
latest native ownership/rank balance, update byte+memory+walk, receiptWf; then
native honest queue construction and accepted-trace extraction. D2 logical QVC
balance now compiles (pendingaudit/commit), ready for physical lift using root
mixedTrace_counter_messages; no balance claim until checked. Receipt74e9fca5
closes full arith_of and wf_of_route, RouteOk/token/counter caller facts remain.
Ups four-row walk finite proof factoring after bounded slow attempt; committed
byte/part/memory proofs stable. Last fullaggregate cb1e3577 is older. No full
AIR certificate, unrestricted NEAR coverage, succinct prover or judge result.


Root QV `e32b4d52`→AIR`0e3d93b9`: physical walk-prefix aggregation for KEYNIB,
FINAL,QVCbothdirections,QSHreceives. `mixedTrace_counter_messages` characterizes
ALL physical QVC traffic as mapped natural walk rank messages+parser endpoints,
up to permutation. Repeated request multiplicities preserved. Target278 jobs;
189 exact axiom guards+15 fixtures PASS (`/tmp/nearproof-word-aggregate.log`,
`/tmp/nearproof-word-aggregate-audit-final.log`). No root process. D2 notified to
compose c594490f corrected full-plan rank classes with this physical API for
actual QVC balance. Next root: complete other-bus canonical mixed traffic and
sound extraction/aggregate integration. Last wholeaggregate cb1e3577 still older.
QVC message characterization is NOT balance by itself. All work remains active,
no end-to-end certificate/prover/judge result. Ups92d6cbca absent-key mismatch
ready for actual WalkOk construction; receipt7bc16688 deposit/storage arithmetic
and gas-price borrow, remaining V3 gas/token/routing active.


Root QV `8ccb2287`: physical mixed parser suffix traffic equals canonical parser
VBYTES/QVC/QSH messages up to permutation on all buses/both directions; padding
silent. `mixedTrace_traffic_split` partitions every physical message into walk
prefix+canonical parser contribution, preserving multiplicities. Reuses existing
CombinedParser.parser_row_traffic (initial duplicate name detected and removed
by complete audit). Target273 jobs;180 exact axiom guards+15 fixtures PASS.
Logs `/tmp/nearproof-parser-traffic.log`, `/tmp/nearproof-parser-traffic-audit-final.log`.
No root process. Next root: physical walk-prefix aggregation into word messages;
D2 owns corrected rank semantic QVC/mode balance. Its e736d359 proves corrected
present walk provider ownership+rank<total,6ca80a31 actual main rank sequence.
Whole-table global bus balance/sound extraction still open; last aggregate
cb1e3577 precedes this. Ups concrete WalkOk local construction active;
receipt58c53868 closes tprev_le with existing no-wrap bound, arithmetic/routing
remain. SharedAIR receives root cherry-pick. No end-to-end certificate claim.


Root QV `24f29b7b`: executable mixedRows/mixedTrace and FULL
`mixedTrace_table_local` for all physical walk+parser+padding rows. Ordinary
inputs only: MainValues.Valid, Record.Valid, fit, supported log, public K binding.
All prior cell/boundary premises discharged by generated construction; generic
in Resolve. Target262 jobs;175 exact axiom guards+15 fixtures PASS. Logs
`/tmp/nearproof-mixed-local.log`, `/tmp/nearproof-mixed-local-audit-final.log`.
No root process. Next root: whole physical mixed-table traffic, then sound
extraction, and aggregate latest agent checkpoints. No global bus balance or
end-to-end certification claimed. Shared AIR receives cherry-pick.
IMPORTANT resolver mismatch found by D2: initial queueForestResolve returns total
users for every walk; actual QVC needs prior-use ordinal per walk, with total
only on parser. D2 is correcting resolver+prefix-count chain. Prior count/seed
lemmas remain useful but do not prove bus completeness; row capacity theorem
remains valid as row count is resolver-independent. Last wholeaggregate cb1e3577
precedes this checkpoint. Other pending agent work: Ups7682b647 fullMemOk family
with depth≤400/HPL<2^22 still renderer capacity premises; receipt31234053 system
iff no-wrap; D2a062eb27 full multiplicity count (before resolver correction).


Root QV `812d5d40`: executable parser suffix after nonempty prefix satisfies
ALL combined table constraints, including interaction bits, cross-record,
padding and cyclic wrap. CombinedParserLift handles extra-column zero embedding;
CombinedRecordPlacement derives original parser acceptance from executable valid
records and proves public-input independence. Final combined_records_suffix_local
requires ordinary generated cells, zero extra columns, fit, and first-prefix
parser marker/zero-mode cells; NO local AIR premise. Target260 jobs;167 exact
axiom guards+15 fixtures PASS. Logs `/tmp/nearproof-record-placement.log`,
`/tmp/nearproof-parser-suffix-audit-final.log`. No root process. Next root: mixed
trace constructor; derive records columns≥37 zero and prefix/suffix first cells,
then combine with plan_prefix_all_constraints into whole TableLocal. Exact
traffic and sound extraction still separate. SharedAIR receives cherry-pick;
last fullaggregate cb1e3577 precedes this. Agents remain active: D2 provider
multiplicity/traffic (408d367a); Ups upperMemOk0b2bba21; receipt account grammar
52103b83 and system/Wf work. No end-to-end replacement claim.


Root QV `ca9e0b00`: `CombinedPrefixLocal.plan_prefix_all_constraints` proves
EVERY table.allConstraints equation on EVERY generated physical walk-prefix row,
including base parser overlay and interaction-bit constraints. Ordinary inputs:
MainValues.Valid, PrefixCells, prefix≤height, public K binding, and first suffix
row markers (act=0 or vf=1, walk=0) if suffix exists. No local-acceptance premise
in the final prefix theorem; intermediate LocalCompose is only a grouping lemma.
Target230 jobs;162 exact axiom guards+15 fixtures PASS. Logs
`/tmp/nearproof-prefix-local.log`, `/tmp/nearproof-prefix-local-audit-final.log`.
No root process. Next root: parser suffix local acceptance and physical wrap,
then full combined trace+traffic. Do not equate full prefix with full table or
end-to-end certificate. Cherry-picked root commit into shared AIR; last aggregate
remains cb1e3577 (before this root checkpoint). Agent new pending commits:
D2 25910b9b QueueSeed exact forestStoreViews ValE vid/bytes/tau membership;
Ups ef048908,693d2dd0,1b8d5507 memory prerequisites; receipt69b2a074 actualV3
canonicity. Their newest audits await next aggregate check.


**Latest full AIR integration `cb1e3577`:1,758 jobs,39 audits,430 exact axiom
guards+15 behavior checks PASS.** Report in shared AIR:
`docs/e2e-results/v3-native-queue-integration/report.json`; external evidence
`/data/illia/nearproof-deps/validation/v3-native-queue-20261007/`.
Driver `/tmp/nearproof-check-native-queue.py`, externalcopy audit-driver.py.
Root new `Assembly/QueueCapacity.checkD0a_queue_rows_fit` composes actual
accepted-input queue records+queueForestResolve+walk plan to≤2^22 rows, without
separate parser byte/count premises. Frozen B0 remains2,000,000. Formal native
execution/trace premises remain; ownership and full traffic are not implied.
Integrated D2 through0842527c→563ef5e4, Ups throughbdd47e79→7d5aabef,
receipt audits through482d216a, QV through03be6b90→8b71e602. New receiptf500146a
exists in shared history but its new audit is outside this selected39-audit set;
Ups ef048908 likewise not yet integrated. No active root build. Next root:
full walk constraint composition and parser suffix acceptance; agents continue
seed-ValE/traffic, memory assembly, receipt Wf/remaining channels. No end-to-end
certificate, unrestricted coverage, succinct prover or judge validation claim.


Root QV `03be6b90`: ALL24 neighbor equations at EVERY physical native walk-prefix
row, from PrefixCells and prefix length≤trace height; cyclic indexing derived.
Exact endpoint-coordinate equivalence closes physical-last equation; exit needs
only first suffix row walk=0 (or physical wrap). PrefixCells.of_append derives
cells from full appended encoding. Target228 jobs;156 exact axiom guards+15
fixtures PASS. Logs `/tmp/nearproof-trace-neighbors.log`,
`/tmp/nearproof-trace-neighbors-audit-final.log`. No active root build. Next root:
full walk constraint composition, parser suffix, provider/global traffic; schedule
new aggregate integration of latest agent checkpoints below. No whole-trace
acceptance, unrestricted NEAR coverage or end-to-end certificate claimed.
D2 `0842527c` (after5ace7872): actual parser Record list Valid, bytes≤2^21,
count≤83,367 from native acceptance; occurrence IDs/modes/countP users/distinct
providers.34 guards pass. Next seed-ValE correspondence/resolver traffic.
Ups `bdd47e79`: whole native ByteInput family from actual trace+source.wf, all12
constructors, full native InstOk with only WalkOkU explicit.4 guards pass.
Receipt `482d216a`: exact final rcptSends3 B_BYTES both TableTraffic directions
from TableLocal and extracted concrete views.13 guards pass; fullWf/otherchannels
remain. These checkpoints await next aggregate integration/audit.


Root QV `27305da2` + `55369c80`: full native plan successor classification,
exact final flag at last plan entry, all24 neighbor equations for indexed word
boundaries; flattened walk row location/exact lookup and successor offsets.
Target227 jobs;147 exact axiom guards+15 fixtures PASS. Logs
`/tmp/nearproof-row-layout.log`, `/tmp/nearproof-row-layout-audit-final.log`.
No active root build. Next: physical trace casting and cyclic/end layout facts,
then full walk constraint composition and parser suffix. The new list-addressing
proofs remove coordinate assumptions at the list layer, not yet physical trace
or whole local acceptance. Both root commits cherry-picked into shared AIR.
Agent receipt447d1d5c now extracts full actual BYTES into chainByteMsgs with
natural counters (semantic rcptSends3/fullWf remain). Ups13be6a19 connects native
source adjacency to positioned signed cN IDs; next whole ByteInput family.
D2 provider ownership/charging remains independently active. New agent changes
still await next aggregate integration/audit; no replacement claim.


Root QV `db44fb12` + `9d9e0412`: all nine between-word step equations composed
by cases, plus all24 neighbor equations (13 inside-word, two start, nine step)
for internal byte neighbors and final words. Terminal-to-next-word rows satisfy
first15, ready to combine with step cases. All24 proved actual AIR members.
Target225 jobs;129 exact axiom guards+15 fixtures PASS. Logs
`/tmp/nearproof-neighbor-equations.log`, `/tmp/nearproof-neighbor-audit-final.log`.
No active root build. Next: derive neighbor classification from flattened native
plan and assemble full walk local acceptance, then parser suffix/traffic.
Physical layout/generated-cell premises are still explicit; no whole-trace
acceptance or end-to-end certificate claimed. Shared AIR receives both commits.
Agents remain active: D2 native value occurrence index5ace7872 and provider
allocation; Ups source adjacency b2bfa802; receipt offset reconstruction c9293e84
and whole BYTES composition. These newer agent checkpoints need next aggregate
integration/audit. The previous user-facing progressbar was status only; this
continuation made checked, committed proof progress.


Root QV `4ae98b04`: all five main successor AIR equations from actual indexed
native plan neighbors; all between-word gates zero inside words or on final
words. Target223 jobs and QV113 exact axiom guards+15 fixtures PASS.
Logs `/tmp/nearproof-main-steps.log`, `/tmp/nearproof-main-steps-audit-final.log`.
Next root: assemble case/layout lemmas into full walk local acceptance, parser
suffix composition and whole traffic. Individual equations do not yet imply a
whole-trace theorem. No active root build. D2 owns executable key→native value
occurrence allocation and unique provider charging; Ups runtime WalkOk/edges;
receipt header bytes/full semantic Wf remain active.


Root QV `8d3371c6`: actual implicit indexed order/flags, successors and main-to-
implicit boundary proved; matching AIR equations for entering tau1 and later
tau+1 transitions checked. Target222 jobs and QV108 axiom guards+15 fixtures
PASS (`/tmp/nearproof-implicit-steps.log`,
`/tmp/nearproof-implicit-order-audit-final.log`). Next root: main-step field
translation and full local/layout composition. No active root build.
D2 8b69ebf4 derives accepted aggregate preValueBytes≤B (12 guards); delegated
constructive distinct queue records/ownership charging next, with duplicate
requests sharing providers. Extra post-query collision-shadow cost remains open.
Ups ab6ca604 closes all non-walk InstOk fields (520 jobs,4 guards), leaving actual
WalkOkU/IDs, memory/window/global capacity composition. Receipt51bd055c closes
extracted count/header register facts with byte range still explicit.


Root QV `3b80b751`: indexed native main-plan metadata/flags and exact adjacent
successor recurrence proved (slot+1, stable count, kind bits, nonfinal flags).
Duplicate shard IDs preserved. QV101 exact axiom guards+15 fixtures PASS; focused
77-job target PASS. Logs `/tmp/nearproof-main-order.log`,
`/tmp/nearproof-main-order-audit-final.log`. Next: field translation, main-to-
implicit and implicit order, then full layout/local composition. No root job.

**Capacity correction verified in source:** frozen B0=2,000,000 at
`spec/lean/v3/NearSpecV3/ChunkValidationV0a.lean:319`; actual ValWf.rows≤2^22
at`zk-formal/ZkFormal/NearV3/Extract/ValProof.lean:36`. These differ from the
conditional combined QV parser2^21-byte premise. Earlier references to a frozen
2MiB ValE cap are inaccurate.87,382 duplicate buffer entries exceed accepted
A7 through the pre-value, so are NOT an accepted-transition counterexample.
No budget changed. D2 now derives proper retained/QV bounds from accepted A7.


**Latest full AIR integration `862fc32c`:1,711 jobs,19 audits,226 exact axiom
guards+15 behavior checks PASS.** Report:
`docs/e2e-results/v3-native-rcpt-integration/report.json` in AIR; evidence
`/data/illia/nearproof-deps/validation/v3-native-rcpt-20261007/`.
Integrated QueryAccepted7adf4cb4→8aa286b3: actual accepted input yields a fresh
encodable/decodable targeted-store witness, exact unfoldedBytes and original A7
bound. This closes raw-store A7 completeness, NOT current ExtV3/AIR completeness.
Retained-byte classification, instance ownership and2MiB value capacity remain.
Full native PartOk through4e3c94f8 and total native part encoding27dd6b63 are
integrated. Receipt through9b210b7c includes actual list decomposition/no-wrap,
terminal offsets, j/le uniqueness and exact whole RCL traffic; full semantic
Wf/byte traffic still open. Queue through93728ed5 physical boundaries integrated.

Next root: actual between-word sequencing and full local/layout composition.
No active root build. D2 next checks capacity with repeated buffered shard IDs:
87,382 empty duplicate entries exceed2MiB while below3MB native store budget;
NOT yet an accepted-transition counterexample, must check unchanged A7 and
constructive native acceptance. Do not assume distinct shards or narrow domain
to justify current conditional2MiB parser/value bound. Representation/cost must
be repaired if accepted coverage exceeds it. Receipt source RCL binding ongoing.


Root QV `93728ed5`: first-row/nonfirst, no-restart and next-word start equations
proved; physical last/exit equations proved with explicit layout premises still
to be derived during full trace construction. Target219 jobs and QV97 exact
axiom guards+15 fixtures PASS (`/tmp/nearproof-physical.log`,
`/tmp/nearproof-physical-audit-final.log`). Next root: between-word metadata
sequencing, actual layout premises, and whole local/trace composition. No active
root job. Many additive receipt/Ups/assembly checkpoints since9fbbdabf still need
joint integration; their individual audits are evidence only for their scopes.


Root QV `1f001da8`: six main/implicit metadata field equations, last-main count,
end-main and absent-buffer count equations derived from generated plan membership.
Subtraction slot−2 is justified by the derived slot≥2 bound. Target218 jobs and
QV91 exact axiom guards+15 fixtures PASS. Evidence:
`/tmp/nearproof-metadata-equations.log`,
`/tmp/nearproof-metadata-equations-audit-final.log`.
Next root: physical endpoints and between-word transition equations, then full
local/trace composition. No active root build. Ups4e3c94f8 closes full encoded
native PartOk from actual trace+ByteInput; whole instance/store IDs remain open.
Receipt15274448 closes unique terminal le and global header j; whole-table RCL
composition and full receipt semantics remain. New agent checkpoints await joint
integration; full proof goal remains incomplete.


Root QV `2a746890`: last-main count/type/source facts, implicit kind/slot,
final tau=K and absent-buffer count0 derived from actual native plan membership;
actual AIR public termination equation proved using existing public K binding.
Target217 jobs and QV86 exact axiom guards+15 fixtures PASS. Logs:
`/tmp/nearproof-termination.log`, `/tmp/nearproof-plan-termination-audit-final.log`.
Root next: remaining metadata field equations, physical boundaries and between-
word sequencing, then complete local/trace composition. No active root build.
Assembly73a07eb9 now preserves exact native per-transition run/rebuild/A7-related
quantities for targeted query-retained raw stores; AIR ownership/2MiB allocation
remains unresolved. Receipt le/RCL uniqueness and global indexing in progress.


Root QV `0bd3bed4`: nine actual candidate read-gate equations (including absent
vid0, present/group/count flags, end-implies-last), final key position0/8 and
native first-byte equations are proved. Target215 jobs and QV80 axiom guards+15
fixtures PASS (`/tmp/nearproof-key-endpoints.log`,
`/tmp/nearproof-read-gates-audit-final.log`). Remaining local work: last-main/count,
implicit metadata, public termination, physical endpoints and between-word
sequencing, then full constraint/trace composition. No active root job.
Receipt checkpoint7222be79 connects actual terminal oEnd to bounded extracted
list length. Assemblyd7c393de gives targeted retained-store exact pre/post replay
and original serialized-store cost, but not2MiB value allocation. Ups shape and
metadata additions await next joint integration. Full goal remains incomplete.


Root QV `72bf392e`: within-word ten-field metadata preservation and three
clock equations, plus actual byte and mode equations, proved from generated
cells over any commutative ring. Target213 jobs and QV76 exact axiom guards+15
fixtures PASS (`/tmp/nearproof-read-algebra.log`,
`/tmp/nearproof-inside-algebra-audit-final.log`). Next: terminal/read gates,
endpoints and between-word sequencing, then full constraint/trace composition.
No active root job. Receipt agent's new `d8d0724a` closes actual list/header
decomposition and encoded-length no-wrap; full receipt semantic Wf/traffic still
open. Further assembly/Ups additive checkpoints await joint integration.


Root QV `120ee9e5`: generated flag/byte bit bounds and actual AIR equations,
all `CombinedTable.table.bitConstraints` multiplicity equations, and inactive
row gates proved over arbitrary commutative rings from generated cells. No
acceptance premise. Target155 jobs and QV71 exact axiom guards+15 fixtures PASS;
logs `/tmp/nearproof-combined-boolean.log`,
`/tmp/nearproof-boolean-audit-final.log`. Root next: remaining read algebra and
sequence constraints, full parser/walk composition, allocator ownership and
reverse extraction. No active root job. Newer than aggregate below.


Root QV `acce82df` adds generated walk base-parser constraints and physical
parser-to-first-walk overlay preservation. The latter uses actual first delayed
mode0; it preserves evaluation without assuming original constraints hold.
`Walk.base_constraints` proves every transformed base equation for generated rows
with inactive-next or next-record-start, discharged for next walks and padding.
Target154 jobs and combined64 exact axiom guards+15 fixtures PASS. Evidence:
`/tmp/nearproof-walk-base.log`, `/tmp/nearproof-boundary-base-audit-final.log`.
Next root: extra read-sequence constraints and multiplicity bits, full plan/parser
composition, ownership/extraction. No root job active. This focused checkpoint
is newer than the full aggregate below.


**Latest full AIR integration `9fbbdabf`:1,663 jobs PASS;13 audits,
182 exact axiom guards,15 behavior checks and7 theorem examples.** Report in AIR:
`docs/e2e-results/v3-word-native-integration/report.json`; external evidence
`/data/illia/nearproof-deps/validation/v3-word-native-20261007/`.
Root QV `c7435184` → AIR `ea4284e4` composes all four bus families over complete
native key words: exactly one FINAL, optional single QVC step, canonical numbered
key nibbles+markers, and shard bytes/count. QV57 guards+15 fixtures pass. Next
root work: whole-plan composition and generic local constraints, parser wrap,
ownership and reverse extraction. No active root build.

Integrated native `24742b93` → AIR `49e02383` derives every GoodV3 field from
actual acceptance except the explicit unchanged original A7 unfolded-size bound.
Normalized-witness shape and singleton canonical reads are closed; this is NOT
FactorComplete. Update allocator depth/kind/part-count/descent metadata through
`b864f657` are integrated. Source SHA and candidate SRC34 public/reuse through
`a6debb88` are integrated; actual candidate assembly must choose that interface.

New receipt gap from agent code audit: RcptV3ViewStmt currently occurs only at its
definition, with no whole-table extraction theorem constructing RcptV3Wf. RC
encoded-length/no-wrap cannot be presumed. Receipt agent owns explicit span-bound
linking then actual receipt decomposition. All end-to-end blockers remain active.


Latest root QV `e1fb4f04` adds exact row-level FINAL/QVC/QSH field messages;
together with KEYNIB all four walk message families are checked. QSH natural
subtractions use proven bounds, including group slot≥3 from actual plan
membership. Target211 jobs and combined49 axiom guards+15 fixtures PASS;
logs `/tmp/nearproof-shard-traffic.log` and
`/tmp/nearproof-terminal-shard-audit-final.log`. Next: compose complete words
and plans, prove generic local constraints and parser wraparound, then ownership
and reverse extraction. No full honest trace or bus-balance claim; no root job
running. This focused checkpoint supersedes the39-guard root result below.


Latest root QV `f416a670`: generated walk rows now prove parser-provider silence
and exact field KEYNIB row messages, including IDs, positions, nibble values,
start/end markers and multiplicity. Combined audit39 exact axiom guards and15
regressions PASS (`/tmp/nearproof-walk-traffic-audit-final.log`, target build
`/tmp/nearproof-walk-traffic.log`). This is newer than the focused report below.
Root next: exact QVC/QSH traffic, whole-word/plan composition, generic local
constraints, parser wraparound and allocator ownership. Agents report new
additive source SHA/public, normalized-witness shape and plan metadata proofs;
these still need root joint integration. No active root build.


**New focused checkpoint AIR `5529e516` (sources `791f879f`):823 dependency
jobs and8 audits PASS,84 exact axiom guards+15 field fixtures.** Report:
`docs/e2e-results/v3-walk-shape-integration/report.json` in AIR; external evidence
`/data/illia/nearproof-deps/validation/v3-walk-shape-20261007/`.
This is a focused joint check, not a replacement for the full aggregate below.

Root QV `405f561c` → AIR `d9557369` now generates actual native queue walk rows,
proves exact main/implicit request projection and `3+9*groups+K` rows, natural
and field byte reconstruction, and the full native key nibble sequence.
Conditional combined log22 capacity uses existing 3MB buffered input,31 implicit,
2MiB record bytes and134028 records; actual allocator ownership still must
supply those premises. QV audit33 axiom guards+15 fixtures. Root next: generic
walk local constraints/traffic, parser wraparound, ownership and extraction.

All native leaf/extension split cases plus wrappers now provide byte and memory
inputs, including executable mB assignment (`2ca69528` → AIR `791f879f`).
Physical serialized length and surrounding child source-byte bounds remain.
Original decoded witness full D0Shape is now proved (`a9e9ddb6` → AIR `fbbd0de9`),
including exact canonical consumed header bytes; normalized witness transfer
and A7 remain open. Source `520c9e0c` now extracts all five buses and unique
terminal SIZE from arbitrary logical acceptance; SHA/public semantics,
isolation and global no-wrap remain open. These supersede corresponding older
gaps stated below. Agent scopes continue unchanged. No active root build.


**Latest aggregate AIR `b5d5817b`:1,585 jobs PASS;12 audits,130 axiom guards,
12 behavior checks and16 theorem regressions.** Report:
`docs/e2e-results/v3-combined-source-native-integration/report.json` in AIR;
external logs under `/data/illia/nearproof-deps/validation/v3-combined-source-native-20261007/`.
This integrates leaf cursor repair, combined queue parser/public bindings,
source joined/unit extraction, native preparation and decoded shape additions.

Root QV checkpoint `0d93939a` (AIR `fee97cc3`) binds the actual full public u32 K
at26 to the candidate expression. `0e9a34b7` (AIR `a96dbcb2`) derives zero read
gates on walk=0 rows and exact standalone-parser traffic from combined local
constraints; original parser constraints transfer when current/next walk flags
are zero. Combined audit15 guards+12 fixtures. Next root work: honest walk
renderer and traffic, parser suffix/wrap composition, native capacity/ownership,
then reverse queue extraction.

Leaf matched metadata repaired in `10b470af` (AIR `027df827`), with actual
root[0,15] yielding(ts,ti,ci)=(3,2,0) and child-leaf regressions. Native terminal
value, inserted-child and extension ByteInput+MemOk dispatch are checked;
branch ancestor additive checkpoint `aa38006f` follows the aggregate. Split
runtime dispatch and allocator linkage remain.

NativePrepared `8768bf43` bundles actual prepD0, execution/header/source and
witness bounds. D0Shape still needs header parser converses (decoded transition/
receipt/path/entry shapes are checked). A7 normalization has a genuine issue:
unread original blobs can shadow new post blobs under first-wins lookup.
`fb28c196` RetainedStore proves retaining all original blobs preserves all
lookups/rebuildPost and cost without hash injectivity. This is NOT adopted into
ExtV3: unreferenced implicit ValE seeds default to tau0, and the 3MB store cap
does not imply the unchanged2MiB value budget. Keep both gaps explicit.

Source `c0ea362a` proves root/segment unit decomposition; `f7cde3f6` additionally
extracts full computed/skip BlockChain and bounded native counters, with44 guards.
The latter is committed after aggregate imports were fixed, so its focused audit
is the evidence. Source agent proceeds semantic metadata/traffic linking.


**After AIR18ca4f17:** combined queue table is implemented (`1dad2d20`,
AIR `9b5850bc`), with actual shape52/8/6/8/log22,14 interactions and local
degree≤6. Five exact axiom guards+12 Fp fixtures pass. Parser length is overlaid
with read mode on raw-empty walk markers; `CombinedOverlay` proves evaluation
transport and unchanged parser-row evaluation. Actual `ReadPlan` confirms main
group-data reads are RAW(mode2), not empty; preserve that semantics.
`SourceCurrentSize` now reads this actual table;275-job build rechecks total
8,359,074/margin29,534. Generic honest walk rendering/traffic, full parser
transfer, extraction and native capacity are the next root queue tasks.

Log23 candidate verifier now has schedule/compiled-query bounds (`cef7a7f0`,
AIR `3a4b1bff`);26 guards+8 regressions pass. Source `2ad46fa4` proves arbitrary
accepting physical partitions plus isolated carry balance reconstruct logical
TableLocal and exactly preserve all external bus counts.24 guards+3 Fp fixtures
pass; source agent continues logical semantic extraction.

Native `e5a076b1` proves actual accepted input→prepClaim success (from decoded
walk outputs), completing the preparation path with prior body proof;5 guards
pass. Remaining full semantic constructor work includes reconstructed D0Shape
and amendment preservation. Ups checked all12 constructor scalar families and
actual value-terminal byte+memory dispatch (`fef53f5f`), but then found a real
trace metadata bug: leaf replacement terminal matched=0 should be key.length.
Agent is fixing this with root-leaf[0,15] regression; do not claim whole dispatch
complete until corrected and integrated.


**Continuation after the 1,403-job checkpoint:** queue field traffic is closed
for generated records (`79aef84e`, AIR `8b081577`):35 exact axiom guards and six
behavior checks. The contract covers canonical VBYTES, QVC provider pairs,
QSH shard bytes/counts and silence elsewhere. Ownership, native capacity, read
orchestration and reverse extraction remain open.

Source physical completeness and endpoint repair are committed (`73d71160`,
`f6ed261c`): the right terminal row is explicitly inactive, preventing a cyclic
carry row from suppressing terminal constraints.49 partition guards plus four
endpoint regressions pass; current source size remains8,359,074 bytes, margin
29,534. The source agent is proving reverse partition composition.

Root introduced an isolated log23 protocol candidate (`1ebd1a62`, AIR `c44fbd87`),
with executable candidate verifier, height/public/header checks, log27 LDE and
27-bit positions, query dominance for every domain log8–27, and the actual BCS
numerical budget.21 exact axiom guards and eight kernel regressions pass. The
round/RBR/ROM/admission chain is still open; no frozen protocol/pin was changed.
See `docs/zk-formal/LOG23-CANDIDATE.md` in the QV/AIR worktrees.

Native assembly now derives the complete constructed-witness size from accepted
raw size, actual scheduler grants≤4,500,000 and forwarding demand bounds with
no assumed replay/cap (`94d89dc9`). Native preparation body/header composition
passes (`925917f4`); accepted native bytes→prepClaim existence remains open.
Ups runtime assembly now derives every emitted part output.memD<2^74, allowing
native u64 overflow; total signed carry-input bounds and ancestor memory
propagation are checked (`e5fa8dc8`, `12f69c13`, `7912ac7d`).

The newer aggregate is AIR `18ca4f17`:1,531 jobs PASS,13 focused audits,141
axiom guards,six behavior guards and12 kernel theorem regressions. Report:
`docs/e2e-results/v3-native-traffic-log23-integration/report.json` in AIR.
External evidence: `/data/illia/nearproof-deps/validation/v3-native-traffic-log23-20261007/`.
The older1,403-job result below is retained as a historical checkpoint.


**Newest shared checkpoint: AIR `96944b6b`, 1,403 jobs PASS.** Full-u32
Node/Ups header repair and width200 carry arithmetic are merged and integrated.
Twelve merged audits pass:86 axiom guards,38 behavior guards, plus theorem
regressions for header aliasing and long-key carry truncation. Evidence:
`docs/e2e-results/v3-full-header-integration/report.json` in the AIR worktree.
V3Synth/V3Eval/AlignedModel now match the actual wider table; source candidate
`03f6fcce` kernel-checks wired/reserved8,359,074 bytes, leaving29,534 under8MiB.
This model still reserves unimplemented queue orchestration and is not admitted.

Queue `a90ccba7` proves all local constraints of complete concatenated executable
records, including boundaries/padding/physical wrap. Latest isolated `e12078bb`
adds the actual field TableLocal interface, exact byte traffic concatenation,
and exact rows=bytes+empty-value-markers. Record audit16 axioms+6 behavior guards;
standalone audit28 axioms+22 behavior guards. Global field traffic, read
orchestration, sound extraction and actual accepted-witness capacity remain open.

Native factoring now has exact decoded-witness/store nonexpansion, globally
allocated forest stores, native ID capacity, actual chronological execution,
and concrete main/implicit execution views (`602a1513`, merged AIR `efb0e186`).
These additions after the1,403 checkpoint have focused audits, not a newer
aggregate. Source dictionary mapping preserves unused fillers. Whole GoodV3
construction/FactorComplete remains open.

Upsert runtime assembly is active in additive modules. Actual partialTrie input
bounds emitted parts≤403; encoding totality, runtime metadata and initial
per-kind dispatch are proved. `f91d292c` (merged AIR `987aeb48`) fixes an overly
strong MemOk convenience premise to native modulo2^64 semantics; a checked
native overflow fixture shows exact output memory2^64+103 but serialized103.
This is a native upsert fixture, not a whole-checkD0a witness. Core carry/MEMD
constraints already support overflow. Full native trace/window/traffic remains
open. Source agent is composing logical and physical partition TableLocal.

All older checkpoints below are superseded where this update differs. Final
succinct prover/certificate/judge and broader NEAR coverage remain unfinished;
mandatory reference lean4lean admission still fails. Frozen parameters and caps
remain unchanged.


**Latest aggregate: AIR `b47ed83f`, 1,347 jobs PASS.** This includes exact
first-match native-store normalization and its executable tree-view bridge,
with 17 store axiom guards, two collision-order regressions, and three
FactorSound guards. Subsequent Assembly additions have their own passing
focused audits but have not yet been included in a newer aggregate checkpoint:
actual decoded witness re-encoding does not grow; normalized stores preserve
the exact partial trie and actual runtime; native main execution is extracted;
and shared forest allocation reconstructs each instance's normalized store.
FactorComplete still needs capacity and remaining native fields.

Queue candidate `1f744100` (merged AIR through `20687f96`) proves all local
constraints for all three parser modes at arbitrary fitting heights, including
padding and executable-generator bridges. Its audit has 28 axiom guards and
11 fixtures in each of integer/field arithmetic. Root is proving record gluing;
read orchestration, sound extraction, and actual global capacity remain open.

Source `37dfbb04` proves its deduplicated SIZE charge stays within the actual
unchanged 8 MiB raw-witness bound, preserving unused dictionary fillers.
Full logical five-bus traffic and exact traffic across overlapping partitions
are proved; full local legality and protocol admission remain open. The cost
model including full-row source carry, reserved combined queue width52, and
Ups width200 is **8,359,074 bytes**, leaving29,534 bytes. This remains a candidate
model; final wiring and protocol/security admission are not established.

The isolated HPL repair has checked full-u32 Node encoding and Ups byte/header
constraints. The carry counterexample requires widened memory carry: checkpoint
`0ae875e0` checks width200, unchanged interactions/degree, full cMem rendering
and extraction. Direct/moved header consumers are checked; split/shape consumers
remain in progress. Do not merge the isolated HPL lane as complete yet.

Reference lean4lean admission remains FAIL. Proof-only factoring experiments
did not solve the E_exec recursion failure; canonical upstream-derived proof
sources were restored, with diagnostic evidence retained. No checker limit was
relaxed. Frozen parameters, raw/proof caps, and accepted domain are unchanged.

The paragraphs below are historical checkpoints where superseded by this one.


**Newest aggregate: AIR `f0da580b` passes 1,337 jobs with proved FactorSound.**
`GoodV3.checkD0`, `GoodV3.checkD0a`, and `factorSound` imply unchanged native
checker acceptance from explicit semantic fields. Three permanent axiom guards
pass; evidence is `docs/e2e-results/v3-factor-sound/report.json`. FactorComplete,
AIR-to-Good and the final succinct prover/certificate remain open.

Queue candidate `1e2da6c2` now proves arbitrary raw-value local constraints,
including empty markers/padding and actual generated trace equality. Buffered
row count/indexing/padding and generator identity are proved, along with u32
header reconstruction; buffered local validity is next. Fourteen axiom guards
and eleven fixtures in both arithmetic models pass. HPL helper is copied exactly
from `60ebdf40`; full HPL repair remains isolated on `lane/v3-hpl` (Node checkpoint
`5a5183d6`, Ups pending). Source `820b58bf` has actual57-column/122-constraint
candidate local duplicate proofs and field row traffic, with partition/security
admission still open. Current size estimate with reserved queue controls is
8,326,114 bytes before carry/wiring, only62,494 below8MiB; this is not an admitted
proof bound.

Reference post-split public and held-out SDK reproducibility/mutation gates pass
(two clean builds each); held-out1433 mutations all rejected. Formal admission
remains FAIL on independent lean4lean recursion, with proof-only repair ongoing.



**Latest coverage and capacity findings (supersede estimates below):**

* Upsert `a0ad83a1` kernel-checks an accepted 305-byte node with a 510-nibble
  leaf key whose HPL header is `[0,1,0,0]`. The old one-byte header assumptions
  are false on the accepted domain. Full-u32 Node/Ups repair is isolated on
  `lane/v3-hpl`; no domain restriction is authorized or introduced.
* Source candidate `9feacb8b` derives deduplicated renderer bounds from actual
  RelD0a/raw decoding: 16,334,272 rows, 16,332,288 preimage bytes, 8,932,712 SHA
  rows, and 256,184 computed messages. Local AIR validity and authenticated
  partition continuation remain open.
* The promising two-source/two-SHA log23 size model is NOT admitted: current
  Table.wf hardcodes log≤22. Four log22 partitions exceed 8 MiB before complete
  queue/wiring costs. A separately proved candidate protocol family is required;
  active limits and frozen parameters remain unchanged.
* Queue candidate `e2e270a0` proves exact generated byte/shard traffic and all
  empty-index local constraints, including the bridge to actual generated rows.
  Raw/buffer general validity, extraction, and walk orchestration remain open.
* Post-split D3 native reproducibility passes twice with identical artifact.
  Formal leanchecker and nanoda accept the closure, but mandatory lean4lean
  fails on E_exec recursion depth. Proof-only factoring compiles and its
  independent recheck is pending. Formal admission is still FAIL, not PASS.

Additional completeness obligation: reconstructing an equivalent unfolded trie is
not enough to establish the original 8 MiB encoded-witness guard. FactorComplete
must preserve/reuse original serialized store records or prove nonexpansion of
the selected view allocation. Its arbitrary unfolded-byte parameter B does not
by itself supply this bound. Keep this separate from semantic reconstruction.

Parallel ownership: root queue candidate/integration; ups_fields full-u32 HPL;
receipt_gap source dedup AIR/partition proofs; d2_validation semantic factoring
and reference gates. Continue through full factoring, concrete AIR, honest
completeness, succinct Rust prover, and final certificate/judge. No succinct
replacement has yet been established.


**Newest aggregate: AIR integration passes 1,329 jobs**, adding the actual
witness constructor and explicit GoodV3/Execution interfaces. Both factoring
directions remain OPEN proposition types; they are not axioms or proved claims.
The prior 1,323 checkpoint (`7c3e3997`) includes all 12 upsert byte constructors
and exact queue semantics. Queue read-request work adds checked identifier and
count bounds; current semantic audit has 11 behavior checks and 38 axiom guards.

Root's isolated queue candidate is `fd20afa7` on `lane/v3-qvals`: a 37-column,
97-constraint parser, kernel-checked static g2 shape `(37,3,6,3,22)` and degree4
well-formedness. Eleven fixtures pass both integer and BabyBear evaluation.
Read orchestration, general field extraction/honest renderer and actual row
capacity remain open. Candidate bus63/QSH byte schema is isolated. See its
`docs/zk-formal/QV-CANDIDATE.md`; active caps/parameters have not changed.

Receipt candidate `d8e34347` now derives the deduplicated path bound directly
from actual accepted raw witness bytes; `78037b64` derives source count≤1984
from successful preprocessing. `ca8bcdff` adds repetition/root semantics for a
low-width skip-repeated-source proposal; real validator source-loop extraction
is active. Upsert now has unconditional runtime trace erasure and actual part
plan, node encoding/root hash bridges, and nine runtime-to-ByteInput bridges;
sparse branch bridges continue. Final all-constraint completeness remains open.

The reference formal gate found an inadmissible proof-only Lean import in the
model closure. D3 fixed the runtime/proof split at `2d8e3588`; 26 model modules,
69 proof modules and 25 axiom guards pass. Fresh native reproducibility and
hostile/formal gates are rerunning because the binary digest changes. Earlier
native passes refer to the pre-split artifact. TTN has five passing fresh
configurations and continues; no general succinct replacement exists yet.


**Current checkpoint superseding the historical entries below:** AIR `c325f2e1`
passes 1,272 integration jobs. Public `Bindings.bindPrepared` now derives all nine
record families, root endpoints, header reads and fit from actual preprocessing
and explicit size bounds. Public audit: 24 behavior checks and 31 axiom guards.
The final AIR, honest witness, succinct prover and certificate remain incomplete.

Root now owns isolated `/data/illia/nearproof-wt/v3-qvals`, branch `lane/v3-qvals`.
Commits `c2cbd6d4`, `23104328`, `0282660c`, `5126a756` prove exact queue encodings,
actual runtime queue-read extraction, group-read completeness, exact buffered
byte counts, and preservation of buffered/group reads across scheduler upserts.
11 behavior checks and 20 axiom guards pass. Yield reads still need preservation
across receipt writes; no queue AIR table exists yet. The old design's A4 128 KiB
queue cap is absent from actual RelD0a and MUST NOT be assumed.

Receipt source hash linkage and actual decoded path widths now have checked
lemmas. A real capacity gap remains: the 8 MiB witness cap does not imply the
current source table's 2^20 row cap, and replaying repeated proofs can overflow
field identifiers. Receipt agent is evaluating proof deduplication/partitioning
in isolation; no active caps or domain restrictions have changed. A preliminary
dedup partition size estimate is tight against the 8 MiB proof cap and does not
yet include all extra wiring or queue tables.

Upsert byte constructors cover 11 of 12 kinds; SPB's seven subcases are active.
D3 reference passed public check-local including byte-identical clean builds,
407 positives, and generic hostile checks. Strict public checks passed 651 cases
and 3,062 worker mutations; held-out strict checks passed 272 cases and 1,433
worker mutations. These validate the reference, not succinct proof replacement.
Configured formal reference admission is running; fresh TTN has four passing
configurations and continues. Assembly agent is implementing ExtV3/GoodV3 and
actual relation factoring without assuming the desired equivalence.

Current parallel plan: root completes queue semantics/preservation and AIR;
upsert agent completes actual constructors; receipt agent resolves source capacity
and dedup semantics; D3 agent completes reference gates and whole assembly.
Then assemble the concrete AIR, prove both factoring directions and honest-trace
completeness, implement the succinct prover, and run the actual certificate/judge.
Broader NEAR coverage remains required beyond the restricted D0a milestone.

**Latest aggregate checkpoint: AIR `c2dba0c4` passes 1,259 integration jobs.**
The honest source renderer now has both `SrcpGen.table_local` (112 constraints,
all multiplicity bits) and `SrcpGen.table_traffic` (`c11a5c8d`), with 86 receipt
axiom guards. Full upsert `cBytes_ok` covers all 76 constraints (`9ab95e1a`);
actual node-form input constructors now cover seven of twelve kinds through
`2c2249e7`, with the remaining cases active. These conditional/local theorems
are not yet full honest-trace completeness.

R2 concrete public packing is implemented in the public lane and merged through
AIR `94ec591e`: a 202-byte header and nine fixed segments, exact source/body/
boundary records, all widths, overall-size-derived count/offset bounds, `pubFit`,
and concrete `PubIdx`. All four scheduler record lists are proved exact from
successful `prepD0`; no scheduler byte-range assumption remains. The checkpoint
passes 24 behavior checks and 24 axiom guards. Evidence is in
`docs/e2e-results/v3-packed-public/report.json` in AIR and the matching validation
archive. Root is extending this with exact root endpoints, all receipt record
families, header reads, and a bundled `Public.Bindings` interface.

D3 agent additionally owns isolated `/data/illia/nearproof-wt/v3-assembly`, branch
`lane/v3-assembly`, based on AIR `7aba6ec8`. Commits `04c8bdf8` and `a1b2d7be`
prove operational scheduler/public-core factoring and actual prep-derived header
root widths, source-root widths, and `sched.length = K+1`. Those commits are now
in the public worktree (`72f79746`, `0e9c7308`); not yet merged to AIR. D3 native
reference has passed its first clean build and is in the second reproducibility
build; worker mutation/formal gates remain pending. TTN remains running.

Next parallel tasks: root completes all prepared-public bindings and merges
assembly facts; receipt agent links SHA contracts using proved disjoint source-ID
intervals; upsert agent constructs remaining edit cases; D3/assembly agent
continues actual relation factoring and reference validation. Keep final
FactorSound/FactorComplete, complete AIR/honest trace, Rust succinct prover,
certificate/judge validation, and broader NEAR coverage explicitly open.


**Latest parallel checkpoint:** R1 indexed-public protocol passed 1,168 integration
jobs and is merged to AIR as `a1215d2e` (public lane `0de153cf`); 14 behavior
checks and five axiom guards pass. Prefixes, generated indices, and dynamic
payload offsets are supported, but concrete NEAR prepared-statement bindings
remain R2 work. Root's public lane has checked byte/packing/payload/layout
lemmas; exact record binding is in progress under `NearV3/Public/`.

The clean snapshot diagnostic ended at its 1,800-second total cutoff: 927 of
1,110 modules passed, and `Render.Ups.GRows` was interrupted. There was no prior
proof failure. Results are in the attempt2 directory named below. This broad
integration closure is not the final certificate; final closure pruning and
checker timing remain necessary. Its heavy scope has been released to D3.

D3 checkpoint `2d9d4e58` wires the read-set model and admission certificate;
25 axiom guards pass. Long native/check-local/formal and worker mutation gates
are next. TTN has two fresh passing configurations, including v1-s1-o300
(236 chunks, 667 calls, 65 expected failures, 635 charged calls); suite continues.
AIR byte completeness has reached 74/76 at `54500db2`. Receipt rendering has
92/112 constraints checked at `3c16b628`, with transitions actively compiling.
These are intermediate milestones, not a succinct validator replacement.


**New checkpoint (after the earlier summary below):** AIR `5e084a5c` passes
1,167 integration jobs. All 29 memory constraints are complete (`ac76c7a8`),
with 24 axiom guards after `memOk_of_semantics`: encoded carry ranges and memory
bytes now follow from ordinary node/scalar semantics and operand bounds.
All 62 field constraints and 62/76 byte constraints are integrated; the field
agent has since reached 68/76 (`3892ab08`). Full `srcp_view` is closed; honest
source generation, capacity, adjacency, SIZE and 33 polynomial constraints
are checked through `3bc8d369`, with remaining renderer work active.
Evidence: lane `docs/e2e-results/v3-memory-complete/report.json` and
`v3-memory-semantics/report.json`. This is not yet validator replacement.

Root is implementing R1 indexed public records in isolated branch
`lane/v3-public`, worktree `/data/illia/nearproof-wt/v3-public`, based on
`5e084a5c`. Protocol edits are not merged until tested. Its builds use the same
AIR lock. An isolated serial clean elaboration diagnostic is running under
`/data/illia/nearproof-deps/validation/v3-clean-elaboration-20261007-attempt2`;
first attempt stopped on an omitted toy-spec snapshot dependency, not a proof
failure. It uses fresh candidate outputs, copied trusted oleans, a 1,800 s total
cutoff and 300 s/module, and is not an actual judge admission.

D3 checkpoints `078eb032` and `3bb5020f` add candidate-local logged reference
foundations, exact hash-filtered storage and encoding proofs with 14 axiom
guards. Re-encoding control-flow simulation is still open; deployed Model is
unchanged. TTN's first fresh run passed (236 chunks/633 calls); the 26-run suite
is still active and may take hours. While clean timing uses the second D3
scope, bounded D3 proof diagnostics may queue behind the AIR flock (one queued
job, source stable) to remain within three 16 GiB heavy scopes globally.

The user explicitly authorized subagents. Three independent tracks are active:
D3 regression/reference work, update-field completeness, and receipt/source-proof
extraction. The lead owns memory completeness and integration. AIR builds and
audits now use an exclusive lock to avoid shared-artifact races:
`taskset -c 8-15,24-31 flock /data/illia/nearproof-deps/validation/v3-air-build.lock /data/illia/nearproof-deps/bin/heavy lake ...`
with `HEAVY_MEM=16G LEAN_NUM_THREADS=4`, from the lane's `zk-formal` directory.
Keep each queued target's source stable until completion.

- **D3 lane:** D2 exact original/logged comparison passes all 67,384 cases,
  and fresh Python agrees with logged Lean and nearcore metadata throughout.
  On the 53,048-case D1 corpus, original/logged D2 agrees exactly; independent
  Python D2 agrees throughout, all 11,089 expected D1 positives are accepted,
  and no nearcore-rejected case is accepted. This checks D2 on the D1 corpus;
  it does not conflate the two domains. See lane evidence reports.
- **WASM gate:** at D3 commit `4416cfb3`, all 14,621 generated cases have exact
  original/logged outcomes. Fresh pinned nearcore agrees on all 14,610 in-domain
  cases; 11 out-of-domain cases remain explicitly covered by parity. The logged
  harness adapters build (143 jobs), and process/output framing is fail-closed.
  TTN harness rebuilding and trace regeneration are next, followed by the exact
  logged read-set reference and unread-value/code injection checks. Existing
  Canon uses necessity iteration; a logged import alone does not prove witness
  reconstruction preserves control flow. No pinned trusted source was changed.
- **AIR lane:** integration at lead commit `036d5467` passes 1,119 jobs.
  Seven concrete aligned generators were previously added. `cPlan_ok` now
  closes the full update-plan group from explicit semantic `PartOk` inputs.
  `GFieldPrefix` covers the first 26 actual field constraints. `MemArith` and
  `GMemRow` cover signed carries and encoded memory-row equations, including
  exact high limbs; all 15 memory axiom guards pass with only `propext` and
  `Quot.sound`. Carry ranges/result bytes, register shifts and full memory
  dispatch still need closure from actual update construction.
- **Source proofs:** root/leaf units, complete path-item traffic, nonwrapping
  counters, exact unique SIZE emission and its field-valued sum, and a semantic
  SHA-contract bridge to receipt verification are proved. Whole-block assembly,
  SHA bus-contract discharge and the honest render remain open. The selected
  new B2 block explains nonempty source lists even when there are no receipts.
  Full `prepClaim` success decomposition remains required. Receipt guards: 28.
- **Evidence:** AIR `docs/e2e-results/v3-parallel-proof/report.json` and
  `/data/illia/nearproof-deps/validation/v3-parallel-proof-20261007`.
  These are incremental checks, not a clean 1,800-second judge measurement or
  a completed succinct state-transition prover. Subsequent agent commits/WIP
  may be ahead of this integration checkpoint; inspect before restarting work.


Main is `048fc45d`; the D0a spec merge is already present. Treat the older lane
status files' requests to merge it, and their receipt-lane pause claims, as stale.
Work proceeds in the following order, retaining the release gates below:

1. **Restore checked baselines.** Build `ZkFormal` on `lane/v3-air`, then repair
   `Logged/WasmRun.lean` on `lane/v3-d3` and rebuild the logged checker. Check the
   transitive theorem axioms and reproduce the formerly stack-overflowing case.
2. **Validate the logged reference.** Run all D3 corpora and the D2/D1/D0
   regressions, WASM harness and trie traces. Implement the exact read-set normal
   form in the D3 reference and run check-local, including unread-value/code
   injection. Record full-case counts and missing results as failures.
3. **Finish the succinct prover.** Resume receipt proofs; finish trie/scheduler
   completeness, indexed public segments, roll-in alignment, assembly and the
   Rust v2 prover. Keep B0 at 2,000,000 and the existing proof-size cap; prove
   the size savings before relying on them. Measure clean elaboration and real
   judge verification before declaring admission feasible.
4. **Resolve domain choices before freezing.** The ChaCha word bound and source
   Merkle-path budget remain user decisions. Until resolved, keep capacity
   statements conditional and do not freeze a newly narrowed domain.
5. **Release only after the gates pass.** Add D0a to the unified tier ladder,
   merge tested lanes, freeze once, measure the paired baseline in a logged w1
   window, then sign/register/deploy and verify reference admission and hostile
   rejection. Preserve signed challenges and all existing pinned files.

Recovery completed on the two lanes (not merged to main):
`lane/v3-d3` at `77b844e0`; `lane/v3-air` at `d455885a`.
* **D3:** repaired and kernel-checked the stack-safe logged loop; built the
  checker and D0a tier (195 jobs). All 115,284 D3 cases agree with the saved
  original Lean and independent Python baselines and nearcore expectations;
  all 1,720 public-fixture comparisons agree in verdict and reason. Saved
  baselines were reused, not rerun. Eight guarded axiom audits and seven
  regression-driver tests pass. Full D1/D2 corpora, WASM/trie harnesses and the
  read-set reference remain next. Evidence: lane file
  `docs/e2e-results/v3-logged-checker/report.json`.
* **AIR:** merged the saved receipt lane at `8c40110e`. The default `ZkFormal`
  root missed hundreds of proof modules. New target
  `lake build ZkFormal.V3.Integration` covers 369 additional modules and passes
  all 1,089 jobs. It exposed and fixed a stale upsV3 width (186 → 187), adding
  928 bytes to each synthetic size bound. Kernel checks now compare all trie,
  scheduler and receipt shapes; seven guarded axiom audits pass. This is an
  incremental integration check, not a clean judge-budget measurement or a
  completed STARK. Evidence: lane file `docs/e2e-results/v3-integration/report.json`.
* **Domain:** the conditional W = 770,000 capacity theorem needs ChaCha
  maxLog 22 (4,141,411 padded rows), whereas the current table uses 21.
  The W and source-path choices remain unanswered; no domain or cap changed.
* Full validation artifacts are preserved at
  `/data/illia/nearproof-deps/validation/v3-recovery-20261007-023334`.
  No live worker was stopped, and no challenge was frozen, signed or deployed.

### Active end condition and alignment milestone

The user clarified: continue until a succinct NEAR state-transition proof can
replace stateless validator verification. Restricted D0a admission is an
intermediate milestone, not evidence of full transition coverage.

The AIR lane now proves the actual FRI schedule's conditional aligned-size
bound and an admission interface requiring the size bound only on honest
trace headers. Its integration target passes 1,092 jobs; six guarded axiom
checks pass. The proposed padded two-SHA model is 6,164,160 bytes, leaving
929,431 bytes after the maximum hint under 8 MiB. qvV3 and the actual padding
construction remain missing. See the AIR lane's
`docs/e2e-results/v3-alignment/report.json` and `Size/Aligned*.lean` /
`Size/HonestAdmission.lean`. Next: construct padding preserving HoldsP,
finish missing tables/proofs, and instantiate the full admission certificate.

A fresh original-vs-logged full D2 comparison (67,384 cases) is running with
outputs at `/data/illia/nearproof-deps/validation/v3-d2-logged-20261007`.
Inspect its `summary.json` before starting another run. It is not yet a pass.

## 0. Goal and standing user directives

**Goal.** A self-hostable arena where candidates submit NEAR state-transition provers. Each submission comes with a machine-checked Lean certificate. The judge independently builds the submission, checks it formally (fixed trusted root), tests it, and benchmarks it.

**Current target.** A **succinct proof of a NEAR chunk state transition, with a formal proof of correctness.** It must be a drop-in replacement for the stateless validator's `validate_chunk_state_witness`.

User directives (binding):
* **Don't shortcut.**
  * Use explicit, decidable domain conditions rather than hidden assumptions.
  * Prove things where possible; don't settle for testing alone.
  * Never loosen measurement rules to make something pass.
* **Proof size and verify time are first-class.** Proofs must be succinct.
* **One challenge.** `near-chunk-v3` covers the whole chunk transition with coverage tiers D0a < D0 < D1 < D2 < D3α. Do not create one challenge per domain.
* **The strategic value of ZK** is one proof across *all* shards, which standard validator hardware cannot re-execute. Single-proof capacity (`G_α`) is the key metric.
* **Recursion: R5.** No proof composition and no bounded R1. Single-proof capacity is raised through the prover, table and verifier levers listed in `docs/requirements/D3_WASM_REQUIREMENTS.md` §2.4.
* **Decisions already taken by the user:**
  * Price model: N_v = 50 validators **per shard**.
  * B0 = 2.0 MB for D0a.
  * A8 is in RelD0a.
  * D3 error kinds count as one failure; floats come in a later stage; block facts are derived from headers.
* **Security and operations:**
  * Repo: GitHub `ilblackdragon/near-proof-arena`, private.
  * Remote access is through `tailscale serve` only, never funnel. Everything binds to loopback.
  * Keys and secrets live outside the repo. Never print keys, env files or env vars.
  * Never modify signed challenges (`challenges/chl_*.json`), the frozen `oracle/v3`, or any pinned file. `make pin-check` must pass.

## 1. Host rules (the host OOM-crashed twice; follow these strictly)

* **Run heavy builds through the wrapper:** `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy <cmd>`.
  * The wrapper is a systemd scope in `zkbuild.slice` with a 48G cap, and `mem-watchdog` runs alongside.
  * Use `HEAVY_MEM=32G` only for the D2 kernel-eval proofs.
  * At most about 3 lanes, and at most 2 heavy builds per lane at a time.
* **CPUs 0-7 and 16-23 are reserved for the live benchmark worker w1.**
  * Stop w1 only in short, logged windows with an empty queue (`docs/LIVE.md` §5f).
  * If a run is interrupted, restart w1.
* **Disk:** `/` is at **96%** and `/data` at **92%**.
  * Delete merged worktrees and their `target/` dirs.
  * Session scratchpads under `/tmp/claude-1002/...` are large (`lean`, `npai-e2e`, `elan` ≈ 25 GB) and can go once you have confirmed nothing needs them.
* **Merging:**
  * Use explicit `git add <paths>` only; other agents work in worktrees. Check `git status` before committing.
  * Merge lanes to main **before** installing live.
  * Run `cargo fmt --check`, clippy with `-D warnings`, the affected tests and `make pin-check` before pushing.
  * Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
* **Worktrees:** lanes live in `/data/illia/nearproof-wt/<lane>`, one per concurrent agent. Never share a worktree between agents.
* **Helper:** `/data/illia/nearproof-deps/bin/resolve-members.py` resolves `Cargo.toml` member conflicts.

## 2. What is DONE (on main, `5ce7c42e`)

* **v1 arena: milestones A–D complete and live.**
  * Firecracker sandboxing, a formal checker with three kernel rechecks and audits, the hostile suite and signed reports.
  * The NPAI (CHECKED) and native-lean routes.
  * Succinct STARK np-udr-stark (L1–L8), formally admitted. It is a validity proof, **not** zero-knowledge.
* **Live instance (`docs/LIVE.md`).**
  * Runs from `/data/illia/nearproof-live` as systemd user units `arena-live.target`.
  * Reachable over the tailnet at `https://ns1027125.tail4c1391.ts.net`.
  * Deploy only with `arena-live build` followed by `arena-live install`. Install refuses stale or dirty builds.
  * The calibration binary at `bin/arena-calibrate` is not copied by install; keep it in place.
* **Cost scoring.**
  * Governed price model `pm-near-mainnet-2026q4@v2`.
  * Paired baseline control and a pinned calibration binary (bench-spec-v1.6, contracts v1.8).
  * Verify time is scored as the lower quartile of 25 runs.
  * The v1-7 challenge `chl_93d98910…` has a live cost board.
* **v3 D0.**
  * Challenge `chl_4b431651…`, speed-scored.
  * The proven normal-form reference (4.5) and its fast prover-only child (104.6, rank 1) are ADMITTED.
  * The old canonical-only reference has been re-run and is now REJECTED.
* **v3 spec ladder.** Each domain was difftested three ways: nearcore vs Lean vs independent Python.

  | Domain | Cases | Disagreements |
  |---|---|---|
  | D1 | 53,048 | 0 |
  | D2 | 67,384 | 0 |
  | D3α (WASM, `G_α` = 3.45 Tgas) | 115,284 | 0 |

* **RelD0a** (B0 = 2.0 MB, A1/A2/canon0f/A7/A8) and `relD0a_relD0`: merged at `5ce7c42e`. Spec: `spec/near-chunk-validation-v0a.md`.
* **Research closed:** recursion (`docs/research/recursion-summary.md`, R5). The cross-shard plan is in `docs/BENCHMARK_SPEC.md` §14.11.

## 3. Stream A: unified challenge `near-chunk-v3`

Branch `lane/v3-d3`, worktree `nearproof-wt/v3-d3`. **Read `STATUS-V3-D3.md` at the lane root.**

**Recovery builds and audits pass.** The open `runUntil_spec` goals and long-run stack overflow are fixed; see the resumption evidence above.

* **Design.**
  * Statement: `RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3`, with `rel_mono` and `sound_lift`.
  * Candidates declare a tier and may abstain with UNSUPPORTED (prove exit code 3). Ranking is by tier, then cost.
  * Documented in `docs/CONTRACTS.md` §11 (contracts v1.7+) and `docs/BENCHMARK_SPEC.md` §17.
  * The coverage code is on main.
  * Draft: `challenges/drafts/near-chunk-v3.draft.json` on the lane, unsigned id `chl_b44dc871…`. Class weights are **ASSUMED** until a mainnet replay measures them.
* **Known limitation.** The union statement means four transcriptions are trusted. The follow-up for a successor version is to define `Rel_Dk := RelD3 ∧ InDk`, so the statement can be `RelD3` alone.

Remaining, in order:
1. **Read-logging refactor.** `checkD2L_eq` and `checkD3L_eq` are already proved; the logged run equals the trusted checker.
   * Completed: close the loop proof and validate the tail-recursive executable.
2. **Re-run every regression with the logged checker:**
   * Completed: D3 three-way on all four corpora;
   * D2 and D1 full corpora remain; D0/D1/D2 public fixtures pass;
   * the WASM harness and trie-accounting traces.
3. **Rebuild the D3α reference `examples/reexec-v3-d3` on the read-set normal form.**
   * base_state must be exactly the logged read set, and verify must accept only those bytes.
   * Run check-local, including the `values/inject-unread` and `codes/inject-unread` mutators.
4. **D0a formal tier is added and builds.** Draft activation still needs checked workload-class coverage and final domain bounds; an empty class list would silently allow abstention on every input.
5. **Re-freeze the trusted tree once**, covering the logged spec and RelD0a.
6. **Run the joint w1 cost-baseline window** for the paired-mode draft. The procedure is in `docs/LIVE.md` §5f and BENCHMARK_SPEC §14.
7. **Release and record.**
   * Sign with the local operator tooling (never print key material), register, and deploy.
   * Submit the reference (expect ADMITTED) and the hostile case `near-v3-d3-lenient-codes` (expect REJECTED).
   * Record the results in `docs/LIVE.md` and `docs/e2e-results/`.

Corpora have been **moved to `/data/illia/nearproof-deps/corpora/`**: `d3c7`, `d3c8`, `d3c9`, `d3c10`, `d2corpus.v2`, `d1run`. The STATUS file still lists the old scratchpad paths. Regeneration commands are in STATUS-V3-D3 §5.

Open nearcore findings and spec ambiguities: STATUS-V3-D3 §6, and `oracle/tools/README-d3.md`.

## 4. Stream B: succinct D0a STARK (np-udr-stark-v2), the critical path

Integration branch `lane/v3-air`, which also carries 13 sub-lane branches. **Read `STATUS-V3-AIR.md` at the lane root.** Design: `docs/zk-formal/V3-D0-DESIGN.md`.

Integration gate: `lake build ZkFormal.V3.Integration` on `lane/v3-air`, now passing. Use this target rather than the incomplete historical root. Next: finish completeness and indexed public segments, then assemble the real AIR and size proof.

* **Proved:**
  * the v2 protocol: public bus, auxGroup and admission;
  * size lever (a), a dedup bound;
  * ChaCha20 tables, sound and complete;
  * trie soundness, through `upsV3_linkB`;
  * scheduler soundness;
  * spec D0a.
* **Partial:**
  * trie completeness: the upsV3 render, M7d;
  * scheduler completeness: M4;
  * the receipt side (rcpt, srcp, qv).
* **Not started:**
  * indexed public segments (R1);
  * assembly: `nearAirV3`, FactorSound and FactorComplete, `honestTrace_fits`, and the certificate;
  * the Rust prover v2;
  * timing of a real judge run.
* **Branches that don't build (WIP):**
  * `lane/v3-trie-h` `1d8b2f12`;
  * `lane/v3-rcpt-h` `4ae51a13`.
* **Correction:** the status file says the receipt lane was "paused by the user". It was not; it stopped only because of a usage-limit interruption. Resume it, since it is on the critical path.
* **Elaboration-budget risk:** v1 alone uses 647 s of the 1,800 s budget, and the v3 additions are large. Measure early.

**Decisions to bring to the user** (STATUS-V3-AIR §5):
1. **Size cap.** With two SHA tables at B0 = 2.0 MB, the bound is about 150 KB over 8 MiB. One SHA table only fits if B0 ≤ about 1.95 MB.
   * Recommendation: lever (1), roll-in alignment, which saves about 1.6 MB.
2. **ChaCha words bound W in RelD0a.** Options are 360k or 770k.
   * It is not a deterministic nearcore invariant, so it carries a liveness note like A7's.
   * If it is approved, add it before the near-chunk-v3 freeze.
3. **Receipt lane edits to PrepD0.lean** (unsigned).
4. **Source-proof Merkle path length.** Bound it as a domain conjunct, or count it in a budget.

Cost-model levers to keep in mind: compact refund codec (about −0.45 MB), width cuts.

## 5. Stream C: cost scoring (done; one task left)

The work is merged and deployed (see §2). The only thing left is the joint near-chunk-v3 baseline window (§3 step 6).

Known issue: per-class verify time varies a lot between inputs. The paired mode already handles this; the speed-scored boards are not paired.

## 6. Smaller follow-ups

* **Succinct badge.** Max proof bytes, max verify time, and a log-log check that neither grows with gas. Proposed values: 2 MiB / 50 ms. Display only; not implemented.
* **Mainnet replay.** Real chunks would provide real class weights and a measured `G_α` (rows per WASM op). The current `G_α` is a checkpoint value.
* **Re-check the D3 spec on the clean-room Python VM.** That VM was tuned against nearcore black-box runs, so it is not fully independent.
* **Future challenge: 1 Pgas in a single STARK, without recursion.** Not started; the user prioritised finishing v3.
  * It needs a field with larger 2-adicity, e.g. Goldilocks with 2^32.
  * It needs a distributed prover.
  * It needs dedicated precompile tables.
* **Future challenge: cross-shard, whole-block proof.** Documented in BENCHMARK_SPEC §14.11.
* **Old worktrees.** About 100 merged lanes under `nearproof-wt/` can be removed with `git worktree remove` once you have checked each one is clean and merged, to free disk.

## 7. Key documents

| Topic | Documents |
|---|---|
| Architecture and contracts | `ARCHITECTURE.md`, `CONTRACTS.md`, `CHANGELOG-contracts.md` |
| Security model | `TCB.md`, `THREAT_MODEL.md`, `SECURITY_POLICY.md` |
| Benchmarking and operation | `BENCHMARK_SPEC.md`, `LIVE.md` |
| v3 domain specs | `spec/near-chunk-validation-{d0,v0a,d1,d2,d3}.md` |
| Requirements | `docs/requirements/` |
| ZK formalisation | `docs/zk-formal/` (DESIGN, STATUS-L*, V3-D0-DESIGN) |
| Audits and reviews | `UNTRUSTED_NEAR_ZK_AUDIT_2026-10-05.md`, `reviews/D3_REVIEW_2026-10-06.md` |
