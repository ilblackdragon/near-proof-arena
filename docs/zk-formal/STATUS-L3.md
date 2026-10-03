# STATUS — lane L3 (IOP math, unique-decoding regime)

Package `zk-formal/`, namespace `ZkFormal.Udr`, files `zk-formal/ZkFormal/Udr/*`.
Statements: `Udr/Statements.lean`; composition: `Udr/Compose.lean`.

| Item | Statement / theorem | Owner | State |
|---|---|---|---|
| counting toolkit | `Udr/Count.lean` | L3 | proved |
| vector-symbol codes, `Strong`/`CA`/`LineGap` | `Udr/Code.lean` | L3 | proved |
| CA ⇒ strong line | `strong_of_ca`, `strong_of_gap` | L3 | proved |
| d/3 gap, any linear code (interleaved incl.) | `gap_d3`, `strong_line_d3` (≤ e+1 bad z) | L3 | proved |
| interleaving lift of a gap (2e<d) | `gap_interleave` | L3 | proved |
| polynomial toolkit | `Udr/Poly.lean` (root bound, IsPoly, swap) | L3 | proved |
| RS code (scalar, interleaved) | `Udr/RS.lean` `rsCode`, `rsInterleaved` | L3 | proved |
| BW d/2 RS line gap | `RsGapStmt` | sub-agent `zk-L3-bw` | open |
| d/2 strong line, interleaved RS | `strong_line_rs2` (from `RsGapStmt`) | L3 | composed |
| FRI pass-set (virtual folds, roll-ins) | `FriStmt` | sub-agent `zk-L3-fri` | open |
| FRI query bound | `fri_far_pass_lt` (from `FriStmt`) | L3 | composed |
| grand product (γ round) | `GpGammaStmt` | sub-agent `zk-L3-gp` | open |
| fingerprints (α round) | `GpAlphaStmt` | sub-agent `zk-L3-gp` | open |
| DEEP farness, ALI divisibility, batching | — | L3 | in progress |
| `Iop.RbrFacts nearAir prm` packaging | needs L4 `PT`/IOP types | L3 | blocked on L4 |

Elaboration times (clean build of `ZkFormal.Udr.*`): each module < 1 s.
