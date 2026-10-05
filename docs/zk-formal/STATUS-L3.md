# STATUS — lane L3 (IOP math, unique-decoding regime)

Package `zk-formal/`, namespace `ZkFormal.Udr` (`ZkFormal.Udr.Np` for the protocol instance).
All listed "proved" items are sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound}.

## Generic UDR math (proved)

| Item | Theorem | File |
|---|---|---|
| CA ⇒ strong (containment) line lemma | `strong_of_ca`, `strong_of_gap` | `Udr/Code.lean` |
| d/3 gap + strong line, any linear code, vector symbols (≤ e+1 bad z) | `gap_d3`, `strong_line_d3` | `Udr/Code.lean` |
| interleaving lift of a 2e<d gap (same threshold) | `gap_interleave` | `Udr/Code.lean` |
| polynomial toolkit (root bounds, IsPoly, Fubini) | `coeffs_zero_of_roots`, `count_roots_lt`, `IsPoly.mul`, `ev_swap` | `Udr/Poly.lean` |
| RS codes (scalar, interleaved) | `rsCode`, `rsInterleaved`, `ev_eq_of_agree` | `Udr/RS.lean` |
| linear algebra (underdetermined systems) | `exists_nonzero_sol` | `Udr/BWLin.lean` |
| **BW d/2 RS line gap** (threshold 3n+2e+1, 2e+D ≤ n) | `rsGap : RsGapStmt` | `Udr/BW.lean` |
| **strong line, interleaved RS, d/2** | `strong_line_rs`, `strong_line_rs_scalar` | `Udr/Main.lean` |
| **FRI pass-set argument** (virtual folds, roll-ins, e_i ≤ 2e_{i+1}+1) | `fri : FriStmt`, `friRoll : FriRollStmt`, `fri_query_bound` | `Udr/Fri.lean`, `Udr/Main.lean` |
| **grand product** (γ round) / fingerprints (α round) | `gpGamma`, `gpAlpha` | `Udr/GrandProduct.lean` |
| **DEEP farness** / closeness transfer | `deep_close`, `deep_value` | `Udr/Deep.lean` |
| **multilinear batching** chain | `batch_close`, `batch_chain` | `Udr/Deep.lean` |

## RbrFacts for np-udr-stark (`Udr/Rbr.lean`, `Udr/Np/*`)

Interface: `RbrFacts V InLang Kall bad agree` (existential `Doomed`), see REQUESTS R-L3-1.
Composition `Np.rbr_of` (proved) from the obligations in `Udr/Np/Statements.lean`:

| Obligation | Owner | State |
|---|---|---|
| `ShapedPrefixStmt`, `ScheduleAltStmt` | ali | **proved** (`shapedPrefix`, `scheduleAlt`, Shape.lean) |
| `Msg0/2/6Stmt` | ali | **proved** (`msg0`, `msg2`, `msg6`, Early.lean) |
| `Msg4Stmt` (aux chain ⇒ grand products) | ali | **proved** (`msg4`, Msg4.lean) |
| `Chal1/3Stmt` (fingerprints ≤ fpBound, γ ≤ multBound) | ali | **proved** (`chal1`, `chal3`, BusRounds.lean) |
| `Chal5Stmt` (α_c), `Chal7Stmt` (z) | ali | **proved** (`chal5`, `chal7`) |
| `ChalLateStmt` (batching, FRI β/γ) | fri2 | **proved** (`chalLate`, Late.lean) |
| `MsgLateStmt` | fri2 | **proved** (`msgLate`, FrameMsg.lean) |
| `QueryStmt` | fri2 | reduced to `LocalBridgeStmt` (`query_of_bridge`); bridge open |
| `Msg8Stmt` (OOD values: DEEP farness, global = semantic ALI) | ali | open |

Elaboration: every `Udr` module < 1.5 s.
