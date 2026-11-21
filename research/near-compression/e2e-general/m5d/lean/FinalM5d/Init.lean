import FinalM5d.Final

/-!
# FinalM5d.Init — the M5d INIT template AIR (claim intake → the `init` boundary)

`B_0 = view (init cb wb)` (lane E, `View.split`: phase 0, `ctxRoot = ctxD (.raw cb wb)`, every
other field empty). The template computes the two digests of `B_0` that depend on the chunk:

* `claimDigest = bdigest (pre ‖ u32 0 ‖ post)` — lane E's canonical statement encoding
  (`StmtEnc.claimDigest`, `encode_splice`: `pre = stmtPre`, `post = stmtPost`, the claim with an
  empty section B); the same message the FINAL template hashes, and what V_d recomputes;
* `ctxRoot = bdigest (0x00 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` with `cb = pre ‖ blocks ‖ post`
  (`= assemble ci secB secC` when `blocks = encList BlockRec.encode secB`) and `ℓ_B = |blocks|`.

Tables: `S384`, `RNG` (as in FINAL), `CLM` (one row per byte of `pre ‖ blocks ‖ post ‖ wb`, kinds in
that order; it feeds both messages: the statement message skips the `blocks` rows), `INI` (one row:
the counts, the length prefixes, the digests, the public values).

Public values: `claimDigest` (14 limbs), `ctxRoot` (14 limbs).
-/

namespace FinalM5d.InitT

open ZkFormal.Air

def ID_CTX : Nat := 3
def CTX_TAG : Nat := 0
/-- `(n_pre, n_blocks, n_claim, n_total, n_stmt)` from the last stream row. -/
def B_END : Nat := 7

def PV_CLAIM : Nat := 0
def PV_CTX : Nat := 14
def NUM_PUB : Nat := 28

namespace Clm
def L : Layout :=
  [("act", 1), ("kc", 1), ("ks", 1), ("b", 1), ("ka", 1), ("kb", 1), ("kp", 1), ("kw", 1),
   ("na", 1), ("nb", 1), ("nc", 1)]
def T : Cols := ⟨L⟩
def act := T.c "act"
def ka := T.c "ka"
def kb := T.c "kb"
def kp := T.c "kp"
def kw := T.c "kw"
def constraints : List Expr :=
  actPrefix T ++ (["ka", "kb", "kp", "kw"].map fun s => bool (T.c s)) ++
  [ ka + kb + kp + kw - act,
    .isFirst * (ka - 1), .isFirst * T.c "kc", .isFirst * T.c "ks",
    .isFirst * T.c "na", .isFirst * T.c "nb", .isFirst * T.c "nc",
    contRow T * (T.n "kc" - T.c "kc" - 1),
    contRow T * (T.n "ks" - T.c "ks" - ka - kp),
    contRow T * (T.n "na" - T.c "na" - ka),
    contRow T * (T.n "nb" - T.c "nb" - kb),
    contRow T * (T.n "nc" - T.c "nc" - ka - kb - kp),
    -- kinds in the order pre, blocks, post, witness; pre, blocks, post are non-empty
    contRow T * ka * (1 - T.n "ka" - T.n "kb"),
    contRow T * kb * (1 - T.n "kb" - T.n "kp"),
    contRow T * kp * (1 - T.n "kp" - T.n "kw"),
    contRow T * kw * (1 - T.n "kw"),
    endRow T * (ka + kb) ]
def interactions : List Interaction :=
  [ snd B_SB (ka + kp) [K ID_CLAIM, T.c "ks" + K 4 * kp, T.c "b"],
    snd B_SB act [K ID_CTX, K 9 + T.c "kc", T.c "b"],
    snd B_END (endRow T) [T.c "na" + ka, T.c "nb" + kb, T.c "nc" + ka + kb + kp, T.c "kc" + 1,
      T.c "ks" + ka + kp] ]
def table : Table := { width := L.width, constraints, interactions, maxLog := 24 }
end Clm

namespace Ini
def L : Layout :=
  [("act", 1), ("na", 1), ("nb", 1), ("nc", 1), ("nt", 1), ("ns", 1), ("pa", 3), ("lb", 3),
   ("lc", 3), ("cd", 48), ("xd", 48)]
def T : Cols := ⟨L⟩
def act := T.c "act"
def le3 (s : String) : Expr := T.c s 0 + K 256 * T.c s 1 + K 65536 * T.c s 2
def b4 (s : String) (j : Nat) : Expr := if j < 3 then T.c s j else 0
def constraints : List Expr :=
  [bool act, .isFirst * (act - 1), .isTransition * T.n "act",
   act * (T.c "na" - le3 "pa"), act * (T.c "nb" - le3 "lb"), act * (T.c "nc" - le3 "lc")] ++
  eqs act ((List.range 14).map fun i => P (PV_CLAIM + i)) (limbs3 (T.cs "cd" 42)) ++
  eqs act ((List.range 14).map fun i => P (PV_CTX + i)) (limbs3 (T.cs "xd" 42))
def interactions : List Interaction :=
  [ rcv B_END act [T.c "na", T.c "nb", T.c "nc", T.c "nt", T.c "ns"] ] ++
  (List.range 4).map (fun j => snd B_SB act [K ID_CLAIM, T.c "na" + K j, K 0]) ++
  [ snd B_SB act [K ID_CTX, K 0, K CTX_TAG] ] ++
  (List.range 4).map (fun j => snd B_SB act [K ID_CTX, K (1 + j), b4 "lb" j]) ++
  (List.range 4).map (fun j => snd B_SB act [K ID_CTX, K (5 + j), b4 "lc" j]) ++
  [ rcv B_SD act ([K ID_CLAIM, K 4 + T.c "ns"] ++ T.cs "cd" 48),
    rcv B_SD act ([K ID_CTX, K 9 + T.c "nt"] ++ T.cs "xd" 48) ] ++
  (["pa", "lb", "lc"].flatMap fun s => (List.range 3).map fun j => rcv B_R8 act [T.c s j])
def table : Table := { width := L.width, constraints, interactions, maxLog := 4 }
end Ini

def initNames : List String := ["S384", "RNG", "CLM", "INI"]

def initAir : Air :=
  { tables := [S384.table, Rng.table, Clm.table, Ini.table], numBuses := NUM_BUSES, numPub := NUM_PUB }

def initLayouts : List (String × Layout) :=
  [("S384", S384.L), ("RNG", Rng.L), ("CLM", Clm.L), ("INI", Ini.L)]

end FinalM5d.InitT
