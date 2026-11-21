import StateM5a.St
import StateM5a.StateView
import NearSpecV3.E2E.StEnc

/-!
# StateM5a.Tmpl — B-T1: the state AIR cut into tree-leaf templates

The M5b AIR (`St.m5bAir D`) is one proof over INTAKE, every working-set segment and FINAL.  Only
`RCH` (the working-set root between segments) crosses the cut (README §M5a-3), so the AIR splits
into two templates with the same tables and one new boundary table each:

* **`m5tIF D`** (INTAKE + FINAL): `SHA KEY BR SN KCMP WSB WSN SNC RNG WSXI` — the INTAKE find walks
  and tree (`RCH(0, R_0)`), the FINAL tree (`RCH(nw, R_n)`) and change walks (`TCH`).  No cached
  table: the `TCH` ends are public values (they were the public `TAPE`).
* **`m5tSeg D`** (one STATE segment): `SHA WSA WSL WSP RNG STB STW WSXS` — the segment's write
  accesses, its batched path update (`RCH(0, R_in) → RCH(1, R_out)`), and the STATE rows producing
  its writes from the execution side's `SREQ`/`HB` (the cached `HTAPE` until the M6 join).

**`WSX`: the working-set root at depth 24.**  The circuit's tree has depth `D` (the template's);
lane E's state view (`StViewE.depth = Enc.wsDepth = 24`, `StateView.wsRoot`) commits to the
zero-padded depth-24 root.  `WSX` extends a depth-`D` root to depth 24 in-circuit: rows
`lvl = D … 23`, `x_{lvl+1} = H(x_lvl, Z_lvl)` with the zero-subtree digest chain `Z_{lvl+1} =
H(Z_lvl, Z_lvl)` starting from the constant `Z_D` (`zeroLimbs D`), for two roots `a` and `b` at once
(`Merkle.root_pad`: the extension is the depth-24 root of the leaves padded with zero digests).

Public values (every AIR of a template proof reads a prefix of one statement vector; a verifier
must check them on every AIR that reads them, as the M5a prover's statement check does):

| index | field | `m5tIF` | `m5tSeg` |
|---|---|---|---|
| 0–15 | `prev_state_root` (16-bit limbs, `pack2`) | `WSB` `DOWN`, `TCH(0, ·)` | not read |
| 16 | `wsLen` | `WSB` | `WSL` (`i < wsLen`) |
| 17–34 | working-set root A, depth 24 (18 limbs of 21 bits, SHA-384 words) | `R_0` (after INTAKE) | `R_in` |
| 35–52 | working-set root B, depth 24 | `R_n` (before FINAL) | `R_out` |
| 53–68 | `post_state_root` | `TCH(n, ·)` | – |
| 69 | the change count `n` (`TCH` index of the post-state root) | `TCH(n, ·)` | – |
-/

namespace StateM5a

open ZkFormal.Air
open StateM5a.StateView (nodeH zero48)
open NearSpec

/-- Public value indices of the template statement. -/
def PUB_WSA : Nat := 17
def PUB_WSB : Nat := 35
def PUB_POST : Nat := 53
def PUB_NCH : Nat := 69
def NUM_PUB_IF : Nat := 70
def NUM_PUB_SEG : Nat := 53

/-- The depth of the committed working-set root: lane E's `Enc.wsDepth` (24). -/
def WS_DEPTH : Nat := NearSpecV3.E2E.Enc.wsDepth

theorem WS_DEPTH_eq : WS_DEPTH = 24 := rfl

/-- The zero-subtree digests: `Z_0` = the 48 zero bytes of an unused leaf, `Z_{d+1} = H(Z_d, Z_d)`. -/
def zeroDig : Nat → Bytes
  | 0 => zero48
  | d + 1 => nodeH (zeroDig d) (zeroDig d)

/-- The 6 big-endian 64-bit words of a 48-byte digest (SHA-384's `H_0 … H_5`). -/
def wordsBE (b : Bytes) : List Nat :=
  (List.range 6).map fun i => (List.range 8).foldl (fun acc k => acc * 256 + (b.getD (8 * i + k) 0).toNat) 0

/-- `Z_d` as the 18 limbs of a digest column group (`wlimbs` per word). -/
def zeroLimbs (d : Nat) : List Nat := (wordsBE (zeroDig d)).flatMap wlimbs

/-! ## WSX: extend two depth-`D` roots to depth 24 -/

namespace Wsx
def L : Layout :=
  [("act", 1), ("top", 1), ("lvl", 1), ("sb", 1),
   ("z", 18), ("zo", 18), ("zx", 6), ("cz", 1),
   ("a", 18), ("ao", 18), ("ax", 6), ("ca", 1),
   ("b", 18), ("bo", 18), ("bx", 6), ("cb", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

/-- Rows `lvl = D, D+1, …, 23` are active (a prefix starting at the first row); the last active row
(`top`) holds the depth-24 roots, equal to the public values. -/
def constraints (D : Nat) : List Expr :=
  let act := c "act"; let top := c "top"; let na := nx "act"
  [bool act, bool top, (1 - act) * top,
   .isFirst * (1 - act), .isFirst * (c "lvl" - K D),
   .isTransition * na * (1 - act),
   .isTransition * (top - act * (1 - na)),
   .isLast * (top - act),
   .isTransition * na * (nx "lvl" - c "lvl" - 1),
   top * (c "lvl" - K (WS_DEPTH - 1))] ++
  ((List.range 18).flatMap fun t =>
    [.isFirst * (c "z" t - K ((zeroLimbs D).getD t 0)),
     .isTransition * na * (nx "z" t - c "zo" t),
     .isTransition * na * (nx "a" t - c "ao" t),
     .isTransition * na * (nx "b" t - c "bo" t),
     top * (c "ao" t - .pub (PUB_WSA + t)),
     top * (c "bo" t - .pub (PUB_WSB + t))])

/-- The three compressions of a row: `zo = H(z, z)`, `ao = H(a, z)`, `bo = H(b, z)`. -/
def comps : List Interaction :=
  let A := c "act"
  let zw := digW fun t => c "z" t
  comp A (c "cz") (ivW ++ nodeBlock zw zw ++ digW (fun t => c "zo" t) ++ wordsOf (fun t => c "zx" t) 2) ++
  comp A (c "ca") (ivW ++ nodeBlock (digW fun t => c "a" t) zw ++ digW (fun t => c "ao" t) ++
    wordsOf (fun t => c "ax" t) 2) ++
  comp A (c "cb") (ivW ++ nodeBlock (digW fun t => c "b" t) zw ++ digW (fun t => c "bo" t) ++
    wordsOf (fun t => c "bx" t) 2)

/-- `m5tIF`: receive the INTAKE root `RCH(0, R_0)` (chain `a`), send the FINAL tree's root
`RCH(sb, R_n)` (chain `b`); the trie-root chain's public ends `TCH(0, prev)`, `TCH(n, post)`. -/
def interactionsIF : List Interaction :=
  [rcv B_RCH .isFirst (0 :: vec "a" 18),
   snd B_RCH .isFirst (c "sb" :: vec "b" 18),
   snd B_TCH .isFirst ([0, 0] ++ (List.range 16).map fun t => Expr.pub t),
   rcv B_TCH .isFirst ([.pub PUB_NCH, 0] ++ (List.range 16).map fun t => Expr.pub (PUB_POST + t))] ++
  comps

/-- `m5tSeg`: send the segment's incoming root `RCH(0, R_in)` (chain `a`), receive its outgoing
root `RCH(sb, R_out)` (chain `b`). -/
def interactionsSeg : List Interaction :=
  [snd B_RCH .isFirst (0 :: vec "a" 18),
   rcv B_RCH .isFirst (c "sb" :: vec "b" 18)] ++
  comps

def tableIF (D : Nat) : Table :=
  { width := L.width, constraints := constraints D, interactions := interactionsIF, maxLog := 5 }
def tableSeg (D : Nat) : Table :=
  { width := L.width, constraints := constraints D, interactions := interactionsSeg, maxLog := 5 }
end Wsx

/-! ## The two templates -/

/-- INTAKE + FINAL. -/
def m5tIF (D : Nat) : Air :=
  { tables := [shaTable, Key.table, Br.table, Sn.table, Kcmp.table, Wsb.table D, Wsn.table D,
      Snc.table, Rng.table, Wsx.tableIF D],
    numBuses := NUM_BUSES_ST, numPub := NUM_PUB_IF }

/-- One STATE segment. -/
def m5tSeg (D : Nat) : Air :=
  { tables := [shaTable, Wsa.table, Wsl.table, Wsp.table D, Rng.table, Stb.table, Stw.table,
      Wsx.tableSeg D],
    numBuses := NUM_BUSES_ST, numPub := NUM_PUB_SEG }

def tableNamesIF : List String := ["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "SNC", "RNG", "WSX"]
def tableNamesSeg : List String := ["SHA", "WSA", "WSL", "WSP", "RNG", "STB", "STW", "WSX"]

/-- The column map of both templates (every table's layout; `tables` lists the template's order). -/
def namesJsonT (D : Nat) (names : List String) : String :=
  let q (s : String) := "\"" ++ s ++ "\""
  let ls := layoutsB D ++ [("WSX", Wsx.L)]
  "{" ++ ",".intercalate (ls.map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++
  s!",\"D\":{D},\"ws_depth\":{WS_DEPTH},\"zero_limbs\":[" ++
    ",".intercalate ((zeroLimbs D).map toString) ++ "],\"tables\":[" ++
    ",".intercalate (names.map q) ++ "]}"

/-- Every table of a template is a table of the M5b AIR (same constraints and interactions), except
`WSX`. -/
theorem m5tIF_tables (D : Nat) :
    (m5tIF D).tables = [shaTable, Key.table, Br.table, Sn.table, Kcmp.table, Wsb.table D, Wsn.table D,
      Snc.table, Rng.table] ++ [Wsx.tableIF D] := rfl

theorem m5tSeg_tables (D : Nat) :
    (m5tSeg D).tables = [shaTable, Wsa.table, Wsl.table, Wsp.table D, Rng.table] ++ m5bExtra ++
      [Wsx.tableSeg D] := rfl

end StateM5a
