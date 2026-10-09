import ZkFormal.NearV3.Rcpt.Candidates.DedupRender

/-! Candidate source AIR only. It is not installed in the active assembly or admitted
by the current log22 protocol. Logical-renderer and partition-continuation proofs are
separate work; the `cap` parameter does not change the active Table.wf predicate. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl SrcpV3

abbrev repeated : Nat := 56
abbrev width : Nat := 57

/-- `dup` is constrained to root rows, so these linear expressions replace
higher-degree products when choosing computed roots and completed source blocks. -/
def computedRoot : Expr := sub (c rt) (c dup)
def endRow : Expr := .add (c sl) (c dup)

/-- Preserve unaffected constraints at their original indices for proof reuse. -/
def patch (i : Nat) (ex : Expr) : Expr :=
  match i with
  | 17 => .mul .isLast computedRoot
  | 19 => .mul computedRoot (not (n sg))
  | 20 => .mul computedRoot (not (n lf))
  | 21 => .mul computedRoot (not (n sf))
  | 22 => .mul computedRoot (sub (n q) (.add (c q) (k 1)))
  | 53 => .mul (c gz) (not endRow)
  | 55 => .mul (mul3 .isTransition endRow (not (c gz))) (not (.add (n rt) (n sg)))
  | 56 => .mul .isLast (.mul endRow (not (c gz)))
  | 58 => sub (c gD) (.add computedRoot (.mul (c wf) (c aw)))
  | 59 => .mul computedRoot (sub (c cId) (mid K_SRC (c qe)))
  | 60 => .mul computedRoot (sub (c cLen) (c le))
  | 65 => .mul computedRoot (sub (n j) (c j))
  | 66 => .mul computedRoot (sub (n L) (c L))
  | 67 => .mul computedRoot (sub (n qe) (c qe))
  | 68 => .mul computedRoot (sub (n le) (c le))
  | _ => ex

def additions : List Expr :=
  [ bool (c repeated),
    .mul (c dup) (not (c rt)),
    .mul (c repeated) (not (c rt)),
    .mul (c dup) (not (c repeated)),
    mul3 (c rt) (c repeated) (sub (c L) (k 12)),
    .mul (c dup) (sub (c qe) (c q)),
    .mul (c dup) (c le),
    mul3 (c dup) (not (c gz)) (not (n rt)),
    .mul .isTransition (mul3 (c dup) (n rt) (sub (n q) (c q))),
    .mul .isTransition (mul3 (c dup) (n rt) (sub (n j) (.add (c j) (k 1)))) ]

def constraints : List Expr := SrcpV3.constraints.mapIdx patch ++ additions

/-- The only public-record change is the all-occurrence repetition bit. All digest,
RCL, byte, and SIZE buses retain their original payload formats. -/
def interactions : List Interaction :=
  [ send B_BYTES (c sg) [mid K_SRC (c q), .add (smul 32 (c wn)) (c pw), c b],
    recv B_DIGEST (c gD) ([c cId, c cLen] ++ SrcpV3.regs),
    recv B_RCL (c rt) [c j, c L],
    recv B_SRC (c rt) ([c j, c dup, c repeated] ++ SrcpV3.regs),
    send B_SIZE (c gz) [k 2, c sz] ]

def table (cap : Nat) : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := cap }

set_option maxRecDepth 16384 in
/-- New dedup transitions retain the original degree4 bound. -/
theorem constraints_degree : constraints.all (fun e => decide (e.degree ≤ 4)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem expressions_width : ((table 24).exprs.all fun e => decide (e.colBound ≤ width)) = true := by
  decide +kernel

theorem counts : constraints.length = 122 ∧ interactions.length = 5 := by decide +kernel

end ZkFormal.NearV3.Rcpt.Candidates.DedupTable
