import ZkFormal.Air.Basic

/-!
# ZkFormal.Air.Export — the AIR description consumed by the Rust prover

`Air.exportJson A` is the exact text the Rust prover (lane L8) reads; the
format `np-air-v1` is specified in `docs/zk-formal/FORMATS.md` §1.  It is not
part of soundness (DESIGN.md §5.1): a mismatch can only make honest proofs
fail.

Expressions are emitted as nested JSON arrays (prefix form):

| `Expr`             | JSON                  |
|--------------------|-----------------------|
| `const c`          | `["c", c]`            |
| `col c next`       | `["v", c, 0/1]`       |
| `pub i`            | `["p", i]`            |
| `isFirst`          | `["first"]`           |
| `isLast`           | `["last"]`            |
| `isTransition`     | `["trans"]`           |
| `add a b`          | `["+", a, b]`         |
| `mul a b`          | `["*", a, b]`         |
| `neg a`            | `["-", a]`            |

Each table lists `constraints` = `Table.allConstraints` (the user constraints
followed by the generated multiplicity-bit booleanity constraints): this is the
exact ordered list the verifier combines with powers of `α_c`.
-/

namespace ZkFormal.Air

/-- JSON for an expression. -/
def Expr.toJson : Expr → String
  | .const c => s!"[\"c\",{c}]"
  | .col c nx => s!"[\"v\",{c},{if nx then 1 else 0}]"
  | .pub i => s!"[\"p\",{i}]"
  | .isFirst => "[\"first\"]"
  | .isLast => "[\"last\"]"
  | .isTransition => "[\"trans\"]"
  | .add a b => s!"[\"+\",{a.toJson},{b.toJson}]"
  | .mul a b => s!"[\"*\",{a.toJson},{b.toJson}]"
  | .neg a => s!"[\"-\",{a.toJson}]"

/-- `[x₁,…,xₙ]` -/
def jsonList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def Interaction.toJson (i : Interaction) : String :=
  s!"\{\"bus\":{i.bus},\"send\":{if i.send then "true" else "false"}," ++
  s!"\"mult\":{jsonList (i.mult.map Expr.toJson)},\"msg\":{jsonList (i.msg.map Expr.toJson)}}"

def Table.toJson (T : Table) : String :=
  s!"\{\"width\":{T.width},\"maxLog\":{T.maxLog}," ++
  s!"\"constraints\":{jsonList (T.allConstraints.map Expr.toJson)}," ++
  s!"\"interactions\":{jsonList (T.interactions.map Interaction.toJson)}}"

/-- **The export** (`export` is a Lean keyword, hence the name). -/
def Air.exportJson (A : Air) : String :=
  s!"\{\"format\":\"np-air-v1\",\"numBuses\":{A.numBuses},\"numPub\":{A.numPub}," ++
  s!"\"tables\":{jsonList (A.tables.map Table.toJson)}}"

end ZkFormal.Air
