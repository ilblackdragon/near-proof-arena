import StateM5a.FieldRows

/-!
# StateM5a.FieldVer — the version constraints of batched FINAL, from the tables' constraints

Row facts the version store (`Store`) needs from a `BR` / `SN` row on which the table's
constraints vanish over BabyBear (as `FieldRows`):

| lemma | what it gives |
|---|---|
| `br_vm_gsha`, `sn_vm_gsha` | a row that publishes its old node on `VER` (a multiplicity bit `vm` set) hashed it (`gsha = 1`) |
| `br_gsha_dig`, `sn_gsha_dig` | a hashed old node is addressed by its digest (`oref = 0`) |
| `br_gsha_isn`, `sn_gsha_xf` | a hashed old node's children are digests (no version id in a SHA-256 preimage) |
| `br_vmn_gnew`, `sn_vmn_gnew` | a row that publishes a new node has one (`gnew = 1`) |
| `br_vid`, `sn_vid` | a new node under a version id (`nref = 1`) carries the row's own id `ID + 2·rid + 1` in cell 0 of its ref and zeros elsewhere: ids are unique per row (`rid` is the row index) and per table (`ID_BR ≠ ID_SN`) |
| `sn_cont` | a continued key never uses `VER`: hashed old node, no version id, no publication |

So every `VER` send under a version id comes from one row (its own id), and every send under a
digest comes from a row that hashed the record: the bus's records are a function of the ref
(`Store.exp_functional`'s premise).
-/

namespace StateM5a.FieldVer

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "P" => 2013265921

/-- `a·b = 0` with `a = 1` gives `b = 0`. -/
theorem gate_zero {a b : Expr} (h : ev tr t r pub (a * b) = 0) (ha : ev tr t r pub a = 1) :
    ev tr t r pub b = 0 := by
  change ev tr t r pub (Expr.mul a b) = 0 at h
  rwa [ev_mul_gate _ ha] at h

/-- `(1 − g)·x = 0` with `x = 1` gives `g = 1`. -/
theorem one_of_gate {g x : Expr} (h : ev tr t r pub ((1 - g) * x) = 0) (hx : ev tr t r pub x = 1) :
    ev tr t r pub g = 1 := by
  change ev tr t r pub (Expr.mul _ x) = 0 at h
  rcases ev_mul_eq_zero h with h | h
  · have := eq_of_sub (a := 1) (b := g) h
    simpa using this.symm
  · omega

/-- `x·(y − z) = 0` with `x = 1` gives `y = z`. -/
theorem eq_of_gate {x y z : Expr} (h : ev tr t r pub (x * (y - z)) = 0) (hx : ev tr t r pub x = 1) :
    ev tr t r pub y = ev tr t r pub z := eq_of_sub (gate_zero h hx)

/-- Membership in a left-nested append of constraint segments: search the segments. -/
syntax "memfind" : tactic
macro_rules
  | `(tactic| memfind) => `(tactic| first
      | (apply Or.inr; refine ⟨_, ‹_ < _›, ?_⟩; simp; done)
      | (apply Or.inr; simp; done)
      | (apply Or.inl; memfind))

/-! ## BR -/

theorem br_vm_gsha (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Br.c "vm" k) = 1) : ev tr t r pub (Br.c "gsha") = 1 := by
  refine one_of_gate (hold (L := Br.constraints) rfl hc ?_) hv
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem br_vmn_gnew (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Br.c "vmn" k) = 1) : ev tr t r pub (Br.c "gnew") = 1 := by
  refine one_of_gate (hold (L := Br.constraints) rfl hc ?_) hv
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem br_gsha_dig (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Br.c "gsha") = 1) : ev tr t r pub (Br.c "oref") = 0 := by
  refine gate_zero (hold (L := Br.constraints) rfl hc ?_) hg
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem br_gsha_isn (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0) (i : Nat) (hi : i < 16)
    (hg : ev tr t r pub (Br.c "gsha") = 1) : ev tr t r pub (Br.c "isn" i) = 0 := by
  refine gate_zero (hold (L := Br.constraints) rfl hc ?_) hg
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

/-- **A version id is the row's own**: cell 0 of the new ref is `ID_BR + 2·rid + 1`, the others
are zero. -/
theorem br_vid (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hn : ev tr t r pub (Br.c "nref") = 1) :
    ev tr t r pub (Br.c "hn" 0) = ev tr t r pub Br.nidN ∧
      ∀ b, b < 31 → ev tr t r pub (Br.c "hn" (b + 1)) = 0 := by
  refine ⟨eq_of_gate (hold (L := Br.constraints) rfl hc ?_) hn, fun b hb => gate_zero (hold (L := Br.constraints) rfl hc ?_) hn⟩
  · unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind
  · unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind

/-! ## SN -/

theorem sn_vm_gsha (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Sn.c "vm" k) = 1) : ev tr t r pub (Sn.c "gsha") = 1 := by
  refine one_of_gate (hold (L := Sn.constraints) rfl hc ?_) hv
  unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem sn_vmn_gnew (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Sn.c "vmn" k) = 1) : ev tr t r pub (Sn.c "gnew") = 1 := by
  refine one_of_gate (hold (L := Sn.constraints) rfl hc ?_) hv
  unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem sn_gsha_dig (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Sn.c "gsha") = 1) :
    ev tr t r pub (Sn.c "oref") = 0 ∧ ev tr t r pub (Sn.c "xf") = 0 := by
  refine ⟨gate_zero (hold (L := Sn.constraints) rfl hc ?_) hg, gate_zero (hold (L := Sn.constraints) rfl hc ?_) hg⟩
  · unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind
  · unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind

theorem sn_vid (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hn : ev tr t r pub (Sn.c "nref") = 1) :
    ev tr t r pub (Sn.c "hn" 0) = ev tr t r pub Sn.nidN ∧
      ∀ b, b < 31 → ev tr t r pub (Sn.c "hn" (b + 1)) = 0 := by
  refine ⟨eq_of_gate (hold (L := Sn.constraints) rfl hc ?_) hn, fun b hb => gate_zero (hold (L := Sn.constraints) rfl hc ?_) hn⟩
  · unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind
  · unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind

/-- **A continued key never uses `VER`.** -/
theorem sn_cont (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hk : ev tr t r pub (Sn.c "cont") = 1) :
    ev tr t r pub (Sn.c "gold") = ev tr t r pub (Sn.c "gsha") ∧ ev tr t r pub (Sn.c "nref") = 0 ∧
      ∀ k, k < VBITS → ev tr t r pub (Sn.c "vm" k) = 0 ∧ ev tr t r pub (Sn.c "vmn" k) = 0 := by
  refine ⟨eq_of_gate (hold (L := Sn.constraints) rfl hc ?_) hk,
    gate_zero (hold (L := Sn.constraints) rfl hc ?_) hk,
    fun k hk' => ⟨gate_zero (hold (L := Sn.constraints) rfl hc ?_) hk,
      gate_zero (hold (L := Sn.constraints) rfl hc ?_) hk⟩⟩
  all_goals (unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]; memfind)

end StateM5a.FieldVer
