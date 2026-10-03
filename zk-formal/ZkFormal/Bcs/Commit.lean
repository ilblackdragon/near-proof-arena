import ZkFormal.Bcs.Wide

/-!
# ZkFormal.Bcs.Commit — commitment schemes over the oracle log

A vector commitment (Merkle tree, MMCS) is described by

* `OpenIn tbl root sh pos v`: the *verifier-side* relation — the final oracle
  log certifies (by recorded wide hashes) that position `pos` of the tree of
  shape `sh` with root `root` holds `v`;
* `ext hist root sh pos`: the *extractor* — the value at `pos` read off the
  log `hist` by inverting recorded wide hashes from the root down.

`Binding` is the deterministic property the BCS argument needs: in a
well-formed final log without wide collisions and without inversions, a
verifier-accepted opening agrees with the extraction from any earlier log
`hist` in which the root was already produced.  `Rooted`: an accepted
opening certifies that the root is produced.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

structure CommitScheme where
  Shape : Type
  /-- What one opening addresses (a leaf index; for MMCS a `(level, index)` pair). -/
  Pos : Type
  OpenIn : Table → Bytes → Shape → Pos → Bytes → Prop
  ext : Table → Bytes → Shape → Pos → Option Bytes

def CommitScheme.Binding (cs : CommitScheme) : Prop :=
  ∀ (pre hist : Table), TableWF (pre ++ hist) → ¬ WideCollision 2 whq (pre ++ hist) →
    NoInv (pre ++ hist) →
    ∀ root sh pos v, cs.OpenIn (pre ++ hist) root sh pos v → (∃ m, WHin hist m root) →
      cs.ext hist root sh pos = some v

def CommitScheme.Rooted (cs : CommitScheme) : Prop :=
  ∀ tbl root sh pos v, cs.OpenIn tbl root sh pos v → ∃ m, WHin tbl m root

/-- Some preimage of `u` recorded in `hist` (unique without wide collisions). -/
noncomputable def invert (hist : Table) (u : Bytes) : Option Bytes :=
  open Classical in if h : ∃ m, WHin hist m u then some (Classical.choose h) else none

theorem invert_spec {hist : Table} {u m : Bytes} (h : invert hist u = some m) : WHin hist m u := by
  classical
  unfold invert at h
  split at h
  · rename_i hex; cases h; exact Classical.choose_spec hex
  · cases h

/-- Inverting in an earlier log returns the preimage certified by the final log. -/
theorem invert_eq {pre hist : Table} (wf : TableWF (pre ++ hist))
    (hcol : ¬ WideCollision 2 whq (pre ++ hist)) {m u : Bytes} (hm : WHin (pre ++ hist) m u)
    (hp : ∃ m', WHin hist m' u) : invert hist u = some m := by
  classical
  unfold invert
  rw [dif_pos hp]
  congr 1
  exact wh_unique wf hcol (WHin.suffix wf.1 (Classical.choose_spec hp)) hm

/-- A digest used by a message produced in `hist`, and produced in the final
log, is produced in `hist` (no inversion). -/
theorem used_produced {pre hist : Table} (wf : TableWF (pre ++ hist)) (hni : NoInv (pre ++ hist))
    {m u mc c : Bytes} (hm : WHin hist m u) (hc : c ∈ slots (whq m 0))
    (hcp : WHin (pre ++ hist) mc c) : WHin hist mc c := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hm
  obtain ⟨s, t, hst⟩ := List.mem_iff_append.mp (lookup_mem_pair ha)
  have h1 : pre ++ hist = (pre ++ s) ++ (whq m 0, a) :: t := by rw [hst]; simp
  have h2 := hni _ _ _ _ h1 c hc mc hcp
  have hwf : TableWF ((s ++ [(whq m 0, a)]) ++ t) := by
    have := wf.suffix; rw [hst] at this; simpa using this
  have := WHin.suffix hwf.1 h2
  rw [hst]; simpa using this

end ZkFormal.Bcs
