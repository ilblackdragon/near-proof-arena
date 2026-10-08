import ZkFormal.NearV3.Candidates.SchedHeight
namespace ZkFormal.NearV3.Candidates.CmpHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Cmp ZkFormal.NearV3.Sched.Complete
def trace (cmps : List (Nat × Nat × Nat)) : Trace Fp :=
  SchedHeight.trace (Gen.Cmp.rows cmps) (fun _=>Gen.Cmp.padRow)
variable (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, CmpOk q)
theorem cmp_constraints (hok : ∀ q ∈ cmps, CmpOk q) (t : Nat) (pub : List Fp) (r : Nat)
    (hr : r < (trace cmps).height t) :
    ∀ e ∈ constraints, e.eval (trace cmps) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  have hE := (SchedHeight.env _ _ (small cmps hok) t r pub).1
  by_cases hin : r < cmps.length
  · have hq := hok _ (List.getElem_mem hin)
    exact constraints_row _ _ _ hq (fun c => by have h := hE c; rw [cell_lt_rows cmps hin] at h; exact h) e he
  · exact constraints_pad (fun c => by have h := hE c; rw [cell_ge_rows cmps (by omega)] at h; exact h) e he

theorem cmp_bits (cmps : List (Nat × Nat × Nat)) (busCmp t r : Nat) (pub : List Fp)
    (hr : r < (trace cmps).height t) :
    ∀ i ∈ interactions busCmp, ∀ b ∈ i.mult,
      b.eval (trace cmps) t r pub = 0 ∨ b.eval (trace cmps) t r pub = 1 := by
  intro i hi b hb
  simp only [interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  show (trace cmps).cell t r colAct = 0 ∨ (trace cmps).cell t r colAct = 1
  change Fp.ofNat (natCell (Gen.Cmp.rows cmps) (fun _=>Gen.Cmp.padRow) r colAct) = 0 ∨ Fp.ofNat (natCell (Gen.Cmp.rows cmps) (fun _=>Gen.Cmp.padRow) r colAct) = 1
  rw [act_cell]
  exact ofNat_bit (by split <;> omega)

theorem cmp_row_count (cmps : List (Nat × Nat × Nat)) (busCmp t r : Nat) (pub : List Fp) (m : List Fp)
    (hr : r < (trace cmps).height t) (send : Bool) :
    ((interactions busCmp).map fun i =>
      if i.bus = busCmp ∧ i.send = send ∧ i.msgVal (trace cmps) t r pub = m then
        i.multNat (trace cmps) t r pub else 0).sum =
      if send = false ∧ r < cmps.length ∧ cmpMsg (cmps.getD r (0, 0, 0)) = m then 1 else 0 := by
  have hcell : ∀ c, (trace cmps).cell t r c = Fp.ofNat (natCell (Gen.Cmp.rows cmps) (fun _=>Gen.Cmp.padRow) r c) := fun _=>rfl
  simp only [interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hmult : Interaction.multNat { bus := busCmp, mult := [ZkFormal.Chacha.Table.E.c colAct], send := false, msg := msg } (trace cmps) t r pub = if r < cmps.length then 1 else 0 := by
    simp only [Interaction.multNat, Interaction.multNat.go]
    show (if (trace cmps).cell t r colAct = 1 then 2 ^ 0 else 0) + 0 = _
    rw [hcell, act_cell]
    split <;> rfl
  rw [hmult]
  by_cases hin : r < cmps.length
  · have hv : Interaction.msgVal { bus := busCmp, mult := [ZkFormal.Chacha.Table.E.c colAct], send := false, msg := msg } (trace cmps) t r pub = cmpMsg (cmps.getD r (0, 0, 0)) := by
      simp only [Interaction.msgVal, msg, List.map_cons, List.map_nil]
      show [(trace cmps).cell t r colX, (trace cmps).cell t r colY,
        (trace cmps).cell t r colB] = _
      rw [hcell, hcell, hcell, cell_lt_rows cmps hin, cell_lt_rows cmps hin,
        cell_lt_rows cmps hin, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some]
      rfl
    rw [hv, if_pos hin]
    by_cases hs : send = false
    · subst hs
      by_cases e : cmpMsg (cmps.getD r (0, 0, 0)) = m
      · simp only [e, hin, true_and, and_self, if_true]
      · simp only [e, hin, true_and, and_false, if_false]
    · have h' : ¬ (false = send) := fun h => hs h.symm
      simp [h', hs]
  · rw [if_neg hin]; simp [hin]

theorem cmp_count (cmps : List (Nat × Nat × Nat)) (busCmp t : Nat) (pub : List Fp) (m : List Fp)
    (send : Bool) (hrows : cmps.length ≤ 2^22) :
    tableBusCount (interactions busCmp) (trace cmps) t pub busCmp send m =
      if send = false then (fmsgs (Gen.Cmp.expected cmps)).count m else 0 := by
  rw [busCount_sum]
  have hle : cmps.length ≤ (trace cmps).height t := by
    exact hrows
  rw [List.map_congr_left (fun r hr => cmp_row_count cmps busCmp t r pub m (List.mem_range.1 hr) send)]
  by_cases hs : send = false
  · subst hs
    rw [if_pos rfl, sum_range_trunc (fun r => if false = false ∧ r < cmps.length ∧
        cmpMsg (cmps.getD r (0, 0, 0)) = m then 1 else 0) (len := cmps.length)
        (fun r hr => if_neg (fun h => absurd h.2.1 (by omega))) _ hle]
    rw [fmsgs_expected, count_map_eq_sum, ← range_map_getD cmps (0, 0, 0)]
    apply congrArg
    apply List.map_congr_left
    intro r hr
    have := List.mem_range.1 hr
    by_cases e : cmpMsg (cmps.getD r (0, 0, 0)) = m
    · simp only [e, this, true_and, and_self, if_true]
    · simp only [e, this, true_and, and_false, if_false]
  · rw [if_neg hs]
    rw [List.map_congr_left (g := fun _ => 0) (fun r _ => by rw [if_neg (fun h => hs h.1)])]
    exact sum_map_zero _

end ZkFormal.NearV3.Candidates.CmpHeight
