import ZkFormal.V2.Air
import ZkFormal.Stark.Protocol

/-! Separate candidate height checks. These definitions do not change the deployed
verifier and do not constitute a soundness or admission certificate. -/
namespace ZkFormal.V2.Log23

open ZkFormal.Air ZkFormal.Stark

def params (g : Nat) : Params :=
  { Params.default with auxGroup := g, maxLogLde := 27, posBits := 27 }

def tableWf (heightCap : Nat) (A : Air) (d : Nat) (T : Air.Table) : Bool :=
  T.exprs.all (fun e => decide (e.colBound ≤ T.width) && decide (e.pubBound ≤ A.numPub)) &&
  T.interactions.all (fun i => decide (i.bus < A.numBuses) && decide (i.mult.length ≤ 25)) &&
  T.allConstraints.all (fun e => decide (e.degree ≤ d)) &&
  decide (1 ≤ T.maxLog) && decide (T.maxLog ≤ heightCap)

def airWf (heightCap : Nat) (A : Air) (d : Nat) : Bool :=
  A.tables.all (tableWf heightCap A d) && decide (A.multBound ≤ busBudget) &&
    decide (A.fpBound ≤ busBudget)

def publicWf (heightCap : Nat) (AP : AirP) (d : Nat) : Bool :=
  AP.tables.all (tableWf heightCap AP.toAir d) &&
  AP.pubSegs.all (fun s => decide (s.bus < AP.numBuses) && decide (1 ≤ s.width)) &&
  decide (AP.multBoundP ≤ busBudget) && decide (AP.fpBoundP ≤ busBudget)

theorem tableWf_22 (A : Air) (d : Nat) (T : Air.Table) :
    tableWf 22 A d T = T.wf A d := rfl

theorem airWf_22 (A : Air) (d : Nat) : airWf 22 A d = A.wf d := rfl

theorem publicWf_22 (AP : AirP) (d : Nat) : publicWf 22 AP d = AP.wf d := rfl

theorem tableWf_mono {a b : Nat} (hab : a ≤ b) {A : Air} {d : Nat} {T : Air.Table}
    (h : tableWf a A d T = true) : tableWf b A d T = true := by
  simp only [tableWf, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, Nat.le_trans h.2 hab⟩

theorem tableWf_facts {cap : Nat} {A : Air} {d : Nat} {T : Air.Table}
    (h : tableWf cap A d T = true) :
    (∀ e ∈ T.exprs, e.colBound ≤ T.width ∧ e.pubBound ≤ A.numPub) ∧
    (∀ i ∈ T.interactions, i.bus < A.numBuses ∧ i.mult.length ≤ 25) ∧
    (∀ e ∈ T.allConstraints, e.degree ≤ d) ∧ 1 ≤ T.maxLog ∧ T.maxLog ≤ cap := by
  simp only [tableWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem publicWf_air {cap : Nat} {AP : AirP} {d : Nat}
    (h : publicWf cap AP d = true) : airWf cap AP.toAir d = true := by
  simp only [publicWf, airWf, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1.1.1, Nat.le_trans AP.multBound_le h.1.2⟩,
    Nat.le_trans AP.fpBound_le h.2⟩

def headerOk (A : Air) (prm : Params) (hdr : List Nat) : Bool :=
  hdr.length == A.tables.length &&
  (A.tables.zip hdr).all (fun (T, l) => decide (1 ≤ l) && decide (l ≤ T.maxLog)
    && decide (l + prm.logBlowup ≤ prm.maxLogLde) && decide (l + prm.logBlowup ≤ prm.posBits)) &&
  airWf 23 A (2 ^ prm.logBlowup) &&
  (A.tables.all fun T => decide (T.degree prm.auxGroup ≤ 2 ^ prm.logBlowup))

theorem headerOk_facts {A : Air} {prm : Params} {l : List Nat}
    (h : headerOk A prm l = true) :
    l.length = A.tables.length ∧
    (∀ t (ht : t < A.tables.length) (hl : t < l.length),
      1 ≤ l[t] ∧ l[t] ≤ A.tables[t].maxLog ∧
      l[t] + prm.logBlowup ≤ prm.maxLogLde ∧ l[t] + prm.logBlowup ≤ prm.posBits) ∧
    airWf 23 A (2 ^ prm.logBlowup) = true ∧
    (∀ T ∈ A.tables, T.degree prm.auxGroup ≤ 2 ^ prm.logBlowup) := by
  simp only [headerOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hall⟩, hwf⟩, hdeg⟩ := h
  refine ⟨hlen, fun t ht hl => ?_, hwf, hdeg⟩
  have hmem : (A.tables[t], l[t]) ∈ A.tables.zip l := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp; omega, by simp⟩
  have hh := hall _ hmem
  exact ⟨hh.1.1.1, hh.1.1.2, hh.1.2, hh.2⟩

theorem header_log_bounds {A : Air} {g : Nat} {l : List Nat}
    (h : headerOk A (params g) l = true) (t : Nat)
    (ht : t < A.tables.length) (hl : t < l.length) :
    1 ≤ l[t] ∧ l[t] ≤ 23 ∧ l[t] + 4 ≤ 27 := by
  have hf := (headerOk_facts h).2.1 t ht hl
  change 1 ≤ l[t] ∧ l[t] ≤ A.tables[t].maxLog ∧ l[t] + 4 ≤ 27 ∧ l[t] + 4 ≤ 27 at hf
  omega

theorem query_bit_budget (g : Nat) :
    (params g).posPerChunk * (params g).posBits ≤ 256 := by
  change 9 * 27 ≤ 256
  decide

theorem unchanged_proof_cap (g : Nat) : (params g).maxProofBytes = 8 * 2 ^ 20 := rfl

theorem layout_lde_bound {A : Air} {g : Nat} {hdr : List Nat}
    (h : headerOk A (params g) hdr = true) {L : TLayout}
    (hL : L ∈ layout A (params g) hdr) : L.lde ≤ 27 := by
  simp only [headerOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hL
  have hh := h.1.1.2 pair hp
  exact hh.1.2

private theorem fold_max_le (xs : List Nat) (n : Nat)
    (h : ∀ x ∈ xs, x ≤ n) : xs.foldr max 0 ≤ n := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact Nat.max_le.mpr ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

theorem queryLog_bound {A : Air} {g : Nat} {hdr : List Nat}
    (h : headerOk A (params g) hdr = true) : queryLog A (params g) hdr ≤ 27 := by
  apply fold_max_le
  intro x hx
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx
  exact layout_lde_bound h hL

end ZkFormal.V2.Log23
