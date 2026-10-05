import ZkFormal.Near.Render.Proof.Base
import ZkFormal.Sha.Complete.All

/-!
# ZkFormal.Near.Render.Proof.ShaTab — the `sha` table of `render` is L5's honest trace

Table `0` of `render c e` is, cell by cell and in height, L5's
`Sha.honestTrace (shaMsgsOf c e)`.  L5's closed completeness theorem
(`Sha.Complete.sha_complete_closed`) then gives `ShaLocalStmt` and
`ShaTrafficStmt` for every `Ext` whose messages are supported
(`Sha.MsgsOk`: bytes `< 256`, lengths `< 2^25`, at most `2^22` rows):
`shaLocal_of_ok`, `shaTraffic_of_ok`.  `MsgsOk` under `Good ∧ Small` is
`Proof/ShaFit*`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- The SHA messages of the honest trace (every digest provided once). -/
def shaMsgsOf (c : Claim) (e : Ext) : List Sha.Gen.Msg := shaMsgs (bundle c e).msgs

section congr
variable {tr₁ tr₂ : Trace Fp} {t : Nat} (hl : tr₁.log t = tr₂.log t) (hc : tr₁.cell t = tr₂.cell t)
include hl hc

theorem rowEnv_congr (r : Nat) (pub : List Fp) : rowEnv tr₁ t r pub = rowEnv tr₂ t r pub := by
  unfold rowEnv Trace.height; rw [hl, hc]

theorem eval_congr (e : Expr) (r : Nat) (pub : List Fp) : e.eval tr₁ t r pub = e.eval tr₂ t r pub := by
  unfold Expr.eval; rw [rowEnv_congr hl hc]

theorem multNat_congr (i : Interaction) (r : Nat) (pub : List Fp) :
    i.multNat tr₁ t r pub = i.multNat tr₂ t r pub := by
  unfold Interaction.multNat
  generalize 0 = k
  induction i.mult generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [Interaction.multNat.go]
    rw [ih, show b.eval tr₁ t r pub = b.eval tr₂ t r pub from eval_congr hl hc b r pub]

theorem msgVal_congr (i : Interaction) (r : Nat) (pub : List Fp) :
    i.msgVal tr₁ t r pub = i.msgVal tr₂ t r pub := by
  simp only [Interaction.msgVal, eval_congr hl hc]

theorem tableBusCount_congr (is : List Interaction) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount is tr₁ t pub b s m = tableBusCount is tr₂ t pub b s m := by
  simp only [tableBusCount, Trace.height, hl, msgVal_congr hl hc, multNat_congr hl hc]

end congr

theorem render_sha_log (c : Claim) (e : Ext) :
    (render c e).log T_SHA = (Sha.honestTrace (shaMsgsOf c e)).log T_SHA := rfl

theorem render_sha_cell (c : Claim) (e : Ext) :
    (render c e).cell T_SHA = (Sha.honestTrace (shaMsgsOf c e)).cell T_SHA := by
  funext r col
  simp [render, renderParts, Sha.honestTrace, Sha.Gen.honestCell, shaMsgsOf, T_SHA]

/-- No interaction of a table is on bus `b`: it carries nothing there. -/
theorem tableBusCount_off (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat)
    (s : Bool) (m : List Fp) (h : ∀ i ∈ is, i.bus ≠ b) : tableBusCount is tr t pub b s m = 0 := by
  simp only [tableBusCount]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldr_cons, ih]
    clear ih
    induction is with
    | nil => rfl
    | cons i is ih' =>
      rw [List.foldr_cons, ih' (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      have := h i (List.mem_cons_self ..)
      simp [this]

theorem sha_bus_cases (i : Interaction) (hi : i ∈ Sha.Table.interactions B_BYTES B_DIGEST) :
    i.bus = B_BYTES ∨ i.bus = B_DIGEST := by
  simp only [Sha.Table.interactions, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ⟨q, -, rfl⟩ | rfl
  · exact .inl rfl
  · exact .inr rfl

/-- **`ShaLocal` for supported messages.** -/
theorem shaLocal_of_ok (c : WfClaim) (e : Ext) (hok : Sha.MsgsOk (shaMsgsOf c.1 e)) :
    TableLocal (Sha.Table.table B_BYTES B_DIGEST) (render c.1 e) T_SHA (publicOf c) := by
  obtain ⟨hL, hB, -⟩ := Sha.Complete.sha_complete_closed _ hok T_SHA (publicOf c)
  have hl := render_sha_log c.1 e
  have hc := render_sha_cell c.1 e
  have hH : (render c.1 e).height T_SHA = (Sha.honestTrace (shaMsgsOf c.1 e)).height T_SHA := by
    simp only [Trace.height, hl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hl]; exact hL.log_ge
  · rw [hl]; exact hL.log_le
  · intro r hr e' he
    rw [eval_congr hl hc]
    exact hL.constr r (hH ▸ hr) e' he
  · intro r hr i hi b hb
    rw [eval_congr hl hc]
    exact hB r (hH ▸ hr) B_BYTES B_DIGEST i hi b hb

/-- **`ShaTraffic` for supported messages.** -/
theorem shaTraffic_of_ok (c : WfClaim) (e : Ext) (hok : Sha.MsgsOk (shaMsgsOf c.1 e)) :
    TableTraffic (Sha.Table.interactions B_BYTES B_DIGEST) (render c.1 e) T_SHA (publicOf c)
      (htf c.1 e T_SHA) := by
  obtain ⟨-, -, hT⟩ := Sha.Complete.sha_complete_closed _ hok T_SHA (publicOf c)
  have hl := render_sha_log c.1 e
  have hc := render_sha_cell c.1 e
  have hf : htf c.1 e T_SHA = shaTraffic (bundle c.1 e).msgs := rfl
  intro b m
  rw [tableBusCount_congr hl hc, tableBusCount_congr hl hc, hf]
  have hT' := fun m => hT (shaMsgsOf c.1 e) hok T_SHA (publicOf c) B_BYTES B_DIGEST (by decide) m
  simp only [shaTraffic]
  by_cases h0 : b = B_BYTES
  · subst h0
    obtain ⟨h1, h2, -, -⟩ := hT' m
    simp only [B_BYTES, B_DIGEST, ite_true, Nat.zero_ne_one, ite_false, List.map_nil, List.count_nil]
    exact ⟨h2, h1⟩
  · by_cases h1 : b = B_DIGEST
    · subst h1
      obtain ⟨-, -, h3, h4⟩ := hT' m
      simp only [B_BYTES, B_DIGEST, ite_true, Nat.one_ne_zero, ite_false, List.map_nil, List.count_nil]
      exact ⟨h3, h4⟩
    · simp only [h0, h1, ite_false, List.map_nil, List.count_nil]
      have hoff : ∀ i ∈ Sha.Table.interactions B_BYTES B_DIGEST, i.bus ≠ b := by
        intro i hi; rcases sha_bus_cases i hi with h | h <;> rw [h] <;> omega
      exact ⟨tableBusCount_off _ _ _ _ _ _ _ hoff, tableBusCount_off _ _ _ _ _ _ _ hoff⟩

end ZkFormal.Near.Render
