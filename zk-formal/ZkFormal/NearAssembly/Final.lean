import ZkFormal.NearAssembly.Certificate
import ZkFormal.Near.Final
import ZkFormal.Near.Main
import ZkFormal.Near.BudgetCheck
import ZkFormal.Near.NpOkCheck

/-!
# ZkFormal.NearAssembly.Final — M5: the NEAR admission certificate, wired to lane L6

`near_certificate`: the judge's `AdmissionStatement` for the NEAR challenge parameters
(native-lean, model `nearModel nearAir`), from exactly three remaining inputs:

| input | statement | owner |
|---|---|---|
| `hR` | `Near.RenderStmt` (honest trace satisfies `Holds`) | L6 (Render) |
| `hmin` | `NearMinHeightStmt`: some table of the honest trace has ≥ 16 rows (query domain ≥ 2^8, R-L7-1) | L6 (Render: pad, or the SHA table always has ≥ 1 block = 17 rows) |
| `hsz` | `NearSizeStmt`: `sizeBound ≤ 8 MiB` at every admissible NEAR header (5 127 343 B at the max header) | L7 (`lane/zk-L7-size`) |

Everything else is proved: soundness (`Near.nearAir_sound_closed`), `NpOk` (`nearAir_npOk`),
`NVu`, the static header facts, the table counts, and the whole protocol layer (`np_admission`).
-/

namespace ZkFormal.NearAssembly

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- Some table of the honest trace has at least 16 rows. -/
def NearMinHeightStmt : Prop :=
  ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w →
    ∃ t, t < nearAir.tables.length ∧ 4 ≤ (honestTrace c w).log t

/-- The proof-size bound at every admissible NEAR header. -/
def NearSizeStmt : Prop :=
  ∀ hdr, (Vd nearAir).headerOk hdr = true → sizeBound (Vd nearAir) hdr ≤ 8388608

theorem near_nvu : NVu nearAir Params.default ≤ 2 ^ 30 := by decide +kernel

theorem near_degree : nearAir.tables.all (fun T =>
    decide (T.degree Params.default.auxGroup ≤ 2 ^ Params.default.logBlowup)) = true := by decide +kernel

theorem near_maxLog : nearAir.tables.all (fun T => decide (T.maxLog ≤ 22)) = true := by decide

/-- Generic: a trace whose heights are within `[2, 2^maxLog]` has an admissible header
(given the static AIR facts), and its query domain is at least `2^(log t + 4)`. -/
theorem headerOk_of_logs (A : Air) (tr : Trace Fp)
    (hlog : ∀ t (ht : t < A.tables.length), 1 ≤ tr.log t ∧ tr.log t ≤ A.tables[t].maxLog)
    (h22 : A.tables.all (fun T => decide (T.maxLog ≤ 22)) = true)
    (hwf : A.wf 16 = true)
    (hdeg : A.tables.all (fun T => decide (T.degree Params.default.auxGroup ≤ 2 ^ Params.default.logBlowup)) = true) :
    headerOk A Params.default (trHdr A tr) = true := by
  simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨by simp [trHdr], ?_⟩, hwf⟩, ?_⟩
  · intro p hp
    obtain ⟨t, ht, hpt⟩ : ∃ t, ∃ ht : t < A.tables.length, p = (A.tables[t], tr.log t) := by
      rw [List.mem_iff_getElem] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      simp only [List.length_zip, trHdr, List.length_map, List.length_range, Nat.min_self] at hi
      refine ⟨i, hi, ?_⟩
      rw [← hpi]; simp [trHdr]
    subst hpt
    have h1 := hlog t ht
    have h2 : A.tables[t].maxLog ≤ 22 := by
      simp only [List.all_eq_true, decide_eq_true_eq] at h22
      exact h22 _ (List.getElem_mem ht)
    show ((1 ≤ tr.log t ∧ tr.log t ≤ A.tables[t].maxLog) ∧ tr.log t + 4 ≤ 26) ∧ tr.log t + 4 ≤ 26
    omega
  · simpa only [List.all_eq_true, decide_eq_true_eq] using hdeg

theorem queryLog_ge_log (A : Air) (tr : Trace Fp) (t : Nat) (ht : t < A.tables.length) :
    tr.log t + 4 ≤ queryLog A Params.default (trHdr A tr) := by
  have hmem : tr.log t + 4 ∈ (layout A Params.default (trHdr A tr)).map (·.lde) := by
    simp only [layout, List.mem_map, trHdr]
    refine ⟨_, ⟨(A.tables[t], tr.log t), ?_, rfl⟩, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp [ht], by simp⟩
  exact le_foldr_max hmem

theorem near_fits (hR : RenderStmt) (hmin : NearMinHeightStmt) (c : WfClaim) (w : Witness)
    (h : NearRelation c.1 w) : (Vd nearAir).headerOk (trHdr nearAir (honestTrace c w)) = true := by
  have h1 := headerOk_of_logs nearAir _ (honestTrace_fits' hR h) near_maxLog Budget.nearAir_wf near_degree
  obtain ⟨t, ht, h4⟩ := hmin c w h
  have h2 := queryLog_ge_log nearAir (honestTrace c w) t ht
  generalize hq : queryLog nearAir Params.default (trHdr nearAir (honestTrace c w)) = q at h2
  generalize hH : trHdr nearAir (honestTrace c w) = H at h1 hq
  show (headerOk nearAir Params.default H && decide (minQueryLog ≤ queryLog nearAir Params.default H)) = true
  rw [h1, hq]
  exact decide_eq_true (show 8 ≤ q by omega)

/-- L6's facts for `nearAir`, from the two remaining L6 inputs and the size bound. -/
theorem near_l6Facts (hR : RenderStmt) (hmin : NearMinHeightStmt) (hsz : NearSizeStmt) :
    L6Facts nearAir honestTrace where
  sound := fun c tr h => nearAir_sound_closed c tr h
  complete := fun c w h => nearAir_complete' hR c w h
  fits := near_fits hR hmin
  nonempty := by decide
  tables := by decide
  size := hsz
  nvu := near_nvu
  npOk := nearAir_npOk

/-- **M5: admission on the NEAR challenge** for the deployed model `nearModel nearAir`. -/
theorem near_certificate (hR : RenderStmt) (hmin : NearMinHeightStmt) (hsz : NearSizeStmt)
    (pid model : String) (tb : Nat) (allowed : List String) (fuel rfuel : Nat)
    (pub : ArenaCore.Bytes) (pd bd : ArenaCore.Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed) (hpub : ArenaCore.sha256 pub = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd, impl := .nativeTrusted bd tid (nearModel nearAir) } :=
  near_admission nearAir honestTrace (near_l6Facts hR hmin hsz) pid model tb allowed fuel rfuel pub pd bd
    tid hmodel htb hallowed hpub

end ZkFormal.NearAssembly
