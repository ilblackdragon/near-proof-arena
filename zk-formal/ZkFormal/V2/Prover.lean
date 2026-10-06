import ZkFormal.Prover.NpLocalMain
import ZkFormal.Prover.NpBus4
import ZkFormal.V2.RomFull

/-!
# ZkFormal.V2.Prover — completeness of np-udr-stark-v2 (lane L7 prover model)

The v2 honest prover is **v1's honest prover** (`Prover.Np.npProver AP.toAir cb tr`): the proof
bytes do not change, and the verifier recomputes the public products from the claim.
`npIopCompleteP` is the analogue of v1's `npIopComplete'`, for traces satisfying `HoldsP`.

What changes, and where:
* v1's local lemmas use `Holds` only through `constr` and `bits`, which `HoldsP` has with the
  same types.  They are restated for `HoldsP` (`…P`, proofs copied).
* `busProdP`: the honest finals satisfy v2's bus equation
  `∏ send finals · Π_pub(send) = ∏ recv finals · Π_pub(recv)`.  It is v1's `busProd` on the
  entry lists extended by the public messages, with `HoldsP.balance`.
* `globalP`: v2's clear-text checks pass (`okLens` as in v1, `pubFit` from `HoldsP`, and
  `globalChecksP`).
* `localNH`: v1's local checks pass on the honest transcript.  v1's proof never uses `Holds`;
  this is the same proof without that hypothesis.
* Shape, reachability and well-formedness transfer from v1, because the v2 IOP has v1's
  schedule and header check.

Completeness is proved for the deployed parameters (`auxGroup = 1`): the prover model is
v1's, and it is defined at `Params.default`.
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

attribute [local instance] Semiring.natCast

section
variable (AP : AirP) (cb : Bytes) (tr : Trace Fp)

/-- The AIR constraints and booleanity vanish on the trace domain. -/
theorem allConstraints_rowP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t)
    {r : Nat} (hr : r < 2 ^ lg tr t) :
    ∀ e ∈ (tb AP.toAir t).allConstraints, e.evalWith (pEnv AP.toAir cb tr t (omg (lg tr t) ^ r)) = 0 := by
  intro e he
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  rw [evalWith_row AP.toAir cb tr t hlog hr e (colBound_allConstraints AP.toAir ht.wf e he)]
  have hT := tb_eq AP.toAir ht.lt
  rcases List.mem_append.mp he with he | he
  · rw [hH.constr t ht.lt r hr e (by rw [← hT]; exact he)]; rfl
  · simp only [Table.bitConstraints, List.mem_flatMap, List.mem_map] at he
    obtain ⟨i, hi, b, hb, rfl⟩ := he
    have hb01 := hH.bits t ht.lt r hr i (by rw [← hT]; exact hi) b hb
    show Fp8.ofBase (b.eval tr t r (pubOf Fp cb) * (b.eval tr t r (pubOf Fp cb) +
      - @Nat.cast Fp Semiring.natCast 1)) = 0
    rcases hb01 with h | h <;> rw [h] <;> decide +kernel

/-- **The honest factor of an interaction on row `r`.** -/
theorem phi_rowP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ : Fp8)
    {r : Nat} (hr : r < 2 ^ lg tr t) {i : Interaction} (hi : i ∈ (tb AP.toAir t).interactions) :
    (chainOf (rEnv AP.toAir cb tr t r) α γ i).2 =
      (γ - FPv α i.bus (i.msgVal tr t r (pubOf Fp cb))) ^ (i.multNat tr t r (pubOf Fp cb)) := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  have hcol := colBound_inter AP.toAir ht.wf hi
  have hev : ∀ e ∈ i.mult ++ i.msg, e.evalWith (rEnv AP.toAir cb tr t r) = Fp8.ofBase (e.eval tr t r (pubOf Fp cb)) :=
    fun e he => evalWith_row AP.toAir cb tr t hlog hr e (hcol e he)
  have hbits : ∀ v ∈ i.mult.map (·.evalWith (rEnv AP.toAir cb tr t r)), v = 0 ∨ v = 1 := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
    rw [hev b (List.mem_append_left _ hb)]
    rcases hH.bits t ht.lt r hr i (by rw [← tb_eq AP.toAir ht.lt]; exact hi) b hb with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hfp : fingerprint (rEnv AP.toAir cb tr t r) α i = FPv α i.bus (i.msgVal tr t r (pubOf Fp cb)) := by
    unfold fingerprint FPv Interaction.msgVal
    rw [fp_fold_eval (rEnv AP.toAir cb tr t r) α (fun e => e.eval tr t r (pubOf Fp cb)) i.msg (0, 1)
      (fun e he => hev e (List.mem_append_right _ he))]
  rw [chain_phi _ α γ i hbits, goV_eval AP.toAir cb tr t r i.mult 0 (fun b hb => hev b (List.mem_append_left _ hb)),
    hfp]
  rfl

/-- **Every constraint vanishes on the honest columns on the trace domain.** -/
theorem csX_row_zeroP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ : Fp8)
    {r : Nat} (hr : r < 2 ^ lg tr t) : ∀ c ∈ csX AP.toAir cb tr α γ t (omg (lg tr t) ^ r), c = 0 := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  intro c hc
  unfold csX at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact allConstraints_rowP AP cb tr hH ht hr e he
  rw [auxConstraints_eq, auxV_row AP.toAir cb tr α γ t hlog hr, omg_mul_pow tr t hlog,
    auxV_row AP.toAir cb tr α γ t hlog (Nat.mod_lt _ (Nat.two_pow_pos _))] at hc
  rw [show pEnv AP.toAir cb tr t (omg (lg tr t) ^ r) = rEnv AP.toAir cb tr t r from rfl] at hc
  obtain ⟨c', hc', hf⟩ := fold_chains (rEnv AP.toAir cb tr t r) α γ (tb AP.toAir t).interactions [] []
    ((List.range (nG AP.toAir t)).map (accAt AP.toAir cb tr α γ t r)) (by simp)
  unfold myAux at hc
  unfold auxRow at hc
  rw [hf] at hc
  simp only [List.nil_append, List.length_append, List.length_map, List.length_range,
    Nat.add_sub_cancel] at hc
  rw [chainsOf_length, ← chainsOf_length (rEnv AP.toAir cb tr t ((r + 1) % 2 ^ lg tr t)) α γ,
    List.drop_left] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hc' c hc
  · exact gc_zero AP.toAir cb tr α γ hlog hr c hc

/-- **The quotient exists** (honest trace satisfying `Holds`). -/
theorem quot_existsP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ αc : Fp8) :
    ∃ co : Nat → Fp8, ∀ x, compX AP.toAir cb tr α γ αc t x =
      (x ^ (2 ^ lg tr t) - 1) * ev ((tb AP.toAir t).quotCount dp.auxGroup * 2 ^ lg tr t) co x := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  have hT : 1 ≤ 2 ^ lg tr t := Nat.one_le_two_pow
  obtain ⟨c, hc⟩ := compX_isPoly AP.toAir cb tr t α γ αc
  have hz : ∀ r, r < 2 ^ lg tr t → ev ((tb AP.toAir t).degree dp.auxGroup * (2 ^ lg tr t - 1) + 1) c
      (omg (lg tr t) ^ r) = 0 := by
    intro r hr
    rw [← hc]
    exact combine_zero αc _ (csX_row_zeroP AP cb tr hH ht α γ hr)
  obtain ⟨q, hq⟩ := exists_div_vanish hT (fun r => omg (lg tr t) ^ r) (npDistinct_omg hlog)
    (fun r _ => omg_pow_r_T hlog r) c hz
  have hD : 1 ≤ (tb AP.toAir t).degree dp.auxGroup := by
    have := (degree_facts (tb AP.toAir t)).1; exact Nat.le_trans (by decide) this
  obtain ⟨c', hc'⟩ := ev_mono_pad (m := (tb AP.toAir t).degree dp.auxGroup * (2 ^ lg tr t - 1) + 1 - 2 ^ lg tr t)
    (m' := (tb AP.toAir t).quotCount dp.auxGroup * 2 ^ lg tr t) (by
      unfold Table.quotCount
      have e1 : ((tb AP.toAir t).degree dp.auxGroup - 1) * 2 ^ lg tr t =
          (tb AP.toAir t).degree dp.auxGroup * 2 ^ lg tr t - 2 ^ lg tr t := by
        rw [Nat.sub_mul, Nat.one_mul]
      have e2 : (tb AP.toAir t).degree dp.auxGroup * (2 ^ lg tr t - 1) =
          (tb AP.toAir t).degree dp.auxGroup * 2 ^ lg tr t - (tb AP.toAir t).degree dp.auxGroup := by
        rw [Nat.mul_sub, Nat.mul_one]
      have e3 : (tb AP.toAir t).degree dp.auxGroup ≤ (tb AP.toAir t).degree dp.auxGroup * 2 ^ lg tr t :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      rw [e1, e2]; omega) q
  exact ⟨c', fun x => by rw [hc x, hq x, hc' x]⟩

theorem qC_specP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ αc : Fp8) :
    ∀ x, compX AP.toAir cb tr α γ αc t x =
      (x ^ (2 ^ lg tr t) - 1) * ev ((tb AP.toAir t).quotCount dp.auxGroup * 2 ^ lg tr t) (qC AP.toAir cb tr α γ αc t) x := by
  unfold qC
  exact pick_spec (quot_existsP AP cb tr hH ht α γ αc)

/-- **The ALI identity** of table `t` at an out-of-domain point. -/
theorem ali_tableP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ αc : Fp8)
    {z : Fp8} (hz : ¬ z.IsBase) :
    combine αc (((tb AP.toAir t).allConstraints.map (·.evalWith (oodEnv (F := Fp)
        (cb.map fun b => ofNatF b.toNat) (tr.log t) z (mainV AP.toAir tr t z) (mainV AP.toAir tr t (omg (lg tr t) * z))))) ++
      auxConstraints (tb AP.toAir t) dp.auxGroup (oodEnv (F := Fp) (cb.map fun b => ofNatF b.toNat) (tr.log t) z
        (mainV AP.toAir tr t z) (mainV AP.toAir tr t (omg (lg tr t) * z))) α γ (auxV AP.toAir cb tr α γ t z)
        (auxV AP.toAir cb tr α γ t (omg (lg tr t) * z)) (finsT AP.toAir cb tr α γ t)) =
      (z ^ (2 ^ tr.log t) - 1) * combine (z ^ (2 ^ tr.log t)) (quotV AP.toAir cb tr α γ αc t z) := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  rw [oodEnv_eq AP.toAir cb tr t hlog hz]
  show compX AP.toAir cb tr α γ αc t z = _
  rw [qC_specP AP cb tr hH ht α γ αc z, ev_chunks]
  rfl

theorem rows_sideP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ : Fp8) (s : Bool)
    (k : Nat) (f : Nat → Nat) (hk : k = ((tb AP.toAir t).interactions.filter fun i => i.send == s).length)
    (hf : ∀ r, prodF ((List.range k).map fun j => phiG (rEnv AP.toAir cb tr t r) α γ (tb AP.toAir t).interactions (f j)) =
      prodF (((tb AP.toAir t).interactions.filter fun i => i.send == s).map
        fun i => (chainOf (rEnv AP.toAir cb tr t r) α γ i).2)) :
    prodF ((List.range k).map fun j => accAt AP.toAir cb tr α γ t (2 ^ lg tr t) (f j)) = sideProd AP.toAir cb tr α γ t s := by
  simp only [accAt_prod]
  rw [prodF_swap (fun j r => phiG (rEnv AP.toAir cb tr t r) α γ (tb AP.toAir t).interactions (f j))]
  unfold sideProd
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [hf r]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact phi_rowP AP cb tr hH ht α γ (List.mem_range.mp hr) (List.mem_filter.mp hi).1

theorem sends_tableP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ : Fp8) :
    ((finsT AP.toAir cb tr α γ t).take (layT AP.toAir tr t).sendG).foldl (· * ·) 1 = sideProd AP.toAir cb tr α γ t true := by
  have hk : (layT AP.toAir tr t).sendG = ((tb AP.toAir t).interactions.filter fun i => i.send == true).length :=
    numSide_eq _ true
  have hle : (layT AP.toAir tr t).sendG ≤ nG AP.toAir t := by unfold nG; exact Nat.le_add_right _ _
  show prodF _ = _
  unfold finsT
  rw [← List.map_take, List.take_range, Nat.min_eq_left hle]
  refine rows_sideP AP cb tr hH ht α γ true _ id hk fun r => ?_
  have := prod_phiG_send (rEnv AP.toAir cb tr t r) α γ (tb AP.toAir t).interactions
  simp only [beq_true] at hk ⊢
  rw [hk]; exact this

theorem recvs_tableP (hH : HoldsP AP (pubOf Fp cb) tr) {t : Nat} (ht : TabOk AP.toAir tr t) (α γ : Fp8) :
    ((finsT AP.toAir cb tr α γ t).drop (layT AP.toAir tr t).sendG).foldl (· * ·) 1 = sideProd AP.toAir cb tr α γ t false := by
  have hk : (layT AP.toAir tr t).sendG = ((tb AP.toAir t).interactions.filter fun i => i.send == true).length :=
    numSide_eq _ true
  have hk' : (layT AP.toAir tr t).recvG = ((tb AP.toAir t).interactions.filter fun i => i.send == false).length :=
    numSide_eq _ false
  show prodF _ = _
  unfold finsT
  rw [show nG AP.toAir t = (layT AP.toAir tr t).sendG + (layT AP.toAir tr t).recvG from rfl, List.range_add, List.map_append,
    List.drop_left' (by simp), List.map_map]
  refine rows_sideP AP cb tr hH ht α γ false _ _ hk' fun r => ?_
  have := prod_phiG_recv (rEnv AP.toAir cb tr t r) α γ (tb AP.toAir t).interactions
  simp only [beq_true, beq_false] at hk hk' ⊢
  rw [hk', hk]; exact this


end

section

theorem localNH (A : Air) (cb : Bytes) (tr : Trace Fp) (hok : headerOk A dp (hdr A tr) = true)
    (cs : List Fp8) (hlen : cs.length = nMsg A tr) (hz : ¬ (cs.getD 3 0).IsBase) (x : Nat)
    (hx : x < 2 ^ n0 A tr) :
    (Vd A).ChecksPass (honT A cb tr cs) x ((Vd A).trueOpenings (honT A cb tr cs) x) := by
  have hf := ctxFacts A cb tr cs hlen
  unfold IopSpec.ChecksPass
  rw [trueOpenings_hon]
  show checkAt (F := Fp) ((Vd A).prep (honT A cb tr cs).erase) x (hOps A cb tr cs x) = true
  have hdeep := deep_hon A cb tr cs hlen x
  generalize (Vd A).prep (honT A cb tr cs).erase = c at hf hdeep
  unfold checkAt
  dsimp only
  rw [hf.ok, hf.commits, hf.ell, hf.n0, hf.fp, hf.gammas, hOps_drop]
  simp only [hdeep]
  have hn := n0_le A tr hok
  have hℓ : ell A tr ≤ n0 A tr := ZkFormal.Stark.finalLayer_le_queryLog A dp (hdr A tr)
  have h0 : Bw A cb tr cs (n0 A tr) (x >>> (n0 A tr - n0 A tr)) = preAt A cb tr cs x 0 := by
    simp [preAt, word]
  rw [h0, chain_fold (rollInAt A dp (hdr A tr)) (ell A tr) (preAt A cb tr cs x) _ _ ?hF 0 (commits A tr)
    (Nat.zero_le _) (commits_chain A tr)]
  case hF =>
    intro c0 a ha hca hno
    dsimp only
    have hv : ∀ v : Fp8, v = word A cb tr cs c0 (x >>> c0) → (true &&
        (decide ((ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 [])).getD
          (x >>> c0 % 2 ^ a) 0 = v) &&
         decide ((ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 [])).length =
          2 ^ a)),
        foldLeaf (F := Fp) c c0 a (x >>> c0 >>> a)
          (ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 []))) =
        (true, preAt A cb tr cs x (c0 + a)) := by
      intro v hv
      rw [hv, leaf_hon A cb tr cs x c0 a (by omega),
        foldLeaf_word A cb tr cs c hf.n0 hf.betas c0 a _ ha (fun i h1 h2 => gammaL_none A tr cs (hno i h1 h2))]
      have hmod : x >>> c0 % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hmod]
      have hpos : (x >>> c0 >>> a) * 2 ^ a + (x >>> c0) % 2 ^ a = x >>> c0 := by
        rw [Nat.shiftRight_eq_div_pow (x >>> c0) a]; exact Nat.div_add_mod' _ _
      simp only [Option.map_some, Option.getD_some, List.length_map, List.length_range, hpos,
        decide_true, Bool.and_self, Bool.true_and]
      simp only [preAt, if_neg (show c0 + a ≠ 0 by omega), Nat.shiftRight_add]
    cases hg : (gammaL A tr cs).lookup c0 with
    | none => dsimp only; exact hv _ (roll_none A cb tr cs x c0 hg)
    | some γ => dsimp only; exact hv _ (roll_some A cb tr cs x c0 (by omega) hg)
  simp only [Bool.true_and, List.length_map, decide_true, Bool.and_true, decide_eq_true_eq]
  have hfin := final_check A cb tr cs hok hlen hz (x >>> ell A tr)
  cases hg : (gammaL A tr cs).lookup (ell A tr) with
  | none => dsimp only; rw [roll_none A cb tr cs x _ hg]; exact hfin
  | some γ => dsimp only; rw [roll_some A cb tr cs x _ hℓ hg]; exact hfin


end

/-! ## The bus product with public messages -/

section
variable (AP : AirP) (cb : Bytes) (tr : Trace Fp)

/-- Public entries of side `s` (multiplicity one each). -/
def pubEntries (s : Bool) : List ((Nat × List Fp) × Nat) :=
  ((pubMsgs AP (pubOf Fp cb)).filter fun x => x.2.1 == s).map fun x => ((x.1, x.2.2), 1)

theorem cntK_ones {κ α : Type} [DecidableEq κ] (k : α → κ) (key : κ) : ∀ L : List α,
    cntK (L.map fun x => (k x, 1)) key = (L.filter fun x => decide (k x = key)).length
  | [] => rfl
  | x :: L => by
    have ih := cntK_ones k key L
    unfold cntK at ih ⊢
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.filter_cons]
    by_cases h : k x = key
    · simp [h]; omega
    · simp [h]

theorem cntK_pub_go (s : Bool) (b : Nat) (m : List Fp) (L : List (Nat × Bool × List Fp)) :
    cntK ((L.filter fun x => x.2.1 == s).map fun x => ((x.1, x.2.2), 1)) (b, m) =
      (L.filter fun x => decide (x = (b, s, m))).length := by
  rw [cntK_ones (fun x : Nat × Bool × List Fp => (x.1, x.2.2)), List.filter_filter]
  congr 1
  apply List.filter_congr
  intro x _
  obtain ⟨xb, xs, xm⟩ := x
  by_cases h1 : xs = s
  · subst h1; by_cases h2 : xb = b <;> by_cases h3 : xm = m <;> simp [h2, h3]
  · have : (xs == s) = false := by simp [h1]
    simp [this, h1]

theorem cnt_pubEntries (s : Bool) (b : Nat) (m : List Fp) :
    cntK (pubEntries AP cb s) (b, m) = pubCount AP (pubOf Fp cb) b s m :=
  cntK_pub_go s b m _

theorem fpv_go (α : Fp8) : ∀ (vs : List Fp8) (a p : Fp8),
    vs.foldl (fun (acc : Fp8 × Fp8) v => (acc.1 + v * acc.2, acc.2 * α)) (a, p) =
      (a + p * combine α vs, p * α ^ vs.length)
  | [], a, p => by
    refine Prod.ext ?_ ?_
    · show a = a + p * 0; grind
    · show p = p * α ^ 0; rw [Semiring.pow_zero]; grind
  | v :: vs, a, p => by
    rw [List.foldl_cons, fpv_go α vs]
    refine Prod.ext ?_ ?_
    · show a + v * p + p * α * combine α vs = a + p * (v + α * combine α vs)
      generalize combine α vs = C
      grind
    · show p * α * α ^ vs.length = p * α ^ (vs.length + 1)
      rw [Semiring.pow_succ]
      generalize α ^ vs.length = P
      grind

/-- The prover model's fingerprint is the verifier's public fingerprint. -/
theorem fpv_eq (α : Fp8) (b : Nat) (m : List Fp) : FPv α b m = pubFp α b m := by
  unfold FPv pubFp
  dsimp only
  rw [fpv_go, combine_snoc]
  have e : (m.map (StarkField.embed (F := Fp) (K := Fp8))) = m.map Fp8.ofBase := rfl
  rw [e, List.length_map]
  generalize combine α (m.map Fp8.ofBase) = C
  generalize α ^ m.length = P
  grind

theorem prodPow_pub (α γ : Fp8) (s : Bool) :
    prodPow (fun k => γ - FPv α k.1 k.2) (pubEntries AP cb s) = pubProd AP (pubOf Fp cb) α γ s := by
  unfold prodPow pubEntries pubProd prodF
  have key : ∀ (L : List (Nat × Bool × List Fp)) (init : Fp8),
      ((L.map fun x => ((x.1, x.2.2), 1)).map fun e => (γ - FPv α e.1.1 e.1.2) ^ e.2).foldl (· * ·) init =
        L.foldl (fun acc x => acc * (γ - pubFp α x.1 x.2.2)) init := by
    intro L
    induction L with
    | nil => intro; rfl
    | cons x L ih =>
      intro init
      simp only [List.map_cons, List.foldl_cons]
      rw [ih, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul, fpv_eq]
  exact key _ 1

/-- **The honest finals satisfy v2's bus equation.** -/
theorem busProdP (hH : HoldsP AP (pubOf Fp cb) tr) (hok : headerOk AP.toAir dp (hdr AP.toAir tr) = true)
    (α γ : Fp8) :
    ((List.range AP.tables.length).map fun t =>
      ((finsT AP.toAir cb tr α γ t).take (layT AP.toAir tr t).sendG).foldl (· * ·) 1).foldl (· * ·) 1 *
        pubProd AP (pubOf Fp cb) α γ true =
      ((List.range AP.tables.length).map fun t =>
        ((finsT AP.toAir cb tr α γ t).drop (layT AP.toAir tr t).sendG).foldl (· * ·) 1).foldl (· * ·) 1 *
        pubProd AP (pubOf Fp cb) α γ false := by
  let g : Nat × List Fp → Fp8 := fun k => γ - FPv α k.1 k.2
  have hside : ∀ s, prodF ((List.range AP.toAir.tables.length).map fun t => sideProd AP.toAir cb tr α γ t s) =
      prodPow g (entries AP.toAir cb tr s) := by
    intro s
    unfold prodPow entries
    rw [List.map_flatMap, prodF_flatMap]
    congr 1; apply List.map_congr_left; intro t _
    unfold sideProd
    rw [List.map_flatMap, prodF_flatMap]
    congr 1; apply List.map_congr_left; intro r _
    rw [List.map_map]; rfl
  have hl : ∀ s, ((List.range AP.toAir.tables.length).map fun t =>
      (if s then ((finsT AP.toAir cb tr α γ t).take (layT AP.toAir tr t).sendG).foldl (· * ·) 1
       else ((finsT AP.toAir cb tr α γ t).drop (layT AP.toAir tr t).sendG).foldl (· * ·) 1)) =
      (List.range AP.toAir.tables.length).map fun t => sideProd AP.toAir cb tr α γ t s := by
    intro s
    apply List.map_congr_left; intro t ht
    have hto := tabOk AP.toAir tr hok (List.mem_range.mp ht)
    cases s
    · exact recvs_tableP AP cb tr hH hto α γ
    · exact sends_tableP AP cb tr hH hto α γ
  have h1 := hl true
  have h2 := hl false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
  have ef : ∀ l : List Fp8, l.foldl (· * ·) 1 = prodF l := fun _ => rfl
  rw [ef, ef, h1, h2, hside true, hside false, ← prodPow_pub AP cb α γ true, ← prodPow_pub AP cb α γ false]
  have happ : ∀ E E' : List ((Nat × List Fp) × Nat), prodPow g E * prodPow g E' = prodPow g (E ++ E') := by
    intro E E'; unfold prodPow; rw [List.map_append, prodF_append]
  rw [happ, happ]
  apply prodPow_eq g _ _ _ (Nat.le_refl _)
  intro k
  obtain ⟨b, m⟩ := k
  have hc : ∀ E E' : List ((Nat × List Fp) × Nat), cntK (E ++ E') (b, m) = cntK E (b, m) + cntK E' (b, m) := by
    intro E E'; unfold cntK; rw [List.map_append, List.sum_append]
  rw [hc, hc, cnt_entries, cnt_entries, cnt_pubEntries, cnt_pubEntries, hH.balance]

theorem globalChecks_honP (hH : HoldsP AP (pubOf Fp cb) tr)
    (hok : headerOk AP.toAir dp (hdr AP.toAir tr) = true) (α γ αc z : Fp8) (hz : ¬ z.IsBase) :
    globalChecksP (F := Fp) AP dp (cb.map fun b => ofNatF b.toNat) (layout AP.toAir dp (hdr AP.toAir tr))
      ((List.range AP.tables.length).map (oodRec AP.toAir cb tr α γ αc z)) (finalsAll AP.toAir cb tr α γ)
      α γ αc z = true := by
  unfold globalChecksP
  dsimp only
  rw [fins_hon]
  have hT : AP.toAir.tables = (List.range AP.toAir.tables.length).map (tb AP.toAir) := tables_eq AP.toAir
  have e : finalsAll AP.toAir cb tr α γ = (List.range AP.toAir.tables.length).flatMap (finsT AP.toAir cb tr α γ) ++ [] := by
    rw [List.append_nil]; rfl
  rw [lay_eq]
  have hB' := busProdP AP cb tr hH hok α γ
  generalize hn : AP.toAir.tables.length = n at hT e hB' ⊢
  rw [hT, zip_map_range, zip_map_range, zip_map_range]
  rw [foldl_tables _ (fun t => (tb AP.toAir t, layT AP.toAir tr t, oodRec AP.toAir cb tr α γ αc z t)) (finsT AP.toAir cb tr α γ) _ [] _ e
    ?step]
  case step =>
    intro t ht R
    have htn : t < AP.toAir.tables.length := by rw [hn]; exact List.mem_range.mp ht
    have hto := tabOk AP.toAir tr hok htn
    have hl : (finsT AP.toAir cb tr α γ t).length = (layT AP.toAir tr t).sendG + (layT AP.toAir tr t).recvG := by
      simp [finsT, layT_sendRecv]
    dsimp only
    rw [List.take_left' hl, List.drop_left' hl]
    dsimp only [layT, oodRec]
    simp only [ali_tableP AP cb tr hH hto α γ αc hz, decide_true, Bool.and_self]
  simp only [Bool.true_and, decide_eq_true_eq]
  rw [List.map_map, List.map_map]
  exact hB'

end

/-- The v2 deployed IOP verifier. -/
abbrev VdP (AP : AirP) : IopSpec Fp Fp8 := Iop.verifierP Fp Fp8 AP dp

/-- **v2's clear-text checks pass on every honest complete transcript.** -/
theorem globalP (AP : AirP) (cb : Bytes) (tr : Trace Fp) (hH : HoldsP AP (pubOf Fp cb) tr)
    (hok : headerOk AP.toAir dp (hdr AP.toAir tr) = true) (cs : List Fp8)
    (hlen : cs.length = nMsg AP.toAir tr) (hz : ¬ (cs.getD 3 0).IsBase) :
    (VdP AP).global ((VdP AP).prep (honT AP.toAir cb tr cs).erase) = true := by
  have h4 : 4 ≤ cs.length := by rw [hlen, nMsg_eq]; omega
  obtain ⟨a, b, c, d, rest, rfl⟩ : ∃ a b c d rest, cs = a :: b :: c :: d :: rest := by
    match cs, h4 with
    | a :: b :: c :: d :: rest, _ => exact ⟨a, b, c, d, rest, rfl⟩
  change (prepP (F := Fp) AP dp (honT AP.toAir cb tr (a :: b :: c :: d :: rest)).erase).globalOk = true
  rw [prepP_eq]
  change globalOkP (F := Fp) (K := Fp8) AP dp (honT AP.toAir cb tr (a :: b :: c :: d :: rest)).erase = true
  unfold globalOkP
  rw [erase_header, honT_header, erase_chals, honT_chals AP.toAir cb tr _ hlen, erase_elems, honT_elems]
  dsimp only
  rw [show oodC AP.toAir cb tr (a :: b :: c :: d :: rest) = oodAll AP.toAir cb tr a b c d from rfl, splitOod_hon]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hn := nMsg_eq AP.toAir tr
  refine ⟨⟨⟨⟨⟨by rw [hn] at hlen; simp [nB, kinds] at hlen ⊢; omega, rfl⟩,
    finalsAll_length AP.toAir cb tr _ _⟩, oodAll_length AP.toAir cb tr _ _ _ _⟩, hH.pubFit⟩, ?_⟩
  exact globalChecks_honP AP cb tr hH hok _ _ _ _ hz

/-! ## Transfer of shape facts from v1 -/

section
variable (AP : AirP)

theorem reach_v1 {pr : IopProver Fp Fp8} {cb : Bytes} {τ : PT Fp8 (Oracle Fp)}
    (h : Reach (VdP AP) pr cb τ) : Reach (Vd AP.toAir) pr cb τ := by
  induction h with
  | init => exact .init
  | msg τ _ hn ih => exact .msg τ ih ((V2.Np.nextIsProver_iff AP dp τ).mp hn)
  | chal τ ood y _ hs ih => exact .chal τ ood y ih (by rw [← V2.Np.slots_eq AP dp τ]; exact hs)

theorem proverWfP {pr : IopProver Fp Fp8} {cb : Bytes} (h : ProverWf (Vd AP.toAir) pr cb) :
    ProverWf (VdP AP) pr cb :=
  ⟨h.hdrOk, h.hdrLen, h.hdrSmall, h.tablesSmall,
    fun τ hr => (V2.Np.shaped_iff AP dp τ).mpr (h.shaped τ (reach_v1 AP hr)),
    fun τ hr hne => h.header τ (reach_v1 AP hr) hne,
    fun τ hr hn l hl => h.hdrParts τ (reach_v1 AP hr) ((V2.Np.nextIsProver_iff AP dp τ).mp hn) l hl⟩

end

/-- (N1-v2) Completeness of the np-udr-stark-v2 IOP: v1's honest prover is accepted on every
trace satisfying `HoldsP`. -/
def NpIopCompleteStmtP : Prop :=
  ∀ (AP : AirP) (cb : Bytes) (tr : Trace Fp), AP.tables.length < 2 ^ 32 →
    HoldsP AP (Udr.pubOf Fp cb) tr → (Iop.verifierP Fp Fp8 AP Params.default).headerOk (trHdr AP.toAir tr) = true →
    ∃ pr : IopProver Fp Fp8, pr.hdr = trHdr AP.toAir tr ∧
      ProverWf (Iop.verifierP Fp Fp8 AP Params.default) pr cb ∧
      IopComplete (Iop.verifierP Fp Fp8 AP Params.default) pr cb

theorem npIopCompleteP : NpIopCompleteStmtP := by
  intro AP cb tr h32 hH hokV
  have hS := schedForm
  have hF := msgFits
  have hP := msgPrefix
  have hokV' : (Vd AP.toAir).headerOk (hdr AP.toAir tr) = true := hokV
  have hok : headerOk AP.toAir dp (hdr AP.toAir tr) = true := (verifier_headerOk hokV').1
  have hwf : ProverWf (Vd AP.toAir) (npProver AP.toAir cb tr) cb := by
    refine ⟨hokV', by simp [npProver, hdr, trHdr]; rfl, ?_, h32, fun τ hr =>
      inv_shaped AP.toAir cb tr hS hF hokV' (reach_inv AP.toAir cb tr hS hr),
      fun τ hr hne => inv_header AP.toAir cb tr (reach_inv AP.toAir cb tr hS hr) hne,
      fun τ _ _ l hl => npMsg_header AP.toAir cb tr _ _ l hl⟩
    intro h hm
    simp only [npProver, hdr, trHdr, List.mem_map, List.mem_range] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    have := headerOk_facts (A := AP.toAir) (prm := dp) hok
    simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := hok
    have hmem : (AP.toAir.tables[t], tr.log t) ∈ AP.toAir.tables.zip (trHdr AP.toAir tr) := by
      rw [List.mem_iff_getElem]
      exact ⟨t, by simp [trHdr]; omega, by simp [trHdr]⟩
    have := hall _ hmem
    simp only [dp, Params.default] at this
    omega
  refine ⟨npProver AP.toAir cb tr, rfl, proverWfP AP hwf, ?_⟩
  intro τ hr' hq'
  have hr := reach_v1 AP hr'
  have hq : (Vd AP.toAir).AtQuery τ := (V2.Np.atQuery_iff AP dp τ).mp hq'
  have hi := reach_inv AP.toAir cb tr hS hr
  obtain ⟨he, hlen⟩ := inv_query AP.toAir cb tr hS hP hok hi hq
  have hz := hi.ood (by
    have := hq.2
    rw [slots_of_header AP.toAir tr (inv_header AP.toAir cb tr hi (by
      intro h0; have h1 := hq.1; rw [header_nil (τ := τ) h0] at h1; cases h1))] at this
    rw [this, hS AP.toAir tr]; simp [slotsOf, List.length_flatMap, slotPairs])
  refine ⟨?_, fun x hx => ?_⟩
  · rw [he]; exact globalP AP cb tr hH hok _ hlen hz
  · have hd : (Vd AP.toAir).domSize τ = 2 ^ n0 AP.toAir tr := by
      simp [IopSpec.domSize, inv_header AP.toAir cb tr hi (by
        intro h0; have h1 := hq.1; rw [header_nil (τ := τ) h0] at h1; cases h1), n0]; rfl
    rw [V2.Np.domSize_eq, hd] at hx
    rw [V2.Np.checksPassP_iff, V2.Np.trueOpenings_eq, he]
    exact localNH AP.toAir cb tr hok _ hlen hz x hx

end ZkFormal.Prover.Np
