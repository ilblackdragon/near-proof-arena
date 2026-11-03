import StateM5a.RowBrL
import StateM5a.RowBrD1

/-!
# StateM5a.RowHloc — `hloc` for the decoded walk rows, and the assembly with the concrete decoder

`DecodeShape.air_batched_changes` takes, for its decoder `Dc`, the premise
`hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (Sem σ keyOf) r`.  For the concrete decoder `cDc`:

* **`hloc_br`**: every decoded `BR` row is `LocalOK`, from the `BR` constraints (`Holds`) and,
  per active row, the record-level facts `BrRowFacts` (old record under the input ref, published
  new record, 16-bit memory limbs, the `NIB` / `KLEN` lookups in interface form, the depth
  bound) — for the ops `brCovered`; all 14 walk ops are covered (`walkOps_covered`).
* **`hloc_cDc`**: with the `SN` rows' `LocalOK` as a premise (`hsn`).
* **`air_batched_changes_cDc`**: `air_batched_changes` with `Dc := cDc` and `hloc` replaced by
  the above.
-/

namespace StateM5a.RowHloc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK StateM5a.RowBrL StateM5a.RowBrV StateM5a.RowBrV2 StateM5a.RowBrUN
open StateM5a.RowBrD1

local notation "P" => 2013265921

/-- **Range facts of an active `BR` row, each where it is used** (`BrRanges` asks them on every
row): the old node's memory and value-length limbs and the old length `< P` (every active row);
the new node's memory limbs and the child's answer limbs `nm` / `om` (rows with a new node only).
`BrRangesW.full` gives `BrRanges` on a row with a new node (the new value-length limbs from the
constraints: kept, cleared, or written with `RNG` bytes). -/
def BrRangesW (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop :=
  (∀ k, k < 4 → (bE tr pub r (Br.M.getD k 0)).toNat < 65536) ∧
  (∀ k, k < 2 → (bE tr pub r (limb16 (fun t => Br.c "vl" t) k)).toNat < 65536) ∧
  brVlen tr pub r < 2013265921 ∧
  (ev tr 2 r pub (Br.c "gnew") = 1 → ∀ k, k < 4 → (bE tr pub r (Br.NM.getD k 0)).toNat < 65536 ∧
    (bE tr pub r (Br.c "nm" k)).toNat < 65536 ∧ (bE tr pub r (Br.c "om" k)).toNat < 65536)

set_option maxHeartbeats 4000000 in
theorem br_mem_nvl_keep (t : Nat) (ht : t < 4) :
    (Br.c "gnew" - Br.c "oUV" - Br.c "oDV") * (Br.c "nvl" t - Br.c "vl" t) ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_nvl_none (t : Nat) (ht : t < 4) : (1 - Br.c "nhv") * Br.c "nvl" t ∈ Br.constraints := by brmem

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem ev_limb16_byte {v : Nat → Expr} {k : Nat} (ha : ev tr 2 r pub (v (2 * k)) < 256)
    (hb : ev tr 2 r pub (v (2 * k + 1)) < 256) : ev tr 2 r pub (limb16 v k) < 65536 := by
  unfold limb16
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 256 * ev tr 2 r pub (v (2 * k + 1)) < P by omega),
    Nat.mod_eq_of_lt (show ev tr 2 r pub (v (2 * k)) + 256 * ev tr 2 r pub (v (2 * k + 1)) < P by omega)]
  omega

theorem ev_limb16_congr {v w : Nat → Expr} {k : Nat} (ha : ev tr 2 r pub (v (2 * k)) = ev tr 2 r pub (w (2 * k)))
    (hb : ev tr 2 r pub (v (2 * k + 1)) = ev tr 2 r pub (w (2 * k + 1))) :
    ev tr 2 r pub (limb16 v k) = ev tr 2 r pub (limb16 w k) := by
  unfold limb16; rw [ev_hadd, ev_hadd, ev_hmul, ev_hmul, ha, hb]

/-- **`BrRanges` on a row with a new node.** -/
theorem BrRangesW.full (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (hW : BrRangesW tr pub r)
    (hg : ev tr 2 r pub (Br.c "gnew") = 1)
    (hnvl : ev tr 2 r pub (Br.c "oUV") = 1 → ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) < 256) :
    BrRanges tr pub r := by
  refine ⟨fun k hk => ⟨hW.1 k hk, (hW.2.2.2 hg k hk).1, (hW.2.2.2 hg k hk).2.1, (hW.2.2.2 hg k hk).2.2⟩,
    fun k hk => ⟨hW.2.1 k hk, ?_⟩, hW.2.2.1⟩
  have bU := bool_le (FieldRows.hold rfl hc (br_bool' "oUV" (by simp [flagNames])))
  have bD := bool_le (FieldRows.hold rfl hc (br_bool' "oDV" (by simp [flagNames])))
  show ev tr 2 r pub (limb16 (fun t => Br.c "nvl" t) k) < 65536
  rcases (by omega : ev tr 2 r pub (Br.c "oUV") = 1 ∨ ev tr 2 r pub (Br.c "oUV") = 0) with hU | hU
  · exact ev_limb16_byte (hnvl hU _ (by omega)) (hnvl hU _ (by omega))
  rcases (by omega : ev tr 2 r pub (Br.c "oDV") = 1 ∨ ev tr 2 r pub (Br.c "oDV") = 0) with hD | hD
  · have hn : ev tr 2 r pub (Br.c "nhv") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dvn) hD
    have z : ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) = 0 := fun t ht => FieldVer.gate_zero
      (FieldRows.hold rfl hc (br_mem_nvl_none t ht)) (by rw [ev_sub, hn]; rfl)
    have := ev_limb16_byte (v := fun t => Br.c "nvl" t) (k := k) (tr := tr) (pub := pub) (r := r)
      (by rw [z _ (by omega)]; omega) (by rw [z _ (by omega)]; omega)
    exact this
  · have g1 : ev tr 2 r pub (Br.c "gnew" - Br.c "oUV" - Br.c "oDV") = 1 := by
      rw [ev_sub, ev_sub, hg, hU, hD]
    have e : ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) = ev tr 2 r pub (Br.c "vl" t) := fun t ht =>
      FieldVer.eq_of_gate (FieldRows.hold rfl hc (br_mem_nvl_keep t ht)) g1
    rw [ev_limb16_congr (w := fun t => Br.c "vl" t) (e _ (by omega)) (e _ (by omega))]
    exact hW.2.1 k hk

end

/-- The record-level facts of an active `BR` walk row (premises: `VER` / SHA-256 decoding, the
`NIB` / `KLEN` lookups against the key table, range facts, the depth bound). -/
structure BrRowFacts (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  old : OldOK σ (brIn tr pub r) (brOld tr pub r)
  new : ev tr 2 r pub (Br.c "gnew") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r)
  ranges : BrRangesW tr pub r
  nib : ev tr 2 r pub (Br.c "act" - Br.gEnd) = 1 →
    (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib)
  klen : ev tr 2 r pub Br.gEnd = 1 → (keyOf (ev tr 2 r pub (Br.c "kid"))).length = ev tr 2 r pub (Br.c "d")
  depth : (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P
  /-- `oDH` / `oDL`: the child's old memory is at most the branch's (`RowFacts.br_mono`). -/
  mono : ev tr 2 r pub (Br.c "oDH") = 1 ∨ ev tr 2 r pub (Br.c "oDL") = 1 →
    le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) ≤ brMem tr pub r
  /-- `oUV`: the written length's bytes are bytes (`RNG`). -/
  nvl : ev tr 2 r pub (Br.c "oUV") = 1 → ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) < 256
  /-- `oDL` / `oUN`: the `MATQ`/`MATR` answer (`BusSplit.mat_reqresp`, responders `SN.oLM`). -/
  mat : ev tr 2 r pub (Br.c "oDL") = 1 ∨ ev tr 2 r pub (Br.c "oUN") = 1 →
    MatRel σ keyOf (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)))
  /-- The looked-up depth is a key position (`NIB`): `d < 2^21`. -/
  nibd : ev tr 2 r pub (Br.c "act" - Br.gEnd) = 1 → ev tr 2 r pub (Br.c "d") < 2 ^ 21
  /-- Keys are nibble strings of length `≤ 2^21` (the `KEY` table). -/
  key : ∀ K, (∀ y ∈ keyOf K, y < 16) ∧ (keyOf K).length ≤ 2 ^ 21
  /-- `oD1`: the sibling's key continues with nibble `sib` (`NIB(kid2, d, sib)`). -/
  nib2 : ev tr 2 r pub (Br.c "oD1") = 1 →
    (keyOf (ev tr 2 r pub (Br.c "kid2")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.sib)
  /-- `oD1`: the `SIBQ`/`SIBA` answer (`BusSplit.sib_reqresp`, responders `SN.oLS`). -/
  sib : ev tr 2 r pub (Br.c "oD1") = 1 →
    SibRel σ keyOf (ev tr 2 r pub (Br.c "d") + 1)
      (refOf (E tr 2 r pub Br.isnSib) ((pack2 Br.chSib).map (E tr 2 r pub)))
      (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))

/-- The `BR` ops whose `LocalOK` is proved here. -/
def brCovered : List String :=
  ["oFD", "oFA", "oFV", "oDA", "oDS", "oDZ", "oUD", "oDH", "oDN", "oDL", "oUV", "oDV", "oUN", "oD1"]

theorem walkOps_covered : ∀ o ∈ walkOps, o ∈ brCovered := by
  intro o ho
  simp only [walkOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [brCovered]

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

/-- Field value of `act − gEnd` and `gEnd` from the op. -/
theorem nib_mult (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (hE : ev tr 2 r pub Br.gEnd = 0) :
    ev tr 2 r pub (Br.c "act" - Br.gEnd) = 1 := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eE := fp_of_ev0 hE
  exact eval_one_ev (by simp only [eval_sub]; rw [eAct, eE]; grind)

theorem gEnd_val (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) {o : String} (h1 : ev tr 2 r pub (Br.c o) = 1)
    (ho : o = "oFD" ∨ o = "oFA" ∨ o = "oDA" ∨ o = "oDS" ∨ o = "oUD" ∨ o = "oDH" ∨ o = "oDN" ∨ o = "oDL" ∨
      o = "oUN" ∨ o = "oD1") : ev tr 2 r pub Br.gEnd = 0 := by
  brfacts hc hg
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  exact ev_of_eval (by evg; grind)

theorem gEnd_one (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) {o : String} (h1 : ev tr 2 r pub (Br.c o) = 1)
    (ho : o = "oFV" ∨ o = "oDZ" ∨ o = "oUV" ∨ o = "oDV") : ev tr 2 r pub Br.gEnd = 1 := by
  brfacts hc hg
  apply eval_one_ev
  rcases ho with rfl | rfl | rfl | rfl
  · have a : (Br.c "oFV").eval tr 2 r pub = 1 := f1
    have b : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
    have c : (Br.c "oUV").eval tr 2 r pub = 0 := f0
    have d : (Br.c "oDV").eval tr 2 r pub = 0 := f0
    evg; grind
  · have a : (Br.c "oFV").eval tr 2 r pub = 0 := f0
    have b : (Br.c "oDZ").eval tr 2 r pub = 1 := f1
    have c : (Br.c "oUV").eval tr 2 r pub = 0 := f0
    have d : (Br.c "oDV").eval tr 2 r pub = 0 := f0
    evg; grind
  · have a : (Br.c "oFV").eval tr 2 r pub = 0 := f0
    have b : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
    have c : (Br.c "oUV").eval tr 2 r pub = 1 := f1
    have d : (Br.c "oDV").eval tr 2 r pub = 0 := f0
    evg; grind
  · have a : (Br.c "oFV").eval tr 2 r pub = 0 := f0
    have b : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
    have c : (Br.c "oUV").eval tr 2 r pub = 0 := f0
    have d : (Br.c "oDV").eval tr 2 r pub = 1 := f1
    evg; grind

/-- **One active `BR` row running a covered op is `LocalOK`.** -/
theorem localOK_br_row {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (hF : BrRowFacts σ keyOf tr pub r)
    {o : String} (ho : o ∈ brCovered) (h1 : ev tr 2 r pub (Br.c o) = 1) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  simp only [brCovered, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact localOK_oFD hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old
  · exact localOK_oFA hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp)))) hF.old
  · exact localOK_oFV hc hg h1 (hF.klen (gEnd_one hc hg h1 (by simp))) hF.old
      (hF.ranges.2.1 0 (by decide)) hF.ranges.2.2.1
  · exact localOK_oDA hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp)))) hF.old
  · exact localOK_oDS hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old
  · exact localOK_oDZ hc hg h1 (hF.klen (gEnd_one hc hg h1 (by simp))) hF.old
  · exact localOK_oUD hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl)
  · exact localOK_oDH hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl) (hF.mono (Or.inl h1))
  · exact localOK_oDN hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl)
  · exact localOK_oDL hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl)
      (hF.mono (Or.inr h1)) (hF.mat (Or.inl h1))
  · exact localOK_oUV hc hg h1 (hF.klen (gEnd_one hc hg h1 (by simp))) hF.old
      (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl) (hF.nvl h1)
  · exact localOK_oDV hc hg h1 (hF.klen (gEnd_one hc hg h1 (by simp))) hF.old
      (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl)
  · have hm := nib_mult hc hg (gEnd_val hc hg h1 (by simp))
    exact localOK_oUN hc hg h1 (hF.nib hm) (by have := hF.nibd hm; omega) hF.old
      (hF.new (by brfacts hc hg; omega)) (hF.ranges.full hc (by brfacts hc hg; omega) hF.nvl) (hF.mat (Or.inr h1)) (hF.key _)
  · have hm := nib_mult hc hg (gEnd_val hc hg h1 (by simp))
    exact localOK_oD1 hc hg h1 (hF.nib hm) (hF.nib2 h1) (by have := hF.nibd hm; omega) hF.old
      (hF.sib h1) (hF.key _)

end

/-- **`hloc` for the decoded `BR` rows.** -/
theorem hloc_br {tr : Trace Fp} {pub : List Fp} (σ : Store) (keyOf : Nat → List Nat) (D : Nat)
    (extra : List Table) (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hF : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRowFacts σ keyOf tr pub r) :
    ∀ x ∈ rowsOf cDc brW tr 2 pub, LocalOK (Sem σ keyOf) x := by
  intro x hx
  obtain ⟨r, hr, hg, rfl⟩ := mem_brRows hx
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hg' := eval_one_ev hg
  obtain ⟨o, ho, h1⟩ := br_some_op hc hg'
  exact localOK_br_row hc hg' (hF r hr hg') (walkOps_covered o ho) h1

/-- **`hloc` for the concrete decoder**, with the `SN` rows' `LocalOK` a premise. -/
theorem hloc_cDc {tr : Trace Fp} {pub : List Fp} (σ : Store) (keyOf : Nat → List Nat) (D : Nat)
    (extra : List Table) (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hF : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRowFacts σ keyOf tr pub r)
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ keyOf) x) :
    ∀ x ∈ walkRows cDc tr pub, LocalOK (Sem σ keyOf) x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hloc_br σ keyOf D extra nb np hH hF x hx
  · exact hsn x hx

open StateM5a.DecodeShape NearSpecV3.D2 in
/-- **Batched FINAL from `Holds` with the concrete decoder.**  `DecodeShape.air_batched_changes`
with `Dc := cDc` and its `hloc` discharged for the `BR` rows running the ops `brCovered` (from the
constraints and the record-level `BrRowFacts`); the `SN`
rows (`hsn`) stay a premise. -/
theorem air_batched_changes_cDc {tr : Trace Fp} {pub : List Fp} (hCR : Walk.Sha256CR) (σ : Store)
    (keyOf : Nat → List Nat) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hbr : ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P)
    (hsnD : ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 →
      ev tr 3 r pub (Sn.c "cont") = 0 ∧ ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hF : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRowFacts σ keyOf tr pub r)
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ keyOf) x)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ walkRoots cDc tr pub, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hFull : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post :=
  air_batched_changes hCR σ keyOf cDc D extra nb np hH hD hx hbr hsnD
    (hloc_cDc σ keyOf D extra nb np hH hF hsn) cs prev post N a b hT hroot T hT0 hFull

end StateM5a.RowHloc
