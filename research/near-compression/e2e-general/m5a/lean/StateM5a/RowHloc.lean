import StateM5a.RowBrK

/-!
# StateM5a.RowHloc — `hloc` for the decoded walk rows, and the assembly with the concrete decoder

`DecodeShape.air_batched_changes` takes, for its decoder `Dc`, the premise
`hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (Sem σ keyOf) r`.  For the concrete decoder `cDc`:

* **`hloc_br`**: every decoded `BR` row is `LocalOK`, from the `BR` constraints (`Holds`) and,
  per active row, the record-level facts `BrRowFacts` (old record under the input ref, published
  new record, 16-bit memory limbs, the `NIB` / `KLEN` lookups in interface form, the depth
  bound) — for the ops `brCovered`; the other ops are the explicit premise `hbrRest`.
* **`hloc_cDc`**: with the `SN` rows' `LocalOK` as a premise (`hsn`).
* **`air_batched_changes_cDc`**: `air_batched_changes` with `Dc := cDc` and `hloc` replaced by
  the above.
-/

namespace StateM5a.RowHloc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK

local notation "P" => 2013265921

/-- The record-level facts of an active `BR` walk row (premises: `VER` / SHA-256 decoding, the
`NIB` / `KLEN` lookups against the key table, range facts, the depth bound). -/
structure BrRowFacts (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  old : OldOK σ (brIn tr pub r) (brOld tr pub r)
  new : ev tr 2 r pub (Br.c "gnew") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r)
  ranges : BrRanges tr pub r
  nib : ev tr 2 r pub (Br.c "act" - Br.gEnd) = 1 →
    (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib)
  klen : ev tr 2 r pub Br.gEnd = 1 → (keyOf (ev tr 2 r pub (Br.c "kid"))).length = ev tr 2 r pub (Br.c "d")
  depth : (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P
  /-- `oDH`: the child's old memory is at most the branch's (`RowBrK`, module note). -/
  mono : ev tr 2 r pub (Br.c "oDH") = 1 →
    le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) ≤ brMem tr pub r

/-- The `BR` ops whose `LocalOK` is proved here. -/
def brCovered : List String := ["oFD", "oFA", "oFV", "oDA", "oDS", "oDZ", "oUD", "oDH", "oDN"]

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
    (ho : o = "oFD" ∨ o = "oFA" ∨ o = "oDA" ∨ o = "oDS" ∨ o = "oUD" ∨ o = "oDH" ∨ o = "oDN") : ev tr 2 r pub Br.gEnd = 0 := by
  brfacts hc hg
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := by
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact f0
  exact ev_of_eval (by evg; grind)

theorem gEnd_one (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) {o : String} (h1 : ev tr 2 r pub (Br.c o) = 1)
    (ho : o = "oFV" ∨ o = "oDZ") : ev tr 2 r pub Br.gEnd = 1 := by
  brfacts hc hg
  have eFV : (Br.c "oFV").eval tr 2 r pub = if o = "oFV" then 1 else 0 := by
    rcases ho with rfl | rfl
    · exact f1
    · exact f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = if o = "oDZ" then 1 else 0 := by
    rcases ho with rfl | rfl
    · exact f0
    · exact f1
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := by rcases ho with rfl | rfl <;> exact f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := by rcases ho with rfl | rfl <;> exact f0
  apply eval_one_ev
  rcases ho with rfl | rfl <;> simp only [if_true, if_false] at eFV eDZ <;> evg <;> grind

/-- **One active `BR` row running a covered op is `LocalOK`.** -/
theorem localOK_br_row {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (hF : BrRowFacts σ keyOf tr pub r)
    {o : String} (ho : o ∈ brCovered) (h1 : ev tr 2 r pub (Br.c o) = 1) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  simp only [brCovered, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact localOK_oFD hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old
  · exact localOK_oFA hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp)))) hF.old
  · exact localOK_oFV hc hg h1 (hF.klen (gEnd_one hc hg h1 (by simp))) hF.old
      (hF.ranges.2.1 0 (by decide)).1 hF.ranges.2.2
  · exact localOK_oDA hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp)))) hF.old
  · exact localOK_oDS hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old
  · exact localOK_oDZ hc hg h1 (hF.klen (gEnd_one hc hg h1 (by simp))) hF.old
  · exact localOK_oUD hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) hF.ranges
  · exact localOK_oDH hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) hF.ranges (hF.mono h1)
  · exact localOK_oDN hc hg h1 (hF.nib (nib_mult hc hg (gEnd_val hc hg h1 (by simp))))
      (hF.depth (by brfacts hc hg; exact f1)) hF.old (hF.new (by brfacts hc hg; omega)) hF.ranges

end

/-- **`hloc` for the decoded `BR` rows.** -/
theorem hloc_br {tr : Trace Fp} {pub : List Fp} (σ : Store) (keyOf : Nat → List Nat) (D : Nat)
    (extra : List Table) (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hF : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRowFacts σ keyOf tr pub r)
    (hbrRest : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ∀ o ∈ walkOps, o ∉ brCovered →
      ev tr 2 r pub (Br.c o) = 1 → LocalOK (Sem σ keyOf) (brRow tr pub r)) :
    ∀ x ∈ rowsOf cDc brW tr 2 pub, LocalOK (Sem σ keyOf) x := by
  intro x hx
  obtain ⟨r, hr, hg, rfl⟩ := mem_brRows hx
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hg' := eval_one_ev hg
  obtain ⟨o, ho, h1⟩ := br_some_op hc hg'
  by_cases hcov : o ∈ brCovered
  · exact localOK_br_row hc hg' (hF r hr hg') hcov h1
  · exact hbrRest r hr hg' o ho hcov h1

/-- **`hloc` for the concrete decoder**, with the `SN` rows' `LocalOK` a premise. -/
theorem hloc_cDc {tr : Trace Fp} {pub : List Fp} (σ : Store) (keyOf : Nat → List Nat) (D : Nat)
    (extra : List Table) (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hF : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRowFacts σ keyOf tr pub r)
    (hbrRest : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ∀ o ∈ walkOps, o ∉ brCovered →
      ev tr 2 r pub (Br.c o) = 1 → LocalOK (Sem σ keyOf) (brRow tr pub r))
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ keyOf) x) :
    ∀ x ∈ walkRows cDc tr pub, LocalOK (Sem σ keyOf) x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hloc_br σ keyOf D extra nb np hH hF hbrRest x hx
  · exact hsn x hx

open StateM5a.DecodeShape NearSpecV3.D2 in
/-- **Batched FINAL from `Holds` with the concrete decoder.**  `DecodeShape.air_batched_changes`
with `Dc := cDc` and its `hloc` discharged for the `BR` rows running the ops `brCovered` (from the
constraints and the record-level `BrRowFacts`); the remaining `BR` ops (`hbrRest`) and the `SN`
rows (`hsn`) stay premises. -/
theorem air_batched_changes_cDc {tr : Trace Fp} {pub : List Fp} (hCR : Walk.Sha256CR) (σ : Store)
    (keyOf : Nat → List Nat) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hbr : ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P)
    (hsnD : ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 →
      ev tr 3 r pub (Sn.c "cont") = 0 ∧ ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hF : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRowFacts σ keyOf tr pub r)
    (hbrRest : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ∀ o ∈ walkOps, o ∉ brCovered →
      ev tr 2 r pub (Br.c o) = 1 → LocalOK (Sem σ keyOf) (brRow tr pub r))
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ keyOf) x)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ walkRoots cDc tr pub, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hFull : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post :=
  air_batched_changes hCR σ keyOf cDc D extra nb np hH hD hx hbr hsnD
    (hloc_cDc σ keyOf D extra nb np hH hF hbrRest hsn) cs prev post N a b hT hroot T hT0 hFull

end StateM5a.RowHloc
