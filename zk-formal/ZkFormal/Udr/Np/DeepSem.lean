import ZkFormal.Udr.SumR
import ZkFormal.Udr.Np.Bridge5

/-!
# ZkFormal.Udr.Np.DeepSem — the verifier's DEEP value is the batched DEEP word

`deepSem : DeepSemStmt`: at the query phase, `deepAt` (L4) of class `m`
computed from the true openings at position `x` equals `deepAtPos m p`
(L3's batched DEEP word, `p = x >>> (n0 - m)`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Zipped folds as sums -/

theorem sumR_shift (n : Nat) (f : Nat → Fp8) : sumR (n + 1) f = f 0 + sumR n (fun i => f (i + 1)) := by
  rw [Nat.add_comm n 1, sumR_append]
  simp only [sumR_succ, sumR_zero]
  have : ∀ i, f (1 + i) = f (i + 1) := fun i => by rw [Nat.add_comm]
  rw [sumR_congr (fun i _ => this i)]; grind

theorem foldl_zip_sum {β : Type} (h : Fp8 → β → Fp8) (db : β) (hz : ∀ u, h u db = 0) :
    ∀ (a : List Fp8) (b : List β) (s : Fp8),
      (a.zip b).foldl (fun s (uv : Fp8 × β) => s + h uv.1 uv.2) s =
        s + sumR a.length (fun c => h (a.getD c 0) (b.getD c db))
  | [], _, s => by simp; grind
  | u :: a, [], s => by
    simp only [List.zip_nil_right, List.foldl_nil, List.length_cons, List.getD_nil]
    rw [sumR_eq_zero (fun c _ => hz _)]; grind
  | u :: a, v :: b, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.length_cons]
    rw [foldl_zip_sum h db hz a b, sumR_shift]
    simp only [List.getD_cons_zero, List.getD_cons_succ]; grind

/-- Extending a sum with vanishing terms. -/
theorem sumR_getD_ext (a : List Fp8) (g : Nat → Fp8) (n : Nat) (hn : a.length ≤ n) :
    sumR a.length (fun c => a.getD c 0 * g c) = sumR n (fun c => a.getD c 0 * g c) := by
  refine (sumR_trunc hn fun c h1 _ => ?_).symm
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp; grind

/-! ## `prep`'s DEEP coefficients -/

/-- The verifier's `dot`. -/
def dotK (a b : List Fp8) : Fp8 := (a.zip b).foldl (fun s (u, v) => s + u * v) 0

/-- One step of `prep`'s DEEP fold (copied from `Stark.prep`). -/
def stepD (eqs : List Fp8) (acc : List (TDeep Fp8) × List (Nat × Nat)) (Lo : TLayout × TOod Fp8) :
    List (TDeep Fp8) × List (Nat × Nat) :=
  let Lt := Lo.1; let o := Lo.2
  let off := (acc.2.lookup Lt.lde).getD 0
  let e := eqs.drop off
  let eMz := e.take Lt.width; let e := e.drop Lt.width
  let eMg := e.take Lt.width; let e := e.drop Lt.width
  let eAz := e.take Lt.aux; let e := e.drop Lt.aux
  let eAg := e.take Lt.aux; let e := e.drop Lt.aux
  let eQ := e.take Lt.quot
  let td : TDeep Fp8 := ⟨eMz, eMg, eAz, eAg, eQ,
    dotK eMz o.mainZ + dotK eAz o.auxZ + dotK eQ o.quotZ, dotK eMg o.mainG + dotK eAg o.auxG⟩
  let cnt := 2 * Lt.width + 2 * Lt.aux + Lt.quot
  (acc.1 ++ [td], (Lt.lde, off + cnt) :: acc.2.filter (·.1 != Lt.lde))

/-! ## The fold invariant -/

def cntL (L : TLayout) : Nat := 2 * L.width + 2 * L.aux + L.quot

/-- Columns of class `m` before a prefix of tables. -/
def offSum (pre : List TLayout) (m : Nat) : Nat := ((pre.filter fun L => L.lde == m).map cntL).sum

/-- The coefficient record of a table at offset `off`. -/
def mkTD (eqs : List Fp8) (off : Nat) (Lt : TLayout) (o : TOod Fp8) : TDeep Fp8 :=
  let e := eqs.drop off
  let eMz := e.take Lt.width; let e := e.drop Lt.width
  let eMg := e.take Lt.width; let e := e.drop Lt.width
  let eAz := e.take Lt.aux; let e := e.drop Lt.aux
  let eAg := e.take Lt.aux; let e := e.drop Lt.aux
  let eQ := e.take Lt.quot
  ⟨eMz, eMg, eAz, eAg, eQ,
    dotK eMz o.mainZ + dotK eAz o.auxZ + dotK eQ o.quotZ, dotK eMg o.mainG + dotK eAg o.auxG⟩

def tdList (eqs : List Fp8) : List TLayout → List (TLayout × TOod Fp8) → List (TDeep Fp8)
  | _, [] => []
  | pre, (L, o) :: ps => mkTD eqs (offSum pre L.lde) L o :: tdList eqs (pre ++ [L]) ps

theorem lookup_filter_ne (k m : Nat) (h : m ≠ k) : ∀ l : List (Nat × Nat),
    (l.filter (·.1 != k)).lookup m = l.lookup m
  | [] => rfl
  | (a, v) :: l => by
    by_cases ha : a = k
    · have hb : (a != k) = false := by simp [ha]
      simp only [List.filter_cons, hb, Bool.false_eq_true, ite_false, List.lookup_cons]
      rw [lookup_filter_ne k m h l]
      have : (m == a) = false := by simp [ha, h]
      simp [this]
    · have hb : (a != k) = true := by simp [ha]
      simp only [List.filter_cons, hb, ite_true, List.lookup_cons]
      rw [lookup_filter_ne k m h l]

theorem offSum_append (pre : List TLayout) (L : TLayout) (m : Nat) :
    offSum (pre ++ [L]) m = offSum pre m + (if L.lde = m then cntL L else 0) := by
  simp only [offSum, List.filter_append, List.map_append, List.sum_append, List.filter_cons,
    List.filter_nil]
  by_cases h : L.lde = m <;> simp [h]

theorem fold_stepD (eqs : List Fp8) : ∀ (ps : List (TLayout × TOod Fp8))
    (acc : List (TDeep Fp8) × List (Nat × Nat)) (pre : List TLayout),
    (∀ m, (acc.2.lookup m).getD 0 = offSum pre m) →
    (ps.foldl (stepD eqs) acc).1 = acc.1 ++ tdList eqs pre ps
  | [], acc, pre, _ => by simp [tdList]
  | (L, o) :: ps, acc, pre, h => by
    rw [List.foldl_cons, fold_stepD eqs ps _ (pre ++ [L])]
    · simp only [stepD, tdList, h L.lde, List.append_assoc, List.singleton_append]
      rfl
    · intro m
      simp only [stepD, offSum_append, h L.lde]
      by_cases hm : m = L.lde
      · subst hm; simp [cntL]
      · rw [List.lookup_cons]
        have : (m == L.lde) = false := by simp [hm]
        rw [this]
        rw [lookup_filter_ne _ _ hm, h m]
        simp [Ne.symm hm]

theorem tdList_get (eqs : List Fp8) : ∀ (ps : List (TLayout × TOod Fp8)) (pre : List TLayout) (t : Nat)
    (ht : t < ps.length),
    (tdList eqs pre ps)[t]? = some (mkTD eqs (offSum (pre ++ (ps.take t).map (·.1)) ps[t].1.lde)
      ps[t].1 ps[t].2)
  | [], _, _, h => absurd h (by simp)
  | (L, o) :: ps, pre, 0, _ => by simp [tdList]
  | (L, o) :: ps, pre, t + 1, h => by
    simp only [tdList, List.getElem?_cons_succ, List.take_succ_cons, List.map_cons,
      List.getElem_cons_succ]
    rw [tdList_get eqs ps (pre ++ [L]) t (by simp at h; omega)]
    simp [List.append_assoc]

theorem tdList_length (eqs : List Fp8) : ∀ (ps : List (TLayout × TOod Fp8)) (pre : List TLayout),
    (tdList eqs pre ps).length = ps.length
  | [], _ => rfl
  | (L, o) :: ps, pre => by simp [tdList, tdList_length eqs ps]

/-! ## Sums over lists with offsets -/

/-- `Σ_j H (off + j) xs[j]`. -/
def sOff {β : Type} (xs : List β) (off : Nat) (H : Nat → β → Fp8) : Fp8 :=
  sumR xs.length (fun j => match xs[j]? with | some b => H (off + j) b | none => 0)

theorem sOff_nil {β : Type} (off : Nat) (H : Nat → β → Fp8) : sOff [] off H = 0 := rfl

theorem sOff_append {β : Type} (xs ys : List β) (off : Nat) (H : Nat → β → Fp8) :
    sOff (xs ++ ys) off H = sOff xs off H + sOff ys (off + xs.length) H := by
  unfold sOff
  rw [List.length_append, sumR_append]
  congr 1
  · apply sumR_congr; intro j hj; rw [List.getElem?_append_left hj]
  · apply sumR_congr; intro j _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Nat.add_assoc]

theorem sOff_map {β : Type} (n : Nat) (f : Nat → β) (off : Nat) (H : Nat → β → Fp8) :
    sOff ((List.range n).map f) off H = sumR n (fun c => H (off + c) (f c)) := by
  unfold sOff
  rw [List.length_map, List.length_range]
  apply sumR_congr; intro j hj
  simp [List.getElem?_map, List.getElem?_range hj]

/-- `(l.drop a).take b` read at `c < b`. -/
theorem getD_take_drop (l : List Fp8) (a b c : Nat) (hc : c < b) :
    ((l.drop a).take b).getD c 0 = l.getD (a + c) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hc, ite_true, List.getElem?_drop]

theorem length_take_drop_le (l : List Fp8) (a b : Nat) : ((l.drop a).take b).length ≤ b := by
  simp; omega

/-- A verifier dot product as a sum. -/
theorem dotK_eq (a b : List Fp8) (n : Nat) (hn : a.length ≤ n) :
    dotK a b = sumR n (fun c => a.getD c 0 * b.getD c 0) := by
  unfold dotK
  have := foldl_zip_sum (fun u v => u * v) 0 (fun u => by grind) a b 0
  rw [this, sumR_getD_ext a (fun c => b.getD c 0) n hn]; grind

theorem dotF_eq (a : List Fp8) (b : List Fp) (n : Nat) (hn : a.length ≤ n) :
    (a.zip b).foldl (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 =
      sumR n (fun c => a.getD c 0 * Fp8.ofBase (b.getD c 0)) := by
  have := foldl_zip_sum (fun u v => u * StarkField.embed (K := Fp8) v) 0
    (fun u => by show u * Fp8.ofBase 0 = 0; rw [show Fp8.ofBase 0 = 0 from rfl]; grind) a b 0
  rw [this]
  have h2 := sumR_getD_ext a (fun c => Fp8.ofBase (b.getD c 0)) n hn
  show 0 + sumR a.length (fun c => a.getD c 0 * Fp8.ofBase (b.getD c 0)) = _
  rw [h2]; grind

/-! ## One table -/

/-- The DEEP columns of one table (as in `deepCols`). -/
def blkOf (L : TLayout) (t : Nat) : List (Col × Bool) :=
  (List.range L.width).map (fun c => (⟨t, 0, c⟩, false)) ++
  (List.range L.width).map (fun c => (⟨t, 0, c⟩, true)) ++
  (List.range L.aux).map (fun c => (⟨t, 1, c⟩, false)) ++
  (List.range L.aux).map (fun c => (⟨t, 1, c⟩, true)) ++
  (List.range L.quot).map (fun c => (⟨t, 2, c⟩, false))

theorem mkTD_fields (eqs : List Fp8) (off : Nat) (L : TLayout) (o : TOod Fp8) :
    (mkTD eqs off L o).eMz = (eqs.drop off).take L.width ∧
    (mkTD eqs off L o).eMg = (eqs.drop (off + L.width)).take L.width ∧
    (mkTD eqs off L o).eAz = (eqs.drop (off + 2 * L.width)).take L.aux ∧
    (mkTD eqs off L o).eAg = (eqs.drop (off + 2 * L.width + L.aux)).take L.aux ∧
    (mkTD eqs off L o).eQ = (eqs.drop (off + 2 * L.width + 2 * L.aux)).take L.quot ∧
    (mkTD eqs off L o).vz = dotK (mkTD eqs off L o).eMz o.mainZ + dotK (mkTD eqs off L o).eAz o.auxZ +
      dotK (mkTD eqs off L o).eQ o.quotZ ∧
    (mkTD eqs off L o).vg = dotK (mkTD eqs off L o).eMg o.mainG + dotK (mkTD eqs off L o).eAg o.auxG := by
  simp only [mkTD, List.drop_drop]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rfl | trivial | (congr 2; omega)

/-- Sum of `e(off + k + c)·(f c − g c)` over `c < n`, as dot products. -/
theorem block_sum (eqs : List Fp8) (a n : Nat) (f g : Nat → Fp8) :
    sumR n (fun c => eqs.getD (a + c) 0 * (f c - g c)) =
      sumR n (fun c => ((eqs.drop a).take n).getD c 0 * f c) -
        sumR n (fun c => ((eqs.drop a).take n).getD c 0 * g c) := by
  rw [← sumR_sub]
  apply sumR_congr; intro c hc
  rw [getD_take_drop _ _ _ _ hc]; grind

theorem block_sum' (eqs : List Fp8) (a a' n : Nat) (h : a = a') (f g : Nat → Fp8) (I : Fp8) :
    sumR n (fun c => eqs.getD (a + c) 0 * (f c - g c) * I) =
      (sumR n (fun c => ((eqs.drop a').take n).getD c 0 * f c) -
        sumR n (fun c => ((eqs.drop a').take n).getD c 0 * g c)) * I := by
  subst h
  rw [← block_sum, ← sumR_mul_right]

theorem table_sum (eqs : List Fp8) (off : Nat) (L : TLayout) (t : Nat) (o : TOod Fp8)
    (rowM rowA rowQ : List Fp) (z ω ξ : Fp8) (val : Col → Fp8) (cl : Col → Bool → Fp8)
    (hv0 : ∀ c, val ⟨t, 0, c⟩ = Fp8.ofBase (rowM.getD c 0))
    (hv1 : ∀ c, val ⟨t, 1, c⟩ = (ksOfRow (F := Fp) rowA).getD c 0)
    (hv2 : ∀ c, val ⟨t, 2, c⟩ = (ksOfRow (F := Fp) rowQ).getD c 0)
    (hc0 : ∀ c, cl ⟨t, 0, c⟩ false = o.mainZ.getD c 0) (hc0' : ∀ c, cl ⟨t, 0, c⟩ true = o.mainG.getD c 0)
    (hc1 : ∀ c, cl ⟨t, 1, c⟩ false = o.auxZ.getD c 0) (hc1' : ∀ c, cl ⟨t, 1, c⟩ true = o.auxG.getD c 0)
    (hc2 : ∀ c, cl ⟨t, 2, c⟩ false = o.quotZ.getD c 0) :
    let td := mkTD eqs off L o
    let H : Nat → Col × Bool → Fp8 := fun j ds =>
      eqs.getD j 0 * (val ds.1 - cl ds.1 ds.2) * (ξ - (if ds.2 then ω * z else z))⁻¹
    sOff (blkOf L t) off H =
      ((td.eMz.zip rowM).foldl (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
          dotK td.eAz (ksOfRow (F := Fp) rowA) + dotK td.eQ (ksOfRow (F := Fp) rowQ) - td.vz) *
        (ξ - z)⁻¹ +
      ((td.eMg.zip rowM).foldl (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
          dotK td.eAg (ksOfRow (F := Fp) rowA) - td.vg) * (ξ - ω * z)⁻¹ := by
  intro td H
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := mkTD_fields eqs off L o
  simp only [blkOf, sOff_append, sOff_map, List.length_append, List.length_map, List.length_range]
  simp only [H, hv0, hv1, hv2, hc0, hc0', hc1, hc1', hc2, Bool.false_eq_true, ite_false, ite_true]
  simp only [td, h6, h7, h1, h2, h3, h4, h5]
  rw [dotF_eq (List.take L.width (List.drop off eqs)) rowM L.width (length_take_drop_le _ _ _),
    dotF_eq (List.take L.width (List.drop (off + L.width) eqs)) rowM L.width (length_take_drop_le _ _ _),
    dotK_eq (List.take L.aux (List.drop (off + 2 * L.width) eqs)) _ L.aux (length_take_drop_le _ _ _),
    dotK_eq (List.take L.aux (List.drop (off + 2 * L.width + L.aux) eqs)) _ L.aux (length_take_drop_le _ _ _),
    dotK_eq (List.take L.quot (List.drop (off + 2 * L.width + 2 * L.aux) eqs)) _ L.quot (length_take_drop_le _ _ _),
    dotK_eq (List.take L.width (List.drop off eqs)) _ L.width (length_take_drop_le _ _ _),
    dotK_eq (List.take L.aux (List.drop (off + 2 * L.width) eqs)) _ L.aux (length_take_drop_le _ _ _),
    dotK_eq (List.take L.quot (List.drop (off + 2 * L.width + 2 * L.aux) eqs)) _ L.quot (length_take_drop_le _ _ _),
    dotK_eq (List.take L.width (List.drop (off + L.width) eqs)) _ L.width (length_take_drop_le _ _ _),
    dotK_eq (List.take L.aux (List.drop (off + 2 * L.width + L.aux) eqs)) _ L.aux (length_take_drop_le _ _ _)]
  rw [block_sum' eqs off off L.width rfl, block_sum' eqs (off + L.width) (off + L.width) L.width rfl,
    block_sum' eqs (off + (L.width + L.width)) (off + 2 * L.width) L.aux (by omega),
    block_sum' eqs (off + (L.width + L.width + L.aux)) (off + 2 * L.width + L.aux) L.aux (by omega),
    block_sum' eqs (off + (L.width + L.width + L.aux + L.aux)) (off + 2 * L.width + 2 * L.aux) L.quot
      (by omega)]
  grind

section
variable {A : Air} {prm : Params} {τ : PTn}

theorem prep_deep (Q : QData A prm τ) :
    (Stark.prep (F := Fp) A prm τ.erase).deep =
      (((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).1).foldl
        (stepD (eqTable ((Q.rest).take (batchRounds (layOf A prm τ))))) ([], [])).1 := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, Q.lay]
  rfl

end

end ZkFormal.Udr.Np
