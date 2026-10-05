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

/-! ## `deepAt` as a sum over the class -/

/-- `Σ_{r ∈ l} f r`. -/
def sumL {α : Type} (l : List α) (f : α → Fp8) : Fp8 := l.foldr (fun a s => f a + s) 0

theorem foldl_pair {α : Type} (g : Fp8 × Fp8 → α → Fp8 × Fp8) (F G : α → Fp8)
    (hg : ∀ acc r, g acc r = (acc.1 + F r, acc.2 + G r)) :
    ∀ (l : List α) (a b : Fp8), l.foldl g (a, b) = (a + sumL l F, b + sumL l G)
  | [], a, b => by simp [sumL]; constructor <;> grind
  | r :: l, a, b => by
    rw [List.foldl_cons, hg, foldl_pair g F G hg l]
    simp only [sumL, List.foldr_cons, Prod.mk.injEq]
    constructor <;> grind

theorem deepAt_eq (c : Ctx Fp8) (op : List (List (List Fp))) (m x : Nat) :
    deepAt (F := Fp) c op m x =
      let p := x >>> (c.n0 - m)
      let ξ : Fp8 := StarkField.embed (K := Fp8) (domPoint (K := Fp8) c.n0 m p : Fp)
      let main := op.getD 0 []; let aux := op.getD 1 []; let quot := op.getD 2 []
      let rows := ((c.lay.zip c.deep).zipIdx).filter (·.1.1.lde == m)
      match rows with
      | [] => 0
      | ((L0, _), _) :: _ =>
        let ω : Fp8 := StarkField.embed (K := Fp8) (StarkField.twoAdicGen (K := Fp8) L0.log : Fp)
        sumL rows (fun r => (r.1.2.eMz.zip (main.getD r.2 [])).foldl
              (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
            dotK r.1.2.eAz (ksOfRow (F := Fp) (aux.getD r.2 [])) +
            dotK r.1.2.eQ (ksOfRow (F := Fp) (quot.getD r.2 [])) - r.1.2.vz) / (ξ - c.z) +
        sumL rows (fun r => (r.1.2.eMg.zip (main.getD r.2 [])).foldl
              (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
            dotK r.1.2.eAg (ksOfRow (F := Fp) (aux.getD r.2 [])) - r.1.2.vg) / (ξ - ω * c.z) := by
  unfold deepAt
  simp only
  split
  · rename_i h; simp only [h]
  · rename_i L0 d0 t0 rs hrs
    simp only [hrs]
    rw [foldl_pair _
      (fun r => (r.1.2.eMz.zip ((op.getD 0 []).getD r.2 [])).foldl
              (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
            dotK r.1.2.eAz (ksOfRow (F := Fp) ((op.getD 1 []).getD r.2 [])) +
            dotK r.1.2.eQ (ksOfRow (F := Fp) ((op.getD 2 []).getD r.2 [])) - r.1.2.vz)
      (fun r => (r.1.2.eMg.zip ((op.getD 0 []).getD r.2 [])).foldl
              (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
            dotK r.1.2.eAg (ksOfRow (F := Fp) ((op.getD 1 []).getD r.2 [])) - r.1.2.vg)
      (fun acc r => by simp only [dotK]; apply Prod.ext <;> simp only <;> grind)]
    simp only
    grind

/-! ## The class sum -/

theorem class_sum (eqs : List Fp8) (m : Nat) (z ω ξ : Fp8) (val : Col → Fp8) (cl : Col → Bool → Fp8)
    (rowM rowA rowQ : Nat → List Fp) (oodF : Nat → TOod Fp8) (layF : Nat → TLayout)
    (hv0 : ∀ t c, (layF t).lde = m → val ⟨t, 0, c⟩ = Fp8.ofBase ((rowM t).getD c 0))
    (hv1 : ∀ t c, (layF t).lde = m → val ⟨t, 1, c⟩ = (ksOfRow (F := Fp) (rowA t)).getD c 0)
    (hv2 : ∀ t c, (layF t).lde = m → val ⟨t, 2, c⟩ = (ksOfRow (F := Fp) (rowQ t)).getD c 0)
    (hc0 : ∀ t c, cl ⟨t, 0, c⟩ false = (oodF t).mainZ.getD c 0)
    (hc0' : ∀ t c, cl ⟨t, 0, c⟩ true = (oodF t).mainG.getD c 0)
    (hc1 : ∀ t c, cl ⟨t, 1, c⟩ false = (oodF t).auxZ.getD c 0)
    (hc1' : ∀ t c, cl ⟨t, 1, c⟩ true = (oodF t).auxG.getD c 0)
    (hc2 : ∀ t c, cl ⟨t, 2, c⟩ false = (oodF t).quotZ.getD c 0) :
    ∀ (ps : List (TLayout × TOod Fp8)) (pre : List TLayout) (s : Nat),
      (∀ k (hk : k < ps.length), ps[k].2 = oodF (s + k)) →
      (∀ k (hk : k < ps.length), ps[k].1 = layF (s + k)) →
      let H : Nat → Col × Bool → Fp8 := fun j ds =>
        eqs.getD j 0 * (val ds.1 - cl ds.1 ds.2) * (ξ - (if ds.2 then ω * z else z))⁻¹
      let rows := (((ps.map (·.1)).zip (tdList eqs pre ps)).zipIdx s).filter (·.1.1.lde == m)
      sumL rows (fun r => (r.1.2.eMz.zip (rowM r.2)).foldl
              (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
            dotK r.1.2.eAz (ksOfRow (F := Fp) (rowA r.2)) +
            dotK r.1.2.eQ (ksOfRow (F := Fp) (rowQ r.2)) - r.1.2.vz) * (ξ - z)⁻¹ +
        sumL rows (fun r => (r.1.2.eMg.zip (rowM r.2)).foldl
              (fun s (uv : Fp8 × Fp) => s + uv.1 * StarkField.embed (K := Fp8) uv.2) 0 +
            dotK r.1.2.eAg (ksOfRow (F := Fp) (rowA r.2)) - r.1.2.vg) * (ξ - ω * z)⁻¹ =
      sOff ((((ps.map (·.1)).zipIdx s).filter fun (L, _) => L.lde == m).flatMap
        (fun (L, t) => blkOf L t)) (offSum pre m) H
  | [], pre, s, _, _ => by simp [sumL, sOff]; grind
  | (L, o) :: ps, pre, s, hps, hls => by
    intro H rows
    have ih := class_sum eqs m z ω ξ val cl rowM rowA rowQ oodF layF hv0 hv1 hv2 hc0 hc0' hc1 hc1' hc2 ps
      (pre ++ [L]) (s + 1) (fun k hk => by
        have := hps (k + 1) (by simp; omega); simp at this; rw [this]; congr 1; omega)
      (fun k hk => by
        have := hls (k + 1) (by simp; omega); simp at this; rw [this]; congr 1; omega)
    have hlf : L = layF s := by have := hls 0 (by simp); simpa using this
    have ho : o = oodF s := by have := hps 0 (by simp); simpa using this
    simp only at ih
    simp only [rows, List.map_cons, tdList, List.zip_cons_cons, List.zipIdx_cons, List.filter_cons]
    by_cases hL : L.lde = m
    · have hb : (L.lde == m) = true := by simp [hL]
      simp only [hb, ite_true, List.flatMap_cons, sOff_append]
      have hlen : (blkOf L s).length = cntL L := by simp [blkOf, cntL]; omega
      have hoff : offSum pre m + (blkOf L s).length = offSum (pre ++ [L]) m := by
        rw [offSum_append, ite_eq_left hL, hlen]
      rw [hoff, ← ih]
      have ht := table_sum eqs (offSum pre L.lde) L s o (rowM s) (rowA s) (rowQ s) z ω ξ val cl
        (fun c => hv0 s c (hlf ▸ hL)) (fun c => hv1 s c (hlf ▸ hL)) (fun c => hv2 s c (hlf ▸ hL))
        (fun c => ho ▸ hc0 s c) (fun c => ho ▸ hc0' s c) (fun c => ho ▸ hc1 s c)
        (fun c => ho ▸ hc1' s c) (fun c => ho ▸ hc2 s c)
      simp only at ht
      rw [show offSum pre m = offSum pre L.lde by rw [hL], ht]
      simp only [sumL, List.foldr_cons]
      grind
    · have hb : (L.lde == m) = false := by simp [hL]
      simp only [hb, Bool.false_eq_true, ite_false]
      rw [show offSum pre m = offSum (pre ++ [L]) m by rw [offSum_append, ite_eq_right hL, Nat.add_zero], ← ih]

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

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

theorem foldl_fst_len {X Y Z : Type} (f : List X × Y → Z → List X × Y)
    (hf : ∀ acc z, (f acc z).1.length = acc.1.length + 1) :
    ∀ (l : List Z) (acc : List X × Y), (l.foldl f acc).1.length = acc.1.length + l.length
  | [], acc => by simp
  | z :: l, acc => by rw [List.foldl_cons, foldl_fst_len f hf l, hf, List.length_cons]; omega

theorem splitOod_len (lay : List TLayout) (ood : List Fp8) : (splitOod lay ood).1.length = lay.length := by
  unfold splitOod
  rw [foldl_fst_len _ (fun acc z => by simp)]
  simp

theorem sOff_congr {β : Type} (xs : List β) (off : Nat) (H H' : Nat → β → Fp8)
    (h : ∀ j (hj : j < xs.length), H (off + j) xs[j] = H' (off + j) xs[j]) :
    sOff xs off H = sOff xs off H' := by
  unfold sOff
  apply sumR_congr; intro j hj
  rw [List.getElem?_eq_getElem hj]; exact h j hj

theorem layout_lde (A : Air) (prm : Params) (hdr : List Nat) (L : TLayout) (hL : L ∈ layout A prm hdr) :
    L.lde = L.log + prm.logBlowup := by
  simp only [layout, List.mem_map] at hL
  obtain ⟨⟨T, l⟩, _, rfl⟩ := hL
  rfl

theorem ds_mem_deepCols (lay : List TLayout) (m : Nat) (d : Col) (s : Bool)
    (h : (d, s) ∈ deepCols lay m) : d.t < lay.length ∧ (lay.getD d.t default).lde = m := by
  simp only [deepCols, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨⟨L, t⟩, ⟨hz, hm⟩, hb⟩ := h
  have hz' := List.mem_zipIdx hz
  simp only [Nat.zero_add, Nat.sub_zero] at hz'
  have hdt : d.t = t := by
    simp only [List.mem_append, List.mem_map, List.mem_range] at hb
    rcases hb with ((((⟨c, _, he⟩ | ⟨c, _, he⟩) | ⟨c, _, he⟩) | ⟨c, _, he⟩) | ⟨c, _, he⟩) <;>
      (cases he; rfl)
  refine ⟨hdt ▸ hz'.2.1, ?_⟩
  rw [hdt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz'.2.1]
  simp only [Option.getD_some]
  rw [← hz'.2.2]; simpa using hm

end ZkFormal.Udr.Np

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- The batched DEEP word as an offset sum over the DEEP columns. -/
theorem deepAtPos_sOff {A : Air} {prm : Params} {τ : PTn} (Q : QData A prm τ) (m p : Nat) :
    deepAtPos A prm τ m p =
      sOff (deepCols (layOf A prm τ) m) 0 (fun j ds =>
        (eqTable ((Q.rest).take (batchRounds (layOf A prm τ)))).getD j 0 *
          ((colVal τ ds.1 p - claimed A prm τ ds.1 ds.2) *
            (pt (n0Of A prm τ) m p - (if ds.2 then omg (tl A prm τ ds.1.t).log * zOf τ else zOf τ))⁻¹)) := by
  have hbc : batchChals A prm τ = (Q.rest).take (batchRounds (layOf A prm τ)) := by
    simp only [batchChals, nBatch, Q.hc, List.drop_succ_cons, List.drop_zero]
  have hlen : ((Q.rest).take (batchRounds (layOf A prm τ))).length = batchRounds (layOf A prm τ) := by
    have := Q.hrest; rw [Q.lay]; simp; omega
  simp only [deepAtPos, batchedWord, hbc]
  rw [batchAll_col, hlen, Nat.zero_mul]
  generalize hrs : (Q.rest).take (batchRounds (layOf A prm τ)) = rs at hlen ⊢
  -- the number of DEEP columns is at most `2^L`
  have hN : (deepCols (layOf A prm τ) m).length ≤ 2 ^ batchRounds (layOf A prm τ) := by
    cases hdc : deepCols (layOf A prm τ) m with
    | nil => simp
    | cons b bs =>
      have hb : b ∈ deepCols (layOf A prm τ) m := by rw [hdc]; exact List.mem_cons_self ..
      obtain ⟨ht, hlde⟩ := ds_mem_deepCols _ m b.1 b.2 hb
      have hmem : (layOf A prm τ).getD b.1.t default ∈ layOf A prm τ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
      have := deepCols_length_le (layOf A prm τ) _ hmem
      rw [hlde, hdc] at this; exact this
  rw [sumR_trunc hN (fun j h1 _ => by
    simp only [deepWord, Nat.zero_add, List.getElem?_eq_none h1]; grind)]
  unfold sOff
  apply sumR_congr
  intro j hj
  have he : (eqTable rs).getD j 0 = eqF rs j := eqTable_getD rs j (by rw [hlen]; omega)
  simp only [deepWord, Nat.zero_add, he]
  rw [List.getElem?_eq_getElem hj]

theorem row_eq (o : Oracle Fp) (lay' : List TLayout) (w : TLayout → Nat)
    (hfit : OFit o (lay'.map fun L => (L.lde, w L))) (x N m t : Nat)
    (hlde : (lay'.getD t default).lde = m) :
    (o.map fun M => M.row (x >>> (N - M.log))).getD t [] = (matOf o t).row (x >>> (N - m)) := by
  obtain ⟨hlen, hk⟩ := hfit
  rw [List.length_map] at hlen
  by_cases ht : t < o.length
  · obtain ⟨sh, hsh, hlog, -⟩ := hk t ht
    rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)] at hsh
    have hl : o[t].log = m := by
      rw [hlog, ← Option.some.inj hsh, ← hlde, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    simp only [matOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht,
      Option.map_some, Option.getD_some, hl]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by omega)]
    simp [matOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt ht)]

theorem deepSem : DeepSemStmt := by
  intro A prm _ τ hs hq hg x _ m _
  obtain ⟨Q⟩ := qdata A prm τ hg
  obtain ⟨o0, o1, o2, fris, hor, h0, h1, h2, -⟩ := query_oracles A prm Q.hdr τ hs hq Q.hh
  let lay := layOf A prm τ
  let oods := (splitOod lay Q.ood).1
  let ps := lay.zip oods
  have hps1 : ps.map (·.1) = lay := by
    simp only [ps, oods]; rw [List.map_fst_zip]; rw [splitOod_len]; exact Nat.le_refl _
  let eqs := eqTable ((Q.rest).take (batchRounds lay))
  let p := x >>> (n0Of A prm τ - m)
  let op := (Vnp A prm).trueOpenings τ x
  let ω := omg (m - prm.logBlowup)
  have hn0 : (Vnp A prm).queryLog Q.hdr = n0Of A prm τ := by
    rw [Q.n0]; rfl
  have hopk : ∀ k o, τ.oracles.getD k [] = o →
      op.getD k [] = o.map (fun M => M.row (x >>> (n0Of A prm τ - M.log))) := by
    intro k o hk
    simp only [op, IopSpec.trueOpenings, Q.hh, hn0]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD] at hk
    cases h : τ.oracles[k]? with
    | none => rw [h] at hk; simp at hk; subst hk; simp
    | some o' => rw [h] at hk; simp at hk; subst hk; simp
  have hlayQ : lay = layout A prm Q.hdr := Q.lay
  have hv : ∀ (k : Nat) (w : TLayout → Nat), k < 3 → OFit (τ.oracles.getD k []) ((layout A prm Q.hdr).map fun L => (L.lde, w L)) →
      ∀ t, (lay.getD t default).lde = m →
        (op.getD k []).getD t [] = (matOf (oracleOf τ k) t).row p := by
    intro k w _ hfit t hl
    rw [hopk k _ rfl]
    exact row_eq _ (layout A prm Q.hdr) w hfit x (n0Of A prm τ) m t (by rw [← hlayQ]; exact hl)
  have hf0 : OFit (τ.oracles.getD 0 []) ((layout A prm Q.hdr).map fun L => (L.lde, L.width)) := by
    rw [hor]; exact h0
  have hf1 : OFit (τ.oracles.getD 1 []) ((layout A prm Q.hdr).map fun L => (L.lde, 8 * L.aux)) := by
    rw [hor]; exact h1
  have hf2 : OFit (τ.oracles.getD 2 []) ((layout A prm Q.hdr).map fun L => (L.lde, 8 * L.quot)) := by
    rw [hor]; exact h2
  let oodF : Nat → TOod Fp8 := fun t =>
    ((splitOod (layOf A prm τ) (τ.elems.getD 1 [])).1).getD t ⟨[], [], [], [], []⟩
  have hood : τ.elems.getD 1 [] = Q.ood := by rw [Q.he]; rfl
  have hcs := class_sum eqs m (zOf τ) ω (pt (n0Of A prm τ) m p) (fun d => colVal τ d p)
    (claimed A prm τ) (fun t => (op.getD 0 []).getD t []) (fun t => (op.getD 1 []).getD t [])
    (fun t => (op.getD 2 []).getD t []) oodF (fun t => lay.getD t default)
    (fun t c hl => by rw [hv 0 _ (by omega) hf0 t hl]; simp [colVal])
    (fun t c hl => by rw [hv 1 _ (by omega) hf1 t hl]; simp [colVal])
    (fun t c hl => by rw [hv 2 _ (by omega) hf2 t hl]; simp [colVal])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    ps [] 0
    (fun k hk => by
      simp only [ps, oods, oodF, hood, List.getElem_zip, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl)
    (fun k hk => by
      simp only [ps, List.getElem_zip, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl)
  simp only [hps1] at hcs
  have hdc : deepCols lay m = ((lay.zipIdx 0).filter fun (L, _) => L.lde == m).flatMap
      (fun (L, t) => blkOf L t) := rfl
  -- the right-hand side
  rw [deepAtPos_sOff Q m p]
  have hlog : ∀ t, (lay.getD t default).lde = m → (lay.getD t default).log = m - prm.logBlowup := by
    intro t ht
    by_cases hlt : t < lay.length
    · have hmem : lay.getD t default ∈ layout A prm Q.hdr := by
        rw [← hlayQ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem hlt
      have := layout_lde A prm Q.hdr _ hmem; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at ht ⊢
      have e1 : (default : TLayout).lde = 0 := rfl
      have e2 : (default : TLayout).log = 0 := rfl
      simp only [Option.getD_none] at ht ⊢
      omega
  rw [show sOff (deepCols (layOf A prm τ) m) 0 _ = sOff (deepCols lay m) 0 _ from rfl]
  rw [sOff_congr (deepCols lay m) 0 _ (fun j ds => eqs.getD j 0 * ((fun d => colVal τ d p) ds.1 -
      claimed A prm τ ds.1 ds.2) * (pt (n0Of A prm τ) m p - (if ds.2 then ω * zOf τ else zOf τ))⁻¹)
      (fun j hj => by
        have hm := ds_mem_deepCols lay m _ _ (List.getElem_mem hj)
        have hl := hlog _ hm.2
        have hl' : (tl A prm τ (deepCols lay m)[j].1.t).log = m - prm.logBlowup := hl
        simp only [Nat.zero_add, hl']
        grind)]
  rw [hdc]
  refine Eq.trans ?_ hcs
  -- the left-hand side
  rw [deepAt_eq]
  simp only [prepF_lay Q, prepF_n0 Q, prepF_z Q, prep_deep Q]
  rw [fold_stepD _ _ ([], []) [] (fun _ => rfl), List.nil_append]
  simp only [lay, eqs, ps, oods, op, p]
  generalize hR : List.filter (fun x => x.fst.fst.lde == m) ((layOf A prm τ).zip
    (tdList (eqTable (List.take (batchRounds (layOf A prm τ)) Q.rest)) []
      ((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).fst))).zipIdx = R
  cases R with
  | nil => simp only [sumL, List.foldr_nil]; grind
  | cons r0 rs =>
    obtain ⟨⟨L0, d0⟩, t0⟩ := r0
    have hmem : ((L0, d0), t0) ∈ List.filter (fun x => x.fst.fst.lde == m) ((layOf A prm τ).zip
        (tdList (eqTable (List.take (batchRounds (layOf A prm τ)) Q.rest)) []
          ((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).fst))).zipIdx := by
      rw [hR]; exact List.mem_cons_self ..
    rw [List.mem_filter] at hmem
    have hz := List.mem_zipIdx hmem.1
    have hLd : (L0, d0) ∈ (layOf A prm τ).zip
        (tdList (eqTable (List.take (batchRounds (layOf A prm τ)) Q.rest)) []
          ((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).fst)) := by
      rw [hz.2.2]; exact List.getElem_mem _
    have hL0 : L0 ∈ layout A prm Q.hdr := by rw [← Q.lay]; exact (List.of_mem_zip hLd).1
    have hlde : L0.lde = m := by simpa using hmem.2
    have hl0 : L0.log = m - prm.logBlowup := by have := layout_lde A prm Q.hdr L0 hL0; omega
    simp only [hl0]
    simp only [Field.div_eq_mul_inv]
    rfl

end ZkFormal.Udr.Np
