import ZkFormal.V2.G.Deg

/-!
# ZkFormal.V2.G.V1 — v1 L3 lemmas stated at `Params.default`, restated at `pg g`

Verbatim copies of v1 lemmas whose statements fix `prm = Params.default` (`Deep8`: `LayOk`,
`deep_ok`; `Msg8`: `layOk_of`, `tl_mem`, `tl_dec`, `colAt_zero`, `ali_of_global`;
`QueryFacts`: `lay_facts`, `queryLog_le`; `Late`: `eRad_two`, `bound_budget`; `Query`:
`eRad_step`; `Bridge6`; `BusRounds.busTagsOk_of`), with `Params.default` replaced by
`pg g`.  None of them depends on `auxGroup`: the proofs only use the other fields
(`logBlowup = 4`, `maxLogLde = 26`, …), which `pg g` shares with `Params.default`.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

variable {g : Nat}

local notation "prm0" => pg g
local notation "P0" => pg g

/-! ## From `Udr.Np.BusRounds` -/

section
variable {A : Air} {prm : Params}

theorem busTagsOk_of {l : List Nat} (hok : NpOkG A prm) (hh : headerOk A prm l = true) : BusTagsOk A := by
  intro t ht i hi
  obtain ⟨_, _, hwf, _⟩ := headerOk_facts hh
  rw [tableOf_lt ht] at hi
  have := ((table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).1 i hi).1
  have := hok.2.2
  have : (2 : Nat) ^ 30 + 1 < Algebra.P := by decide
  omega

end

/-! ## From `Udr.Np.Deep8` -/


/-- Facts of the layout of a header-carrying transcript (`prm = default`). -/
structure LayOk (g : Nat) (A : Air) (τ : PTn) : Prop where
  lde : ∀ L ∈ layOf A (pg g) τ, L.lde = L.log + 4 ∧ L.lde ≤ 26

theorem eRad_facts (log : Nat) :
    2 ^ log + 1 + 2 * eRad (pg g) (log + 4) ≤ 2 ^ (log + 4) ∧ 2 ^ log + 1 ≤ 2 ^ (log + 4) := by
  unfold eRad
  have e1 : 2 ^ (log + 4) = 2 ^ log * 16 := by rw [Nat.pow_add]
  have e2 : log + 4 - (pg g).logBlowup = log := rfl
  rw [e2, e1]
  have := Nat.two_pow_pos log
  omega

theorem deep_ok (A : Air) (τ : PTn) (hL : LayOk g A τ) (L0 : TLayout) (hL0 : L0 ∈ layOf A (pg g) τ)
    (hz : ¬ (zOf τ).IsBase)
    (hc : CloseRS (pt (n0Of A (pg g) τ) L0.lde) (2 ^ L0.lde) (2 ^ L0.log) (eRad (pg g) L0.lde)
      (deepWord A (pg g) τ L0.lde)) :
    CloseRS (pt (n0Of A (pg g) τ) L0.lde) (2 ^ L0.lde) (2 ^ L0.log + 1) (eRad (pg g) L0.lde)
      (classWord A (pg g) τ L0.lde 3) ∧
    ∀ d s, (d, s) ∈ deepCols (layOf A (pg g) τ) L0.lde →
      colAt A (pg g) τ d (if s then omg L0.log * zOf τ else zOf τ) = claimed A (pg g) τ d s := by
  let prm := (pg g)
  let m := L0.lde
  let log := L0.log
  let n0 := n0Of A prm τ
  let xs := pt n0 m
  have hm : m = log + 4 := (hL.lde L0 hL0).1
  have hm27 : m ≤ 27 := by have := (hL.lde L0 hL0).2; omega
  have hxs : Distinct xs (2 ^ m) := fun i j hi hj h => pt_inj hm27 hi hj h
  have hEf := eRad_facts (g := g) log
  rw [← hm] at hEf
  have hD : 2 ^ log ≤ 2 ^ m := by omega
  have hD1 : 2 ^ log + 1 ≤ 2 ^ m := hEf.2
  -- the member tables of class m
  have hmem : ∀ d s, (d, s) ∈ deepCols (layOf A prm τ) m → tl A prm τ d.t = tl A prm τ d.t ∧
      (tl A prm τ d.t).lde = m ∧ (tl A prm τ d.t).log = log := fun d s h => by
    obtain ⟨L, hLd, hLm⟩ := mem_deepCols h
    have htl : tl A prm τ d.t = L := by
      unfold tl; rw [List.getD_eq_getElem?_getD, hLd]; rfl
    have := (hL.lde L (List.mem_of_getElem? hLd)).1
    rw [htl]; exact ⟨rfl, hLm, by omega⟩
  have hzpt : ∀ j i, i < 2 ^ m → xs i ≠ deepZ A prm τ m j := fun j i _ => by
    unfold deepZ
    split
    · next d s h =>
      have := hmem d s (List.mem_of_getElem? h)
      split
      · rw [this.2.2]; exact pt_ne_of_not_base (omg_mul_not_base (by omega) hz) _ _ _
      · exact pt_ne_of_not_base hz _ _ _
    · exact pt_ne_zero hm27 i
  obtain ⟨P, hP⟩ := hc
  have hq : Good (rsInterleaved xs (2 ^ m) (2 ^ log) hD hxs Nat) (eRad prm m)
      (deepW xs (deepF A prm τ m) (deepZ A prm τ m) (deepV A prm τ m)) (fun _ _ => 0) 0 := by
    refine ⟨fun p j => ev (2 ^ log) (P j) (xs p), fun j => ⟨P j, fun i _ => rfl⟩,
      Nat.le_trans (dist_mono fun i _ hne he => hne ?_) hP⟩
    funext j
    have := congrFun he j
    show deepW xs (deepF A prm τ m) (deepZ A prm τ m) (deepV A prm τ m) i j + 0 * 0 = _
    rw [← deepWord_eq, this]; grind
  obtain ⟨P', hPz, hPd⟩ := deep_close hD hD1 hxs _ _ _ hzpt hq
  -- single columns
  have hcol : ∀ j d s, (deepCols (layOf A prm τ) m)[j]? = some (d, s) →
      ∀ x, colAt A prm τ d x = ev (2 ^ log + 1) (P' j) x := fun j d s h x => by
    obtain ⟨_, h1, h2⟩ := hmem d s (List.mem_of_getElem? h)
    have hD' : 2 ^ (tl A prm τ d.t).log + 1 + 2 * eRad prm (tl A prm τ d.t).lde ≤
        2 ^ (tl A prm τ d.t).lde := by rw [h1, h2]; exact hEf.1
    have hxs' : Distinct (pt (n0Of A prm τ) (tl A prm τ d.t).lde) (2 ^ (tl A prm τ d.t).lde) := by
      rw [h1]; exact hxs
    rw [colAt_of_close τ d hD' hxs' (P' j) ?_ x, h2]
    rw [h1, h2]
    refine Nat.le_trans (dist_mono fun i _ hne he => hne ?_) hPd
    have := congrFun he j
    funext u
    simp only [deepF, h] at this
    exact this
  refine ⟨?_, fun d s hds => ?_⟩
  · refine closeRS_sub (fun j => ?_) ⟨P', hPd⟩
    unfold classWord
    cases hj : (classCols (layOf A prm τ) m 3)[j]? with
    | none => exact Or.inr fun _ => rfl
    | some d =>
      left
      obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp (deepCols_of_classCols (List.mem_of_getElem? hj))
      exact ⟨j', fun p => by simp only [deepF, hj']⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hds
    have h1 := hcol j d s hj
    have h2 := hPz j
    have hj' : (deepCols (layOf A prm τ) m)[j]? = some (d, s) := hj
    simp only [deepZ, deepV, hj'] at h2
    rw [h1, ← h2, (hmem d s hds).2.2]


/-! ## From `Udr.Np.Msg8` -/

/-! ## Generic helpers -/

theorem list_eq_range_map (l : List Fp8) (n : Nat) (f : Nat → Fp8) (hl : l.length = n)
    (h : ∀ c, c < n → l.getD c 0 = f c) : l = (List.range n).map f := by
  refine List.ext_getElem (by simp [hl]) fun c h1 h2 => ?_
  have := h c (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
  rw [this]; simp

theorem getD_range_map (n : Nat) (f : Nat → Fp8) (c : Nat) :
    ((List.range n).map f).getD c 0 = if c < n then f c else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem mem_deepCols_of {lay : List TLayout} {t : Nat} (ht : t < lay.length) :
    (∀ c, c < lay[t].width → (⟨t, 0, c⟩, false) ∈ deepCols lay lay[t].lde ∧
      (⟨t, 0, c⟩, true) ∈ deepCols lay lay[t].lde) ∧
    (∀ c, c < lay[t].aux → (⟨t, 1, c⟩, false) ∈ deepCols lay lay[t].lde ∧
      (⟨t, 1, c⟩, true) ∈ deepCols lay lay[t].lde) ∧
    (∀ c, c < lay[t].quot → (⟨t, 2, c⟩, false) ∈ deepCols lay lay[t].lde) := by
  have hz : (lay[t], t) ∈ lay.zipIdx.filter (fun (L, _) => L.lde == lay[t].lde) :=
    List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr (by simp), by simp⟩
  have key : ∀ x, x ∈ ((List.range lay[t].width).map (fun c => ((⟨t, 0, c⟩ : Col), false)) ++
      (List.range lay[t].width).map (fun c => ((⟨t, 0, c⟩ : Col), true)) ++
      (List.range lay[t].aux).map (fun c => ((⟨t, 1, c⟩ : Col), false)) ++
      (List.range lay[t].aux).map (fun c => ((⟨t, 1, c⟩ : Col), true)) ++
      (List.range lay[t].quot).map (fun c => ((⟨t, 2, c⟩ : Col), false))) →
      x ∈ deepCols lay lay[t].lde := fun x hx => List.mem_flatMap.mpr ⟨_, hz, hx⟩
  refine ⟨fun c hc => ⟨key _ ?_, key _ ?_⟩, fun c hc => ⟨key _ ?_, key _ ?_⟩, fun c hc => key _ ?_⟩ <;>
    simp [hc]

/-! ## Layout facts -/

theorem layOk_of {A : Air} {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A prm0 l = true) : LayOk g A τ := by
  obtain ⟨hlen, hlog, _, _⟩ := headerOk_facts hh
  refine ⟨fun L hL => ?_⟩
  unfold layOf hdrOf at hL; rw [hl] at hL
  simp only [Option.getD_some, layout, List.mem_map] at hL
  obtain ⟨⟨T, x⟩, hTx, rfl⟩ := hL
  obtain ⟨t, ht, he⟩ := List.mem_iff_getElem.mp hTx
  simp only [List.getElem_zip, Prod.mk.injEq] at he
  have := hlog t (by simp at ht; omega) (by simp at ht; omega)
  rw [he.2] at this
  have h26 : (pg g).maxLogLde = 26 := rfl
  have h4 : (pg g).logBlowup = 4 := rfl
  exact ⟨by simp [h4], by simp; omega⟩

theorem tl_mem {A : Air} {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A prm0 l = true) (t : Nat) (ht : t < A.tables.length) :
    (layOf A prm0 τ).length = A.tables.length ∧ t < (layOf A prm0 τ).length ∧
      tl A prm0 τ t = (layOf A prm0 τ)[t]'(by
        have := (headerOk_facts hh).1
        unfold layOf hdrOf; rw [hl]; simp [layout]; omega) := by
  have hlen := (headerOk_facts hh).1
  have hlay : (layOf A prm0 τ).length = A.tables.length := by
    unfold layOf hdrOf; rw [hl]; simp [layout, hlen]
  refine ⟨hlay, by omega, ?_⟩
  unfold tl; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

/-! ## The polynomial environment at `z ∉ F` is `oodEnv` -/

theorem env_eq (A : Air) (τ : PTn) (t : Nat) (z : Fp8) (hz : ¬ z.IsBase)
    (hlog : (tl A prm0 τ t).log ≤ 27) (mainZ mainG : List Fp8)
    (hZ : ∀ c, mainZ.getD c 0 = colAt A prm0 τ ⟨t, 0, c⟩ z)
    (hG : ∀ c, mainG.getD c 0 = colAt A prm0 τ ⟨t, 0, c⟩ (omg (tl A prm0 τ t).log * z)) :
    oodEnv (pubOf Fp τ.cb) (tl A prm0 τ t).log z mainZ mainG = polyEnv A prm0 τ t z := by
  have hT := natCast_two_pow_ne hlog
  have hz1 := one_not_base_ne hz
  have hωz1 := one_not_base_ne (omg_mul_not_base hlog hz)
  have hpow : (omg (tl A prm0 τ t).log * z) ^ (2 ^ (tl A prm0 τ t).log) = z ^ (2 ^ (tl A prm0 τ t).log) := by
    rw [CommSemiring.mul_pow, omg_pow_T hlog, Semiring.one_mul]
  have hF := sel_closed hT hz1
  have hL := sel_closed hT hωz1
  rw [hpow] at hL
  unfold oodEnv polyEnv
  dsimp only
  have ecol : (fun (c : Nat) (nx : Bool) => (if nx then mainG else mainZ).getD c 0) =
      fun (c : Nat) (nx : Bool) => colAt A prm0 τ ⟨t, 0, c⟩ (if nx then omg (tl A prm0 τ t).log * z else z) := by
    funext c nx; cases nx
    · exact hZ c
    · exact hG c
  rw [ecol]
  have e1 : (StarkField.embed (StarkField.twoAdicGen (K := Fp8) (tl A prm0 τ t).log : Fp) : Fp8) =
      omg (tl A prm0 τ t).log := rfl
  rw [e1, hF, hL]
  rfl

/-! ## Decoding facts of one table -/

section
variable {A : Air} {τ : PTn} {l : List Nat}

theorem tl_dec (hl : τ.header? = some l) (hh : headerOk A prm0 l = true) (t : Nat)
    (ht : t < A.tables.length) :
    2 ^ (tl A prm0 τ t).log + 1 + 2 * eRad prm0 (tl A prm0 τ t).lde ≤ 2 ^ (tl A prm0 τ t).lde ∧
    Distinct (pt (n0Of A prm0 τ) (tl A prm0 τ t).lde) (2 ^ (tl A prm0 τ t).lde) ∧
    (tl A prm0 τ t).lde = (tl A prm0 τ t).log + 4 ∧ (tl A prm0 τ t).lde ≤ 26 := by
  obtain ⟨_, hlt, htl⟩ := tl_mem hl hh t ht
  have hmem : tl A prm0 τ t ∈ layOf A prm0 τ := by rw [htl]; exact List.getElem_mem _
  have h := (layOk_of hl hh).lde _ hmem
  refine ⟨?_, fun i j hi hj e => pt_inj (by omega) hi hj e, h⟩
  have := (eRad_facts (g := g) (tl A prm0 τ t).log).1
  rw [← h.1] at this; exact this

theorem colAt_zero (hl : τ.header? = some l) (hh : headerOk A prm0 l = true) {o0 : Oracle Fp}
    (ho0 : oracleOf τ 0 = o0) (hf0 : OFits o0 ((layout A prm0 l).map fun L => (L.lde, L.width)))
    (t : Nat) (ht : t < A.tables.length) (c : Nat) (hc : (tl A prm0 τ t).width ≤ c) (x : Fp8) :
    colAt A prm0 τ ⟨t, 0, c⟩ x = 0 := by
  obtain ⟨hD, hxs, _⟩ := tl_dec hl hh t ht
  obtain ⟨hlay, hlt, htl⟩ := tl_mem hl hh t ht
  have hlayl : layOf A prm0 τ = layout A prm0 l := by unfold layOf hdrOf; rw [hl]; rfl
  rw [colAt_of_close τ ⟨t, 0, c⟩ hD hxs (fun _ => 0) ?_ x]
  · exact ev_eq_zero (fun _ _ => rfl) x
  · have ho0l : t < o0.length := by rw [hf0.1, List.length_map, ← hlayl]; exact hlt
    obtain ⟨sh, hsh, hlog, hwid, hrow⟩ := hf0.2 t ho0l
    have hsh' : sh = ((tl A prm0 τ t).lde, (tl A prm0 τ t).width) := by
      rw [htl] at *
      simp only [List.getElem?_map] at hsh
      rw [← hlayl, List.getElem?_eq_getElem hlt] at hsh
      simp only [Option.map_some, Option.some.injEq] at hsh
      exact hsh.symm
    subst hsh'
    have hzero : ∀ p, p < 2 ^ (tl A prm0 τ t).lde → colVal τ ⟨t, 0, c⟩ p = 0 := fun p hp => by
      simp only [colVal, if_pos, ho0]
      have hm : matOf o0 t = o0[t] := by
        unfold matOf; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho0l]; rfl
      rw [hm, List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [hrow p (by rw [hlog]; exact hp), hwid]; exact hc)]
      rfl
    have : dist (2 ^ (tl A prm0 τ t).lde) (fun p (_ : Unit) => colVal τ ⟨t, 0, c⟩ p)
        (fun p _ => ev (2 ^ (tl A prm0 τ t).log + 1) (fun _ => 0) (pt (n0Of A prm0 τ) (tl A prm0 τ t).lde p))
        ≤ 0 := by
      refine Nat.le_trans (count_mono_mem _ (F := fun _ => False) fun p hp hne => hne ?_) (by
        rw [count_const]; simp)
      funext u
      show colVal τ ⟨t, 0, c⟩ p = ev (2 ^ (tl A prm0 τ t).log + 1) (fun _ => 0) _
      rw [hzero p (List.mem_range.mp hp), ev_eq_zero (fun _ _ => rfl)]
    exact Nat.le_trans this (Nat.zero_le _)

end

/-! ## One table's ALI identity from the global checks -/

theorem zip3_get {α β γ' : Type} (a : List α) (b : List β) (c : List γ') (t : Nat)
    (h : t < (a.zip (b.zip c)).length) :
    (a.zip (b.zip c))[t] = (a[t]'(by simp at h; omega), b[t]'(by simp at h; omega), c[t]'(by simp at h; omega)) := by
  simp [List.getElem_zip]

theorem zip3_take_map {α β γ' : Type} (a : List α) (b : List β) (c : List γ') (hab : b.length ≤ a.length)
    (hbc : b.length ≤ c.length) (f : β → Nat) (k : Nat) :
    ((a.zip (b.zip c)).take k).map (fun x => f x.2.1) = (b.take k).map f := by
  rw [List.map_take]
  have : ∀ (a : List α) (b : List β) (c : List γ'), b.length ≤ a.length → b.length ≤ c.length →
      (a.zip (b.zip c)).map (fun x => f x.2.1) = b.map f := by
    intro a b c h1 h2
    induction b generalizing a c with
    | nil => simp
    | cons y b ih =>
      match a, c, h1, h2 with
      | x :: a, z :: c, h1, h2 =>
        simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
        exact ih a c (by simp at h1; omega) (by simp at h2; omega)
  rw [this a b c hab hbc, List.map_take]

theorem ali_of_global {A : Air} {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A prm0 l = true) {o0 : Oracle Fp}
    (ho0 : oracleOf τ 0 = o0) (hf0 : OFits o0 ((layout A prm0 l).map fun L => (L.lde, L.width)))
    {ood : List Fp8} (hood : τ.elems.getD 1 [] = ood)
    (hoodl : ood.length = ((layOf A prm0 τ).map oodCnt).sum) (hz : ¬ (zOf τ).IsBase)
    (t : Nat) (ht : t < A.tables.length)
    (hclaim : ∀ d s, (d, s) ∈ deepCols (layOf A prm0 τ) (tl A prm0 τ t).lde →
      colAt A prm0 τ d (if s then omg (tl A prm0 τ t).log * zOf τ else zOf τ) = claimed A prm0 τ d s)
    (αfp γ αc : Fp8)
    (hX : t < (A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1)).length)
    (hk : aliOk A prm0 (pubOf Fp τ.cb) αfp γ αc (zOf τ)
      (A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1))[t].1
      (A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1))[t].2.1
      (A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1))[t].2.2
      (((finalsOf τ).drop (((A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1)).take t).map
          fun x => x.2.1.sendG + x.2.1.recvG).sum).take
        ((A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1))[t].2.1.sendG +
          (A.tables.zip ((layOf A prm0 τ).zip (splitOod (layOf A prm0 τ) ood).1))[t].2.1.recvG))) :
    Ct A prm0 τ t αfp γ αc (zOf τ) =
      ((zOf τ) ^ (2 ^ (tl A prm0 τ t).log) - 1) * Qt A prm0 τ t (zOf τ) := by
  obtain ⟨hlay, hlt, htl⟩ := tl_mem hl hh t ht
  obtain ⟨_, _, hlde, h26⟩ := tl_dec hl hh t ht
  have hlog : (tl A prm0 τ t).log ≤ 27 := by omega
  have hsp := splitOod_props (layOf A prm0 τ) ood hoodl
  have hoodsl : (splitOod (layOf A prm0 τ) ood).1.length = (layOf A prm0 τ).length := hsp.1
  have hto : t < (splitOod (layOf A prm0 τ) ood).1.length := by omega
  have hfit := hsp.2 t hto hlt
  rw [zip3_get] at hk
  simp only at hk
  have e3 := zip3_take_map (f := fun L => L.sendG + L.recvG) A.tables (layOf A prm0 τ)
    (splitOod (layOf A prm0 τ) ood).1 (by omega) (by omega) t
  rw [e3] at hk
  rw [← htl] at hk hfit
  -- claimed values are slices of `(splitOod (layOf A prm0 τ) ood).1[t]`
  have hcl : ∀ d s, d.t = t → claimed A prm0 τ d s =
      match d.kind, s with
      | 0, false => (splitOod (layOf A prm0 τ) ood).1[t].mainZ.getD d.c 0
      | 0, true => (splitOod (layOf A prm0 τ) ood).1[t].mainG.getD d.c 0
      | 1, false => (splitOod (layOf A prm0 τ) ood).1[t].auxZ.getD d.c 0
      | 1, true => (splitOod (layOf A prm0 τ) ood).1[t].auxG.getD d.c 0
      | _, _ => (splitOod (layOf A prm0 τ) ood).1[t].quotZ.getD d.c 0 := fun d s hd => by
    unfold claimed
    rw [hood, hd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hto]
    rfl
  have hmem := mem_deepCols_of hlt
  rw [← htl] at hmem
  have hT : tableOf A t = A.tables[t] := tableOf_lt ht
  -- main values
  have hmZ : ∀ c, (splitOod (layOf A prm0 τ) ood).1[t].mainZ.getD c 0 = colAt A prm0 τ ⟨t, 0, c⟩ (zOf τ) := fun c => by
    by_cases hc : c < (tl A prm0 τ t).width
    · have := hclaim _ _ (hmem.1 c hc).1
      rw [hcl _ _ rfl] at this
      simp only [Bool.false_eq_true, if_false] at this
      exact this.symm
    · rw [colAt_zero hl hh ho0 hf0 t ht c (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [hfit.1]; omega)]; rfl
  have hmG : ∀ c, (splitOod (layOf A prm0 τ) ood).1[t].mainG.getD c 0 =
      colAt A prm0 τ ⟨t, 0, c⟩ (omg (tl A prm0 τ t).log * zOf τ) := fun c => by
    by_cases hc : c < (tl A prm0 τ t).width
    · have := hclaim _ _ (hmem.1 c hc).2
      rw [hcl _ _ rfl] at this
      simp only [if_true] at this
      exact this.symm
    · rw [colAt_zero hl hh ho0 hf0 t ht c (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [hfit.2.1]; omega)]; rfl
  have hEnv := env_eq A τ t (zOf τ) hz hlog _ _ hmZ hmG
  have haZ : (splitOod (layOf A prm0 τ) ood).1[t].auxZ = (List.range (tl A prm0 τ t).aux).map
      fun a => colAt A prm0 τ ⟨t, 1, a⟩ (zOf τ) := list_eq_range_map _ _ _ hfit.2.2.1 fun c hc => by
    have := hclaim _ _ (hmem.2.1 c hc).1
    rw [hcl _ _ rfl] at this
    simp only [Bool.false_eq_true, if_false] at this
    exact this.symm
  have haG : (splitOod (layOf A prm0 τ) ood).1[t].auxG = (List.range (tl A prm0 τ t).aux).map
      fun a => colAt A prm0 τ ⟨t, 1, a⟩ (omg (tl A prm0 τ t).log * zOf τ) :=
    list_eq_range_map _ _ _ hfit.2.2.2.1 fun c hc => by
    have := hclaim _ _ (hmem.2.1 c hc).2
    rw [hcl _ _ rfl] at this
    simp only [if_true] at this
    exact this.symm
  have hqZ : (splitOod (layOf A prm0 τ) ood).1[t].quotZ = (List.range (tl A prm0 τ t).quot).map
      fun a => colAt A prm0 τ ⟨t, 2, a⟩ (zOf τ) := list_eq_range_map _ _ _ hfit.2.2.2.2 fun c hc => by
    have := hclaim _ _ (hmem.2.2 c hc)
    rw [hcl _ _ rfl] at this
    simp only [Bool.false_eq_true, if_false] at this
    exact this.symm
  have hfins : ((finalsOf τ).drop (((layOf A prm0 τ).take t).map fun L => L.sendG + L.recvG).sum).take
      ((tl A prm0 τ t).sendG + (tl A prm0 τ t).recvG) = finsOf A prm0 τ t := rfl
  unfold aliOk at hk
  rw [hEnv, haZ, haG, hqZ, hfins, ← hT] at hk
  unfold Ct Qt csAt
  exact hk

/-! ## `Msg8` -/


/-! ## From `Udr.Np.QueryFacts` -/

section
variable (A : Air)

theorem lay_facts (hdr : List Nat) (h : headerOk A (pg g) hdr = true) :
    ∀ L ∈ layout A (pg g) hdr, 5 ≤ L.lde ∧ L.lde ≤ 26 ∧ L.lde = L.log + 4 := by
  simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro L hL
  simp only [layout, List.mem_map] at hL
  obtain ⟨⟨T, l⟩, hm, rfl⟩ := hL
  have := h.1.1.2 _ hm
  simp only [pg, Params.default] at this
  show 5 ≤ l + 4 ∧ l + 4 ≤ 26 ∧ l + 4 = l + 4
  omega

theorem qf_foldr_max_le (l : List Nat) (b c : Nat) (hb : b ≤ c) (h : ∀ x ∈ l, x ≤ c) :
    l.foldr max b ≤ c := by
  induction l with
  | nil => exact hb
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem qf_le_foldr_max (l : List Nat) (b x : Nat) (hx : x ∈ l) : x ≤ l.foldr max b := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem queryLog_le (hdr : List Nat) (h : headerOk A (pg g) hdr = true) :
    queryLog A (pg g) hdr ≤ 26 :=
  qf_foldr_max_le _ _ _ (by omega) fun x hx => by
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx
    exact (lay_facts A hdr h L hL).2.1

theorem lde_le_queryLog (prm : Params) (hdr : List Nat) (L : TLayout) (hL : L ∈ layout A prm hdr) :
    L.lde ≤ queryLog A prm hdr :=
  qf_le_foldr_max _ _ _ (List.mem_map.mpr ⟨L, hL, rfl⟩)

end

/-! ## From `Udr.Np.Late` -/

theorem eRad_two (m : Nat) : 2 * eRad (pg g) m + 2 ^ (m - 4) ≤ 2 ^ m := by
  unfold eRad
  simp only [show (pg g).logBlowup = 4 from rfl]
  have : 2 ^ (m - 4) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem bound_budget (m : Nat) (hm : m ≤ 26) : 3 * 2 ^ m + 2 * eRad (pg g) m + 1 ≤ badBudget := by
  have h1 := eRad_two (g := g) m
  have h2 : 2 ^ m ≤ 67108864 := Nat.le_trans (Nat.pow_le_pow_right (by omega) hm) (by decide)
  have h3 : badBudget = 68719476736 := rfl
  rw [h3]
  generalize 2 ^ m = b at *
  generalize eRad (pg g) m = c at *
  generalize 2 ^ (m - 4) = f at *
  omega

/-! ## From `Udr.Np.Query` -/

theorem eRad_step (m : Nat) (hm : 5 ≤ m) :
    eRad (pg g) (m + 1) ≤ 2 * eRad (pg g) m + 1 := by
  simp only [eRad, show (pg g).logBlowup = 4 from rfl]
  have h1 : 2 ^ m = 2 ^ (m - 5) * 32 := by
    rw [← show 2 ^ 5 = 32 from rfl, ← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (m + 1) = 2 ^ (m - 5) * 64 := by
    rw [← show 2 ^ 6 = 64 from rfl, ← Nat.pow_add]; congr 1; omega
  have h3 : 2 ^ (m - 4) = 2 ^ (m - 5) * 2 := by
    rw [← show 2 ^ 1 = 2 from rfl, ← Nat.pow_add]; congr 1; omega
  have h4 : 2 ^ (m + 1 - 4) = 2 ^ (m - 5) * 4 := by
    rw [← show 2 ^ 2 = 4 from rfl, ← Nat.pow_add]; congr 1; omega
  have h5 : 1 ≤ 2 ^ (m - 5) := Nat.one_le_two_pow
  rw [h1, h2, h3, h4]; omega


/-! ## From `Udr.Np.Bridge6` (without `roll_eq`, restated in `G.Query`) -/

section
variable (A : Air) (τ : PTn)

/-- The verifier's fold arriving at layer `e` on the path through `x`. -/
def Arr (x e : Nat) : Fp8 :=
  foldPos (n0Of A P0 τ) (e - 1) (2 * (x >>> e)) (betaOf A P0 τ (e - 1))
    (Fv A P0 τ (e - 1) (2 * (x >>> e))) (Fv A P0 τ (e - 1) (2 * (x >>> e) + 1))

theorem ell_eq (Q : QData A P0 τ) : ellOf A P0 τ = n0Of A P0 τ - 5 := by
  simp only [ellOf, finalLayer, n0Of]; rfl

theorem arr_eq (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (j : Nat) (hj : j < 2 ^ n0Of A P0 τ)
    (e : Nat) (he1 : 1 ≤ e) (heℓ : e ≤ ellOf A P0 τ) :
    Fri.foldW (mkSetup A P0 τ hn0) (mkRun A P0 τ) (e - 1) (j % 2 ^ (n0Of A P0 τ - e)) () =
      Arr (g := g) A τ (permAt A P0 τ 0 j) e := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  have hb : j % 2 ^ (n0Of A P0 τ - e) < 2 ^ (n0Of A P0 τ - (e - 1 + 1)) := by
    rw [show e - 1 + 1 = e by omega]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have := fold_eq_foldPos τ hn0 hl (e - 1) (by omega) _ hb (betaOf A P0 τ (e - 1))
  rw [show e - 1 + 1 = e by omega, permAt_path A P0 τ hl e j heℓ hj] at this
  exact this

theorem rollInV_eq (Q : QData A P0 τ) (op : List (List (List Fp))) (x i : Nat) (hi1 : 1 ≤ i)
    (hiℓ : i ≤ finalLayer A P0 Q.hdr) (v : Fp8) :
    rollInV (Stark.prep (F := Fp) A P0 τ.erase) op x i v =
      v + gammaOf A P0 τ i * (if rollInAt A P0 Q.hdr i then
        deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op ((Stark.prep (F := Fp) A P0 τ.erase).n0 - i) x
        else 0) := by
  have := rollIn_eq Q i hi1 hiℓ v
    (deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op ((Stark.prep (F := Fp) A P0 τ.erase).n0 - i) x)
  simp only [rollInV]
  cases h : (Stark.prep (F := Fp) A P0 τ.erase).gammas.lookup i <;> simp only [h] at this ⊢ <;> exact this

theorem shl_add (b t a : Nat) (ht : t < 2 ^ a) :
    ((b <<< a) + t) >>> a = b ∧ ((b <<< a) + t) % 2 ^ a = t := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hp : 0 < 2 ^ a := Nat.pow_pos (by omega)
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem shr_lt (x n c : Nat) (hx : x < 2 ^ n) (hc : c ≤ n) : x >>> c < 2 ^ (n - c) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add, show c + (n - c) = n by omega]; exact hx)

/-- The FRI word at the layer of commit `k`, on verifier positions. -/
theorem Fv_committed (Q : QData A P0 τ) (k : Nat) (hk : k < (commitsOf A P0 τ).length) (P : Nat)
    (hP : P < 2 ^ (n0Of A P0 τ - ((commitsOf A P0 τ)[k]).1)) :
    Fv A P0 τ ((commitsOf A P0 τ)[k]).1 P = committedAt τ k ((commitsOf A P0 τ)[k]).2 P := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  have hcl : ((commitsOf A P0 τ)[k]).1 ≤ ellOf A P0 τ := by
    have := (commits_mem A P0 Q.hdr _ (by rw [← Q.commits]; exact List.getElem_mem hk)).1
    rw [Q.ell]; omega
  simp only [Fv]
  rw [friF_committed A P0 τ k hk, (permAt_permInv τ hl _ hcl P hP).1]

/-- At a layer strictly inside a commit block the FRI word is the plain fold. -/
theorem Fv_inner (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (i : Nat) (hiℓ : i < ellOf A P0 τ)
    (hnc : ∀ k (hk : k < (commitsOf A P0 τ).length), ((commitsOf A P0 τ)[k]).1 ≠ i + 1)
    (hnr : rollInAt A P0 Q.hdr (i + 1) = false) (q : Nat) (hq : q < 2 ^ (n0Of A P0 τ - (i + 1))) :
    Fv A P0 τ (i + 1) q = foldPos (n0Of A P0 τ) i (2 * q) (betaOf A P0 τ i)
      (Fv A P0 τ i (2 * q)) (Fv A P0 τ i (2 * q + 1)) := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  obtain ⟨h1, h2⟩ := permAt_permInv τ hl (i + 1) (by omega) q hq
  simp only [Fv]
  rw [friF_virtual A P0 τ i hnc]
  generalize hj : permInvK (n0Of A P0 τ) (ellOf A P0 τ) (ellOf A P0 τ - (i + 1)) q = j'' at h1 h2
  have hz : rollG A P0 τ i j'' () = 0 := by
    simp only [rollG, Q.hhdr, hnr, Bool.false_eq_true, ↓reduceIte]
  have := fold_eq_foldPos τ hn0 hl i hiℓ j'' h2 (betaOf A P0 τ i)
  rw [h1] at this
  simp only [Fv] at this
  rw [← this]
  simp only [line, hz]
  show _ + _ * 0 = _
  rw [Semiring.mul_zero, Semiring.add_zero]
  rfl

/-- Structure of commit `k`: a block `(c0, c0 + a)` with `a ≥ 1`, inside `[0, ℓ]`,
without commitments or roll-ins strictly inside. -/
theorem block_facts (Q : QData A P0 τ) (k : Nat) (hk : k < (commitsOf A P0 τ).length) :
    1 ≤ ((commitsOf A P0 τ)[k]).2 ∧
    ((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2 ≤ ellOf A P0 τ ∧
    (∀ i, ((commitsOf A P0 τ)[k]).1 < i → i < ((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2 →
      rollInAt A P0 Q.hdr i = false ∧
      ∀ k' (hk' : k' < (commitsOf A P0 τ).length), ((commitsOf A P0 τ)[k']).1 ≠ i) := by
  have hcm := Q.commits
  have hk2 : k < (friCommits A P0 Q.hdr).length := by rw [← hcm]; exact hk
  obtain ⟨-, h2, h3, h4⟩ := chain_get A P0 Q.hdr _ _ 0 (chain_commits A P0 Q.hdr) k hk2
  have hs := List.pairwise_iff_getElem.mp (commits_sorted A P0 Q.hdr)
  simp only [hcm, Q.ell]
  refine ⟨h2, ?_, fun i hi1 hi2 => ⟨h3 i hi1 hi2, fun k' hk' heq => ?_⟩⟩
  · split at h4
    · rename_i hh
      have := (commits_mem A P0 Q.hdr _ (List.getElem_mem hh)).1
      omega
    · omega
  · have hk'2 : k' < (friCommits A P0 Q.hdr).length := hk'
    rcases Nat.lt_trichotomy k' k with hlt | heq' | hgt
    · have := hs k' k hk'2 hk2 hlt; omega
    · subst heq'; omega
    · split at h4
      · rename_i hh
        by_cases hkk : k' = k + 1
        · subst hkk; omega
        · have := hs (k + 1) k' hh hk'2 (by omega); omega
      · omega

/-- **The folded committed leaf** is the fold arriving at the end of the block. -/
theorem leaf_eq (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (x : Nat) (hx : x < 2 ^ n0Of A P0 τ)
    (k : Nat) (hk : k < (commitsOf A P0 τ).length) (o : List (List Fp))
    (ho : ksOfRow (F := Fp) (K := Fp8) (o.getD 0 []) =
      ksOfRow ((matOf (oracleOf τ (3 + k)) 0).row ((x >>> ((commitsOf A P0 τ)[k]).1) >>> ((commitsOf A P0 τ)[k]).2)))
    (hlen : (ksOfRow (F := Fp) (K := Fp8) (o.getD 0 [])).length = 2 ^ ((commitsOf A P0 τ)[k]).2) :
    foldLeaf (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) ((commitsOf A P0 τ)[k]).1 ((commitsOf A P0 τ)[k]).2
        ((x >>> ((commitsOf A P0 τ)[k]).1) >>> ((commitsOf A P0 τ)[k]).2) (ksOfRow (o.getD 0 [])) =
      Arr (g := g) A τ x (((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2) := by
  obtain ⟨ha1, hcaℓ, hin⟩ := block_facts A τ Q k hk
  generalize hc0 : ((commitsOf A P0 τ)[k]).1 = c0 at *
  generalize ha : ((commitsOf A P0 τ)[k]).2 = a at *
  have hℓ := ell_eq A τ Q
  have hn0c : c0 + a ≤ n0Of A P0 τ := by omega
  have hpa : (x >>> c0) >>> a < 2 ^ (n0Of A P0 τ - (c0 + a)) := by
    rw [← Nat.shiftRight_add]; exact shr_lt _ _ _ hx hn0c
  let U : Nat → Nat → Fp8 := fun s q => if s < a then Fv A P0 τ (c0 + s) q else
    foldPos (n0Of A P0 τ) (c0 + a - 1) (2 * q) (betaOf A P0 τ (c0 + a - 1))
      (Fv A P0 τ (c0 + a - 1) (2 * q)) (Fv A P0 τ (c0 + a - 1) (2 * q + 1))
  have key := foldLeaf_eq (Stark.prep (F := Fp) A P0 τ.erase) c0 a ((x >>> c0) >>> a) _ U hlen
    (fun t ht => ?_) (fun s q hs hq => ?_)
  · rw [key]
    simp only [U, Nat.lt_irrefl, ↓reduceIte, Arr, Nat.shiftRight_add,
      show c0 + a - 1 = c0 + a - 1 from rfl]
  · -- the leaf values
    obtain ⟨e1, e2⟩ := shl_add ((x >>> c0) >>> a) t a ht
    have hP : ((x >>> c0) >>> a) <<< a + t < 2 ^ (n0Of A P0 τ - c0) := by
      rw [Nat.shiftLeft_eq]
      have : 2 ^ (n0Of A P0 τ - c0) = 2 ^ (n0Of A P0 τ - (c0 + a)) * 2 ^ a := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [this]
      have := Nat.mul_le_mul_right (2 ^ a) (show (x >>> c0) >>> a + 1 ≤ 2 ^ (n0Of A P0 τ - (c0 + a)) by omega)
      rw [Nat.succ_mul] at this; omega
    simp only [U, show 0 < a by omega, ↓reduceIte, Nat.add_zero]
    rw [← hc0, Fv_committed A τ Q k hk _ (by rw [hc0]; exact hP), ho]
    simp only [committedAt, ha]
    rw [hc0, e1, e2]
  · -- the folds
    have hβ : (Stark.prep (F := Fp) A P0 τ.erase).betas.getD (c0 + s) 0 = betaOf A P0 τ (c0 + s) :=
      prepF_betas Q (c0 + s) (by rw [← Q.ell]; omega)
    rw [hβ, prepF_n0 Q]
    by_cases hs1 : s + 1 < a
    · simp only [U, hs1, hs, ↓reduceIte]
      obtain ⟨hr, hc⟩ := hin (c0 + s + 1) (by omega) (by omega)
      have hq' : q < 2 ^ (n0Of A P0 τ - (c0 + s + 1)) := by
        have h2 : 2 ^ (n0Of A P0 τ - (c0 + s + 1)) = 2 ^ (n0Of A P0 τ - (c0 + a)) * 2 ^ (a - (s + 1)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [h2]
        have := Nat.mul_le_mul_right (2 ^ (a - (s + 1)))
          (show (x >>> c0) >>> a + 1 ≤ 2 ^ (n0Of A P0 τ - (c0 + a)) by omega)
        omega
      rw [show c0 + (s + 1) = c0 + s + 1 by omega]
      exact Fv_inner A τ hn0 Q (c0 + s) (by omega) (fun k' hk' => by
        have := hc k' hk'; omega) hr q hq'
    · have hsa : s + 1 = a := by omega
      simp only [U, hs, ↓reduceIte, show ¬ (s + 1 < a) from hs1]
      rw [show c0 + a - 1 = c0 + s by omega]

end

end ZkFormal.V2.G
