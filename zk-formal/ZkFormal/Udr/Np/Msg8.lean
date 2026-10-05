import ZkFormal.Udr.Np.Global8

/-!
# ZkFormal.Udr.Np.Msg8 — the OOD-values message (`E = 8 → 9`)

After the OOD values, the transcript is doomed if the clear-text checks fail
or some class's DEEP word is far.  If neither: every DEEP word is close, so
(`deep_ok`) all classes are close and all claimed values are the decoded
values at `z`, `ωz`; then L4's `globalChecks` computes exactly `C_t(z)` and
`(z^T - 1)·Q_t(z)` (`oodEnv` = `polyEnv` at `z ∉ F`), and its bus equation is
`¬ BusFinalsFail` — contradicting stage 8.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr

local notation "prm0" => Params.default

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
    (hh : headerOk A prm0 l = true) : LayOk A τ := by
  obtain ⟨hlen, hlog, _, _⟩ := headerOk_facts hh
  refine ⟨fun L hL => ?_⟩
  unfold layOf hdrOf at hL; rw [hl] at hL
  simp only [Option.getD_some, layout, List.mem_map] at hL
  obtain ⟨⟨T, x⟩, hTx, rfl⟩ := hL
  obtain ⟨t, ht, he⟩ := List.mem_iff_getElem.mp hTx
  simp only [List.getElem_zip, Prod.mk.injEq] at he
  have := hlog t (by simp at ht; omega) (by simp at ht; omega)
  rw [he.2] at this
  have h26 : Params.default.maxLogLde = 26 := rfl
  have h4 : Params.default.logBlowup = 4 := rfl
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
  have := (eRad_facts (tl A prm0 τ t).log).1
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

theorem msg8 : Msg8Stmt := by
  intro A prm hok τ m hs _ hE hst
  obtain ⟨hprm, _, _⟩ := hok
  subst hprm
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hsτ := (shapedPrefix A _ τ).1 m hs
  obtain ⟨S⟩ := shape8 hsτ hE
  obtain ⟨l2, hl2, _, s8, h81, h82⟩ := push_fits hs hne
  rw [S.hl] at hl2; cases hl2
  rw [hE, (sched_odd A prm0 S.l).2.2.2.2] at h81; cases h81
  obtain ⟨a8, hm, ha8⟩ := fits_one h82
  cases hm
  obtain ⟨ood, rfl, hoodl⟩ := fits_elems ha8
  -- the transcripts
  have hent := S.hent
  have hchals : τ.chals = [S.c1, S.c3, S.c5, S.c7] := by
    unfold PT.chals; rw [hent]; rfl
  have hchals' : (τ.push [PartV.elems ood]).chals = [S.c1, S.c3, S.c5, S.c7] := by
    rw [chals_push, hchals]
  have helems : τ.elems = [S.fins] := by unfold PT.elems; rw [hent]; rfl
  have helems' : (τ.push [PartV.elems ood]).elems = [S.fins, ood] := by
    unfold PT.elems PT.push; simp only [hent]; rfl
  have hor : τ.oracles = [S.o0, S.o1, S.o2] := by unfold PT.oracles; rw [hent]; rfl
  have hor' : (τ.push [PartV.elems ood]).oracles = [S.o0, S.o1, S.o2] := by
    unfold PT.oracles PT.push; simp only [hent]; rfl
  have hh' : (τ.push [PartV.elems ood]).header? = τ.header? := header?_push τ _ hne
  have hl' : (τ.push [PartV.elems ood]).header? = some S.l := by rw [hh', S.hl]
  have hO : ∀ k, OAgree k (τ.push [PartV.elems ood]) τ := fun k =>
    ⟨rfl, hh', fun i _ => by unfold oracleOf; rw [hor', hor]⟩
  have hfin : finalsOf (τ.push [PartV.elems ood]) = finalsOf τ := by
    unfold finalsOf; rw [helems', helems]; rfl
  have hfin' : finalsOf (τ.push [PartV.elems ood]) = S.fins := by
    unfold finalsOf; rw [helems']; rfl
  have hE' : (τ.push [PartV.elems ood]).entries.length = 9 := by rw [len_push, hE]
  generalize hτ' : τ.push [PartV.elems ood] = τ' at *
  have hz' : zOf τ' = S.c7 := by unfold zOf; rw [hchals']; rfl
  -- stage 8 of τ
  simp only [Stage, hE, hchals] at hst
  have hz : ¬ (zOf τ').IsBase := by rw [hz']; exact hst.1
  -- the claim
  simp only [Stage, hE']
  refine Classical.byContradiction fun hno => ?_
  have hfri : FriGoodSoFar A prm0 τ' := by
    intro q hq
    exfalso
    have : friChals A prm0 τ' = [] := by
      unfold friChals; rw [hchals', List.drop_eq_nil_of_le (by simp), List.zip_nil_right]
    rw [this] at hq; exact Nat.not_lt_zero _ hq
  rw [_root_.not_or] at hno
  obtain ⟨hGF, hBF0⟩ := hno
  have hBF : ∀ L ∈ layOf A prm0 τ', ¬ BatchFar A prm0 τ' L.lde L.log := fun L hL hf => hBF0 ⟨⟨L, hL, hf⟩, hfri⟩
  have hg : globalChecks (F := Fp) A prm0 (pubOf Fp τ'.cb) (layOf A prm0 τ')
      (splitOod (layOf A prm0 τ') ood).1 S.fins S.c1 S.c3 S.c5 S.c7 = true := by
    unfold GlobalFail at hGF; rw [hchals', helems'] at hGF
    simpa using hGF
  have hbw : ∀ m, batchedWord A prm0 τ' m = deepWord A prm0 τ' m := fun m => by
    unfold batchedWord batchChals; rw [hchals', List.drop_eq_nil_of_le (by simp), List.take_nil]; rfl
  have hLay := layOk_of hl' S.hh
  have hdeep : ∀ L ∈ layOf A prm0 τ', _ := fun L hL => by
    have hc := hBF L hL
    unfold BatchFar at hc
    rw [hbw, Classical.not_not] at hc
    exact deep_ok A τ' hLay L hL hz hc
  have hAC : AllClose A prm0 τ' 3 := fun L hL => (hdeep L hL).1
  have hgt := globalChecks_true hg
  rcases hst.2 with h | ⟨t, ht, hC⟩ | h
  · exact h ((allClose_congr (hO 3) (by omega)).mp hAC)
  · apply hC
    obtain ⟨_, hlt, htl⟩ := tl_mem hl' S.hh t ht
    have hd := (hdeep _ (List.getElem_mem hlt)).2
    rw [← htl] at hd
    have hoodl' : ood.length = ((layOf A prm0 τ').map oodCnt).sum := by
      rw [hoodl]; unfold layOf hdrOf; rw [hl']; rfl
    have hsp := splitOod_props (layOf A prm0 τ') ood hoodl'
    have hX : t < (A.tables.zip ((layOf A prm0 τ').zip (splitOod (layOf A prm0 τ') ood).1)).length := by
      simp only [List.length_zip]; omega
    have hk := hgt.1 t hX
    rw [← hfin'] at hk
    have := ali_of_global hl' S.hh (by unfold oracleOf; rw [hor']; rfl) S.hf0
      (by rw [helems']; rfl) hoodl' hz t ht hd S.c1 S.c3 S.c5 hX (by rw [hz']; exact hk)
    rw [hz', Ct_congr (hO 3) (by omega) hfin, Qt_congr (hO 3) (Nat.le_refl 3),
      tl_congr A prm0 hh'] at this
    exact this
  · have h' := (busFinalsFail_congr hh' hfin).mpr h
    unfold BusFinalsFail at h'
    rw [hfin'] at h'
    exact h' hgt.2

end ZkFormal.Udr.Np
