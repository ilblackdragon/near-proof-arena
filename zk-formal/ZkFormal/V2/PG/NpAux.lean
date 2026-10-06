import ZkFormal.V2.PG.NpRows

/-!
# ZkFormal.V2.PG.NpAux (P2 copy of `Prover.NpAux` at `dp = pg g`) — the generated aux constraints on the honest aux columns

`myAux` is `Stark.auxConstraints` with its fold step and group step named
(`auxConstraints_eq : … = myAux …` by `rfl`).  On honest chain values every chain
constraint vanishes (`aStep_chain`) and the interaction factors are the honest `φ`s.
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- The fold step of `auxConstraints`. -/
def aStep (env : Env Fp8) (α γ : Fp8) (acc : List Fp8 × List (Interaction × Fp8) × List Fp8)
    (i : Interaction) : List Fp8 × List (Interaction × Fp8) × List Fp8 :=
  let (cs, phi, rest) := interactionAux env α γ i acc.2.2
  (acc.1 ++ cs, acc.2.1 ++ [(i, phi)], rest)

/-- The three constraints of one running-product group. -/
def aGroup (env : Env Fp8) (x : (List (Interaction × Fp8) × (Fp8 × Fp8)) × Fp8) : List Fp8 :=
  match x with
  | ((grp, (a, an)), fin) =>
    let Φ := (grp.map (·.2)).foldl (· * ·) 1
    [env.isFirst * (a - 1), env.isTransition * (an - a * Φ), env.isLast * (a * Φ - fin)]

def myAux (T : Air.Table) (g : Nat) (env : Env Fp8) (α γ : Fp8) (auxZ auxG fins : List Fp8) :
    List Fp8 :=
  let (cs, phis, rest) := T.interactions.foldl (aStep env α γ) ([], [], auxZ)
  let nChain := auxZ.length - rest.length
  let groups := (chunksOf (max g 1) (phis.filter (·.1.send))) ++
                (chunksOf (max g 1) (phis.filter (! ·.1.send)))
  let accs := (rest.zip (auxG.drop nChain))
  let gc := ((groups.zip accs).zip fins).flatMap (aGroup env)
  cs ++ gc

theorem auxConstraints_eq (T : Air.Table) (g : Nat) (env : Env Fp8) (α γ : Fp8)
    (auxZ auxG fins : List Fp8) :
    auxConstraints T g env α γ auxZ auxG fins = myAux T g env α γ auxZ auxG fins := rfl

/-! ## Zip/index helper -/

theorem mem_zip_map {α β γ : Type} {f : α × β → γ} {l : List α} {m : List β} {x : γ}
    (h : x ∈ (l.zip m).map f) : ∃ j, ∃ (h1 : j < l.length) (h2 : j < m.length), x = f (l[j], m[j]) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
  simp only [List.length_zip, Nat.lt_min] at hj
  exact ⟨j, hj.1, hj.2, by simp⟩

/-! ## Chains -/

theorem chainOf_length (env : Env Fp8) (α γ : Fp8) (i : Interaction) :
    (chainOf env α γ i).1.length = 2 * (i.mult.length - 1) := by
  unfold chainOf
  generalize hb : i.mult.map (·.evalWith env) = bits
  have hl : bits.length = i.mult.length := by rw [← hb, List.length_map]
  match bits, hl with
  | [], hl => simp at hl ⊢; omega
  | [_], hl => simp at hl ⊢; omega
  | b0 :: b1 :: bs, hl =>
    simp only [List.length_append, List.length_map, List.length_range, List.length_tail,
      List.length_scanl, List.length_zip, List.length_cons] at hl ⊢
    omega

theorem chainsOf_length (env : Env Fp8) (α γ : Fp8) (is : List Interaction) :
    (chainsOf env α γ is).length = (is.map fun i => 2 * (i.mult.length - 1)).sum := by
  unfold chainsOf
  rw [sum_flatMap_length]
  congr 1; apply List.map_congr_left; intro i _; exact chainOf_length env α γ i

theorem scanl_eq_cons_tail {α β : Type} (f : α → β → α) (b : α) (l : List β) :
    l.scanl f b = b :: (l.scanl f b).tail := by
  cases l <;> simp [List.scanl_cons]

/-- On honest chain values, one interaction's constraints vanish and its factor is `φ`. -/
theorem interactionAux_chain (env : Env Fp8) (α γ : Fp8) (i : Interaction) (R : List Fp8) :
    ∃ zs, (∀ x ∈ zs, x = 0) ∧
      interactionAux env α γ i ((chainOf env α γ i).1 ++ R) = (zs, (chainOf env α γ i).2, R) := by
  unfold interactionAux chainOf
  generalize γ - fingerprint env α i = p0
  generalize i.mult.map (·.evalWith env) = bits
  match bits with
  | [] => exact ⟨[], by simp, by simp⟩
  | [b] => exact ⟨[], by simp, by simp⟩
  | b0 :: b1 :: bs' =>
    simp only
    generalize hbs : b1 :: bs' = bs
    generalize hps : (List.range bs.length).map (fun j => p0 ^ (2 ^ (j + 1))) = ps
    generalize hS : ((bs.zip ps).map fun (b, pj) => 1 + b * (pj - 1)).scanl (· * ·)
      (1 + b0 * (p0 - 1)) = S
    have hpsl : ps.length = bs.length := by rw [← hps]; simp
    have hSl : S.length = bs.length + 1 := by rw [← hS]; simp [hpsl]
    have hpisl : S.tail.length = bs.length := by simp [hSl]
    have e1 : (ps ++ S.tail ++ R).take bs.length = ps := by
      rw [List.append_assoc, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have e2 : ((ps ++ S.tail ++ R).drop bs.length).take bs.length = S.tail := by
      rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have e3 : (ps ++ S.tail ++ R).drop (2 * bs.length) = R := by
      rw [show 2 * bs.length = ps.length + S.tail.length by omega, List.append_assoc, List.drop_append,
        List.drop_of_length_le (by omega), Nat.add_sub_cancel_left, List.nil_append, List.drop_left]
    simp only [e1, e2, e3]
    refine ⟨_, ?_, rfl⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨j, h1, h2, rfl⟩ := mem_zip_map hx
      have hj : ps[j] = p0 ^ (2 ^ (j + 1)) := by subst hps; simp
      have hj' : (p0 :: ps)[j] = p0 ^ (2 ^ j) := by
        cases j with
        | zero => simp [Semiring.pow_one]
        | succ j => simp only [List.getElem_cons_succ]; subst hps; simp
      simp only [hj, hj']
      rw [show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by rw [Nat.pow_succ]; omega, Semiring.pow_add]
      grind
    · obtain ⟨j, h1, h2, rfl⟩ := mem_zip_map hx
      simp only [List.length_zip, Nat.lt_min] at h1
      simp only [List.getElem_zip]
      have hS0 : S = (1 + b0 * (p0 - 1)) :: S.tail := by
        rw [← hS]; exact scanl_eq_cons_tail _ _ _
      have ha : S.tail[j] = S[j + 1] := by simp
      have hb : ((1 + b0 * (p0 - 1)) :: S.tail)[j] = S[j]'(by omega) := by
        simp only [← hS0]
      have hc := List.getElem_succ_scanl (f := (· * ·)) (b := 1 + b0 * (p0 - 1))
        (l := (bs.zip ps).map fun (b, pj) => 1 + b * (pj - 1)) (i := j) (by rw [hS]; omega)
      simp only [hS] at hc
      rw [ha, hb, hc]
      grind

theorem fold_chains (env : Env Fp8) (α γ : Fp8) : ∀ (is : List Interaction) (c : List Fp8)
    (p : List (Interaction × Fp8)) (R : List Fp8), (∀ x ∈ c, x = 0) →
    ∃ c', (∀ x ∈ c', x = 0) ∧
      is.foldl (aStep env α γ) (c, p, chainsOf env α γ is ++ R) = (c', p ++ phisOf env α γ is, R)
  | [], c, p, R, hc => ⟨c, hc, by simp [chainsOf, phisOf]⟩
  | i :: is, c, p, R, hc => by
    obtain ⟨zs, hz, he⟩ := interactionAux_chain env α γ i (chainsOf env α γ is ++ R)
    have hstep : aStep env α γ (c, p, chainsOf env α γ (i :: is) ++ R) i =
        (c ++ zs, p ++ [(i, (chainOf env α γ i).2)], chainsOf env α γ is ++ R) := by
      unfold aStep
      simp only [chainsOf, List.flatMap_cons, List.append_assoc] at he ⊢
      rw [he]
    rw [List.foldl_cons, hstep]
    obtain ⟨c', hc', he'⟩ := fold_chains env α γ is (c ++ zs) _ R (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact hc x h
      · exact hz x h)
    refine ⟨c', hc', ?_⟩
    rw [he']
    simp [phisOf, List.append_assoc]

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem auxRow_length (α γ : Fp8) (t r : Nat) :
    (auxRow A cb tr α γ t r).length = (tb A t).auxCount dp.auxGroup := by
  simp [auxRow, chainsOf_length, Table.auxCount, nG]; omega

theorem auxC_spec (α γ : Fp8) (t a : Nat) (hlog : tr.log t ≤ 27) :
    ∀ r, r < 2 ^ lg tr t → ev (2 ^ lg tr t) (auxC A cb tr α γ t a) (omg (lg tr t) ^ r) =
      (auxRow A cb tr α γ t r).getD a 0 := by
  unfold auxC
  exact pick_spec <| exists_interp (npDistinct_omg hlog) _

theorem auxV_row (α γ : Fp8) (t : Nat) (hlog : tr.log t ≤ 27) {r : Nat} (hr : r < 2 ^ lg tr t) :
    auxV A cb tr α γ t (omg (lg tr t) ^ r) = auxRow A cb tr α γ t r := by
  apply List.ext_getElem (by simp [auxV, auxRow_length])
  intro a h1 h2
  simp only [auxV, List.getElem_map, List.getElem_range]
  rw [auxC_spec A cb tr α γ t a hlog r hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

theorem accAt_zero (α γ : Fp8) (t j : Nat) : accAt A cb tr α γ t 0 j = 1 := rfl

theorem accAt_succ (α γ : Fp8) (t r j : Nat) :
    accAt A cb tr α γ t (r + 1) j =
      accAt A cb tr α γ t r j * phiG (rEnv A cb tr t r) α γ (tb A t).interactions j := by
  simp [accAt, List.range_succ, List.foldl_append]

theorem chunksOf_go_one {α : Type} : ∀ (n : Nat) (l : List α), l.length ≤ n →
    chunksOf.go 1 n l = l.map fun x => [x]
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, [], _ => rfl
  | n + 1, a :: l, h => by
    simp only [chunksOf.go, List.take, List.drop, List.map_cons]
    rw [chunksOf_go_one n l (by simpa using h)]

theorem chunksOf_one {α : Type} (l : List α) : chunksOf 1 l = l.map fun x => [x] :=
  chunksOf_go_one _ l (Nat.le_refl _)

theorem groupsOf_length (env : Env Fp8) (α γ : Fp8) (t : Nat) :
    (groupsOf env α γ (tb A t).interactions).length = nG A t := by
  have hg := AuxG.one_le
  unfold groupsOf nG phisOf
  rw [show dp.auxGroup = AuxG.g from rfl, Nat.max_eq_left hg, List.filter_map, List.filter_map,
    V2.G.chunksOf_map, V2.G.chunksOf_map, List.length_append, List.length_map, List.length_map,
    V2.G.chunksOf_length hg, V2.G.chunksOf_length hg]
  have e1 : ((fun x : Interaction × Fp8 => x.fst.send) ∘ fun i => (i, (chainOf env α γ i).snd)) =
      fun i => i.send == true := by funext i; simp
  have e2 : ((fun x : Interaction × Fp8 => !x.fst.send) ∘ fun i => (i, (chainOf env α γ i).snd)) =
      fun i => i.send == false := by funext i; simp
  rw [e1, e2]
  rfl

theorem gc_zero (α γ : Fp8) {t : Nat} (hlog : tr.log t ≤ 27) {r : Nat} (hr : r < 2 ^ lg tr t) :
    ∀ x ∈ (((groupsOf (rEnv A cb tr t r) α γ (tb A t).interactions).zip
        (((List.range (nG A t)).map (accAt A cb tr α γ t r)).zip
          ((List.range (nG A t)).map (accAt A cb tr α γ t ((r + 1) % 2 ^ lg tr t))))).zip
        (finsT A cb tr α γ t)).flatMap (aGroup (rEnv A cb tr t r)), x = 0 := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [List.length_zip, Nat.lt_min, List.length_map, List.length_range, finsT,
    groupsOf_length] at hj
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range, finsT] at hxy
  have hphi : (((groupsOf (rEnv A cb tr t r) α γ (tb A t).interactions)[j]'(by
      rw [groupsOf_length]; omega)).map (·.2)).foldl (· * ·) 1 =
      phiG (rEnv A cb tr t r) α γ (tb A t).interactions j := by
    unfold phiG
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [groupsOf_length]; omega)]
    rfl
  unfold aGroup at hxy
  simp only [hphi] at hxy
  have hF : (rEnv A cb tr t r).isFirst = if r = 0 then 1 else 0 := npSelSum_omg hlog hr
  have hL : (rEnv A cb tr t r).isLast = if r + 1 = 2 ^ lg tr t then 1 else 0 :=
    npSelSum_omg_next hlog hr
  have hT : (rEnv A cb tr t r).isTransition = if r + 1 = 2 ^ lg tr t then 0 else 1 := by
    show 1 - (rEnv A cb tr t r).isLast = _
    rw [hL]; split
    · show (1 : Fp8) - 1 = 0; grind
    · show (1 : Fp8) - 0 = 1; grind
  rw [hF, hL, hT] at hxy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxy
  rcases hxy with h | h | h <;> rw [h]
  · split
    · rename_i h0; subst h0; rw [accAt_zero]; grind
    · grind
  · split
    · grind
    · rename_i h1
      rw [Nat.mod_eq_of_lt (by omega), accAt_succ]; grind
  · split
    · rename_i h1
      rw [show 2 ^ lg tr t = r + 1 from h1.symm, accAt_succ]; grind
    · grind

/-- **Every constraint vanishes on the honest columns on the trace domain.** -/
theorem csX_row_zero (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ : Fp8)
    {r : Nat} (hr : r < 2 ^ lg tr t) : ∀ c ∈ csX A cb tr α γ t (omg (lg tr t) ^ r), c = 0 := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  intro c hc
  unfold csX at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact allConstraints_row A cb tr hH ht hr e he
  rw [auxConstraints_eq, auxV_row A cb tr α γ t hlog hr, omg_mul_pow tr t hlog,
    auxV_row A cb tr α γ t hlog (Nat.mod_lt _ (Nat.two_pow_pos _))] at hc
  rw [show pEnv A cb tr t (omg (lg tr t) ^ r) = rEnv A cb tr t r from rfl] at hc
  obtain ⟨c', hc', hf⟩ := fold_chains (rEnv A cb tr t r) α γ (tb A t).interactions [] []
    ((List.range (nG A t)).map (accAt A cb tr α γ t r)) (by simp)
  unfold myAux at hc
  unfold auxRow at hc
  rw [hf] at hc
  simp only [List.nil_append, List.length_append, List.length_map, List.length_range,
    Nat.add_sub_cancel] at hc
  rw [chainsOf_length, ← chainsOf_length (rEnv A cb tr t ((r + 1) % 2 ^ lg tr t)) α γ,
    List.drop_left] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hc' c hc
  · exact gc_zero A cb tr α γ hlog hr c hc

end

end ZkFormal.Prover.Np.G
