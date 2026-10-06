import ZkFormal.V2.G.Defs

/-!
# ZkFormal.V2.G.Groups — running products over groups of `g` interactions

The generalisation of v1's `AuxChain.auxC_sem` and `Msg4` (`table_fins`, `TabOk`,
`table_side`, `no_localFail`, `gp_tables`) from `auxGroup = 1` to `auxGroup = g ≥ 1`.

With groups `grpsOf g is` (the `chunksOf g` of the send interactions, then of the receive
interactions; exactly the verifier's `auxConstraints` grouping), vanishing running-product
constraints on the trace domain force the final of group `j` to be
`∏_{i ∈ group j} Φ_t(i)` (`table_fins`), where `Φ_t(i) = ∏_r φ_i(ω^r)`.  The groups of one
side partition that side (`chunksOf_flatten`), so the product of the send (receive) finals
is `∏_{i send} Φ_t(i)` (`table_side`), exactly as for `g = 1`.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

/-- Interaction groups of a table (verifier order): send groups, then receive groups. -/
def grpsOf (g : Nat) (is : List Interaction) : List (List Interaction) :=
  chunksOf g (is.filter (fun i => i.send)) ++ chunksOf g (is.filter (fun i => !i.send))

theorem prod_flatten_map {β : Type} (Φ : β → Fp8) : ∀ L : List (List β),
    (L.flatten.map Φ).prod = (L.map fun c => (c.map Φ).prod).prod
  | [] => rfl
  | c :: L => by
    rw [List.flatten_cons, List.map_append, prod_append', prod_flatten_map Φ L, List.map_cons,
      List.prod_cons]

theorem prod_chunks {β : Type} {g : Nat} (hg : 1 ≤ g) (Φ : β → Fp8) (l : List β) :
    ((chunksOf g l).map fun c => (c.map Φ).prod).prod = (l.map Φ).prod := by
  rw [← prod_flatten_map, chunksOf_flatten hg]

/-! ## One point: vanishing aux constraints -/

theorem auxC_semG {g : Nat} (hg : 1 ≤ g) (Tb : Air.Table) (env : Env Fp8) (α γ : Fp8)
    (auxZ auxG fins : List Fp8)
    (hb : ∀ i ∈ Tb.interactions, ∀ b ∈ i.mult, b.evalWith env = 0 ∨ b.evalWith env = 1)
    (hlen : nCons Tb.interactions ≤ auxZ.length)
    (hz : ∀ c ∈ auxConstraints Tb g env α γ auxZ auxG fins, c = 0)
    (j : Nat) (hj : j < (grpsOf g Tb.interactions).length)
    (hjZ : nCons Tb.interactions + j < auxZ.length) (hjG : nCons Tb.interactions + j < auxG.length)
    (hjF : j < fins.length) :
    let a := auxZ.getD (nCons Tb.interactions + j) 0
    let an := auxG.getD (nCons Tb.interactions + j) 0
    let Φ := (((grpsOf g Tb.interactions).getD j []).map (phiOf env α γ)).prod
    env.isFirst * (a - 1) = 0 ∧ env.isTransition * (an - a * Φ) = 0 ∧
      env.isLast * (a * Φ - fins.getD j 0) = 0 := by
  have e : auxConstraints Tb g env α γ auxZ auxG fins =
      (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).1 ++
      List.flatMap (fun y =>
          [env.isFirst * (y.1.2.fst - 1),
            env.isTransition *
              (y.1.2.snd - y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst)),
            env.isLast *
              (y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst) - y.snd)])
        ((((chunksOf (max g 1) (List.filter (fun x => x.fst.send)
            (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.1) ++
          chunksOf (max g 1) (List.filter (fun x => !x.fst.send)
            (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.1)).zip
          ((Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.2.zip
            (List.drop (auxZ.length - (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.2.length)
              auxG))).zip fins)) := by
    simp only [auxConstraints]; rfl
  rw [e] at hz
  have hF := fold_sem env α γ Tb.interactions ([], [], auxZ) hb hlen
    (fun c hc => hz c (List.mem_append_left _ hc))
  simp only [List.nil_append] at hF
  rw [hF.1, hF.2, Nat.max_eq_left hg, List.filter_map, List.filter_map, chunksOf_map, chunksOf_map,
    List.length_drop,
    show auxZ.length - (auxZ.length - nCons Tb.interactions) = nCons Tb.interactions by omega] at hz
  have hz2 := mem_flatMap3 (fun c hc => hz c (List.mem_append_right _ hc))
  have hgr : (chunksOf g (List.filter ((fun x : Interaction × Fp8 => x.fst.send) ∘
        fun i => (i, phiOf env α γ i)) Tb.interactions)).map (List.map fun i => (i, phiOf env α γ i)) ++
      (chunksOf g (List.filter ((fun x : Interaction × Fp8 => !x.fst.send) ∘
        fun i => (i, phiOf env α γ i)) Tb.interactions)).map (List.map fun i => (i, phiOf env α γ i)) =
      (grpsOf g Tb.interactions).map (List.map fun i => (i, phiOf env α γ i)) := by
    rw [grpsOf, List.map_append]; rfl
  rw [hgr] at hz2
  have hjL : j < ((((grpsOf g Tb.interactions).map (List.map fun i => (i, phiOf env α γ i))).zip
      ((auxZ.drop (nCons Tb.interactions)).zip (auxG.drop (nCons Tb.interactions)))).zip fins).length := by
    simp only [List.length_zip, List.length_map, List.length_drop]; omega
  have := hz2 _ (List.getElem_mem hjL)
  simp only [List.getElem_zip, List.getElem_map, List.getElem_drop, List.map_map] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjZ, List.getElem?_eq_getElem hjG,
    List.getElem?_eq_getElem hjF, List.getElem?_eq_getElem hj, Option.getD_some]
  obtain ⟨h1, h2, h3⟩ := this
  have hΦ : List.foldl (fun x1 x2 => x1 * x2) 1
      (List.map ((fun x : Interaction × Fp8 => x.snd) ∘ fun i => (i, phiOf env α γ i))
        (grpsOf g Tb.interactions)[j]) = ((grpsOf g Tb.interactions)[j].map (phiOf env α γ)).prod := by
    rw [foldl_mul_prod]; have e1 : ∀ x : Fp8, 1 * x = x := fun x => by grind
    rw [e1]; rfl
  rw [hΦ] at h2 h3
  exact ⟨h1, h2, h3⟩

/-! ## Per-table facts -/

section
variable (A : Air) (g : Nat)

/-- The per-table factor product `Φ_t(i) = ∏_r φ_i(ω^r)` (at `pg g`). -/
noncomputable def PhiT (τ : PTn) (α γ : Fp8) (t : Nat) (i : Interaction) : Fp8 :=
  ((List.range (2 ^ (tl A (pg g) τ t).log)).map fun r =>
    phiOf (polyEnv A (pg g) τ t (omg (tl A (pg g) τ t).log ^ r)) α γ i).prod

theorem table_fins {g : Nat} (hg : 1 ≤ g) (τ : PTn) (t : Nat) (αfp γ : Fp8)
    (hlog : (tl A (pg g) τ t).log ≤ 27)
    (haux : (tl A (pg g) τ t).aux = nCons (tableOf A t).interactions +
      (grpsOf g (tableOf A t).interactions).length)
    (hfins : (finsOf A (pg g) τ t).length = (grpsOf g (tableOf A t).interactions).length)
    (hz : ∀ r, r < 2 ^ (tl A (pg g) τ t).log →
      ∀ c ∈ csAt A (pg g) τ t αfp γ (omg (tl A (pg g) τ t).log ^ r), c = 0)
    (j : Nat) (hj : j < (grpsOf g (tableOf A t).interactions).length) :
    (finsOf A (pg g) τ t).getD j 0 =
      (((grpsOf g (tableOf A t).interactions).getD j []).map (PhiT A g τ αfp γ t)).prod := by
  let log := (tl A (pg g) τ t).log
  let ω := omg log
  let cj := nCons (tableOf A t).interactions + j
  have hsem : ∀ r, r < 2 ^ log → _ := fun r hr => by
    have hzr := hz r hr
    unfold csAt at hzr
    have hall : ∀ e ∈ (tableOf A t).allConstraints, e.evalWith (polyEnv A (pg g) τ t (ω ^ r)) = 0 :=
      fun e he => hzr _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    have hb := bits_bool_of (polyEnv A (pg g) τ t (ω ^ r)) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) _ hall
    exact auxC_semG hg (tableOf A t) (polyEnv A (pg g) τ t (ω ^ r)) αfp γ
      ((List.range (tl A (pg g) τ t).aux).map fun a => colAt A (pg g) τ ⟨t, 1, a⟩ (ω ^ r))
      ((List.range (tl A (pg g) τ t).aux).map fun a => colAt A (pg g) τ ⟨t, 1, a⟩ (ω * ω ^ r))
      (finsOf A (pg g) τ t) hb (by simp; omega) (fun c hc => hzr c (List.mem_append_right _ hc)) j hj
      (by simp; omega) (by simp; omega) (by omega)
  have hgetZ : ∀ x, ((List.range (tl A (pg g) τ t).aux).map fun a => colAt A (pg g) τ ⟨t, 1, a⟩ x).getD cj 0 =
      colAt A (pg g) τ ⟨t, 1, cj⟩ x := fun x => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  have hrun := running_prod (2 ^ log) (Nat.two_pow_pos _)
    (fun r => colAt A (pg g) τ ⟨t, 1, cj⟩ (ω ^ r)) (fun r => colAt A (pg g) τ ⟨t, 1, cj⟩ (ω * ω ^ r))
    (fun r => (((grpsOf g (tableOf A t).interactions).getD j []).map
      (phiOf (polyEnv A (pg g) τ t (ω ^ r)) αfp γ)).prod)
    (fun r => (polyEnv A (pg g) τ t (ω ^ r)).isFirst) (fun r => (polyEnv A (pg g) τ t (ω ^ r)).isTransition)
    (fun r => (polyEnv A (pg g) τ t (ω ^ r)).isLast) ((finsOf A (pg g) τ t).getD j 0)
    (fun r hr => selSum_omg hlog hr)
    (fun r hr => by
      show 1 - selSum (2 ^ log) (ω * ω ^ r) = _
      rw [selSum_omg_next hlog hr]; split <;> grind)
    (fun r hr => selSum_omg_next hlog hr)
    (fun r _ => by show colAt A (pg g) τ ⟨t, 1, cj⟩ (ω * ω ^ r) = colAt A (pg g) τ ⟨t, 1, cj⟩ (ω ^ (r + 1))
                   rw [Semiring.pow_succ]; congr 1; grind)
    (fun r hr => by have := (hsem r hr).1; rw [hgetZ] at this; exact this)
    (fun r hr => by have := (hsem r hr).2.1; rw [hgetZ, hgetZ] at this; exact this)
    (fun r hr => by have := (hsem r hr).2.2; rw [hgetZ] at this; exact this)
  rw [hrun]
  unfold PhiT
  exact prod_swap _ _ _

end

theorem table_side {g : Nat} (hg : 1 ≤ g) (is : List Interaction) (fins : List Fp8) (Φ : Interaction → Fp8)
    (hlen : fins.length = (grpsOf g is).length)
    (hj : ∀ j, j < (grpsOf g is).length → fins.getD j 0 = (((grpsOf g is).getD j []).map Φ).prod) :
    (fins.take (chunksOf g (is.filter (fun i => i.send))).length).prod =
        ((is.filter (fun i => i.send)).map Φ).prod ∧
    (fins.drop (chunksOf g (is.filter (fun i => i.send))).length).prod =
        ((is.filter (fun i => !i.send)).map Φ).prod := by
  have hf : fins = (grpsOf g is).map fun c => (c.map Φ).prod := by
    refine List.ext_getElem (by rw [List.length_map]; exact hlen) fun j h1 h2 => ?_
    have := hj j (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
    rw [this, List.getElem_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_map] at h2; exact h2), Option.getD_some]
  rw [hf]
  unfold grpsOf
  rw [List.map_append, List.take_left' (List.length_map _), List.drop_left' (List.length_map _)]
  exact ⟨prod_chunks hg Φ _, prod_chunks hg Φ _⟩

/-! ## Per-table facts of a shaped transcript -/

section
variable {A : Air} {g : Nat}

structure TabOk (A : Air) (g : Nat) (τ : PTn) (t : Nat) : Prop where
  hdl : (hdrOf τ).getD t 0 = (tl A (pg g) τ t).log
  hlog : (tl A (pg g) τ t).log ≤ 27
  hbase : ∀ (c j : Nat), (colAt A (pg g) τ ⟨t, 0, c⟩ (omg (tl A (pg g) τ t).log ^ j)).IsBase
  haux : (tl A (pg g) τ t).aux = nCons (tableOf A t).interactions + (grpsOf g (tableOf A t).interactions).length
  hsend : (tl A (pg g) τ t).sendG = (chunksOf g ((tableOf A t).interactions.filter (fun i => i.send))).length
  hn : (tl A (pg g) τ t).sendG + (tl A (pg g) τ t).recvG = (grpsOf g (tableOf A t).interactions).length

theorem tabOk_of (hg : 1 ≤ g) {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A (pg g) l = true) (t : Nat) (ht : t < A.tables.length) : TabOk A g τ t := by
  obtain ⟨hlen, hlog, hwf, _⟩ := headerOk_facts hh
  have htl := tl_eq (prm := pg g) hl hlen t ht
  have hlt := hlog t ht (by omega)
  have hmx := (table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).2.1
  have hT := tableOf_lt ht
  have hgl : ∀ is : List Interaction, (grpsOf g is).length =
      numGroups (is.filter (fun i => i.send == true)).length g +
        numGroups (is.filter (fun i => i.send == false)).length g := fun is => by
    rw [grpsOf, List.length_append, chunksOf_length hg, chunksOf_length hg, filter_send_eq, filter_recv_eq]
  refine ⟨?_, ?_, fun c j => ?_, ?_, ?_, ?_⟩
  · rw [htl]; unfold hdrOf; rw [hl]
    simp only [Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < l.length by omega)]
  · rw [htl]; show l[t] ≤ 27; omega
  · have e : omg (tl A (pg g) τ t).log ^ j = Fp8.ofBase (Fp.twoAdicGen (tl A (pg g) τ t).log ^ j) := by
      unfold omg; rw [ofBase_pow]
    rw [e]
    refine colAt_base τ ⟨t, 0, c⟩ rfl (by rw [htl]) rfl ?_ _
    rw [htl]; show l[t] + 4 ≤ 27
    have := hlt.2.2; simp [pg, Params.default] at this; omega
  · rw [htl, hT, hgl]
    show (A.tables[t]).auxCount g = _
    unfold Air.Table.auxCount nCons Air.Table.numSide
    omega
  · rw [htl, hT, chunksOf_length hg, filter_send_eq]; rfl
  · rw [htl, hT, hgl]; rfl

theorem finsOf_length (hg : 1 ≤ g) {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A (pg g) l = true)
    (hfl : (finalsOf τ).length = ((layOf A (pg g) τ).map fun L => L.sendG + L.recvG).sum)
    (t : Nat) (ht : t < A.tables.length) :
    (finsOf A (pg g) τ t).length = (grpsOf g (tableOf A t).interactions).length := by
  obtain ⟨hlen, _, _, _⟩ := headerOk_facts hh
  have hlay : (layOf A (pg g) τ).length = A.tables.length := by
    unfold layOf hdrOf; rw [hl]; simp [layout, hlen]
  have := sum_take_le (fun L => L.sendG + L.recvG) (layOf A (pg g) τ) t (by omega)
  unfold finsOf
  rw [List.length_take, List.length_drop, ← (tabOk_of hg hl hh t ht).hn]
  unfold tl at *
  omega

theorem no_localFail (hg : 1 ≤ g) {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A (pg g) l = true) (α γ : Fp8)
    (hz : ∀ t, t < A.tables.length → ∀ r, r < 2 ^ (tl A (pg g) τ t).log →
      ∀ c ∈ csAt A (pg g) τ t α γ (omg (tl A (pg g) τ t).log ^ r), c = 0) :
    ¬ LocalFail A (pg g) τ := by
  rintro ⟨t, ht, r, hr, e, he, hne⟩
  have tab := tabOk_of hg hl hh t ht
  have hr' : r < 2 ^ (tl A (pg g) τ t).log := by
    have : (decTrace A (pg g) τ).height t = 2 ^ (hdrOf τ).getD t 0 := rfl
    rw [this, tab.hdl] at hr; exact hr
  have h1 := evalWith_hom A (pg g) τ t tab.hdl tab.hlog tab.hbase r hr' e
  have h2 := hz t ht r hr' _ (by unfold csAt; exact List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
  rw [h1] at h2
  exact hne (Fp8.ofBase_inj (h2.trans rfl))

theorem phiOf_eqG (τ : PTn) (t : Nat)
    (hdl : (hdrOf τ).getD t 0 = (tl A (pg g) τ t).log) (hlog : (tl A (pg g) τ t).log ≤ 27)
    (hbase : ∀ (c j : Nat), (colAt A (pg g) τ ⟨t, 0, c⟩ (omg (tl A (pg g) τ t).log ^ j)).IsBase)
    (r : Nat) (hr : r < 2 ^ (tl A (pg g) τ t).log) (α γ : Fp8) (i : Interaction) :
    phiOf (polyEnv A (pg g) τ t (omg (tl A (pg g) τ t).log ^ r)) α γ i =
      (γ - fpL α ((i.msgVal (decTrace A (pg g) τ) t r (pubOf Fp τ.cb)).map Fp8.ofBase ++
        [((i.bus + 1 : Nat) : Fp8)])) ^ i.multNat (decTrace A (pg g) τ) t r (pubOf Fp τ.cb) := by
  have hh := evalWith_hom A (pg g) τ t hdl hlog hbase r hr
  unfold phiOf
  rw [fingerprint_eq]
  have e1 : i.msg.map (·.evalWith (polyEnv A (pg g) τ t (omg (tl A (pg g) τ t).log ^ r))) =
      (i.msgVal (decTrace A (pg g) τ) t r (pubOf Fp τ.cb)).map Fp8.ofBase := by
    unfold Interaction.msgVal; rw [List.map_map]
    exact List.map_congr_left fun e _ => hh e
  rw [e1]
  congr 1
  unfold Interaction.multNat
  rw [multNat_go_bval _ t r _ (fun b => b.evalWith (polyEnv A (pg g) τ t
    (omg (tl A (pg g) τ t).log ^ r))) (fun b => by
      rw [hh b]; exact ⟨fun h => Fp8.ofBase_inj h, fun h => by rw [h]; rfl⟩) i.mult 0]
  simp

theorem gp_tables (hg : 1 ≤ g) {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A (pg g) l = true) (α γ : Fp8) (s : Bool) :
    ((expand (busMsgs A (pg g) τ s)).map fun m => γ - fpL α m).prod =
      ((List.range A.tables.length).map fun t =>
        (((tableOf A t).interactions.filter (fun i => i.send == s)).map (PhiT A g τ α γ t)).prod).prod := by
  rw [gp_side]
  congr 1
  apply List.map_congr_left
  intro t ht
  have tab := tabOk_of hg hl hh t (List.mem_range.mp ht)
  have hh' : (decTrace A (pg g) τ).height t = 2 ^ (tl A (pg g) τ t).log := by
    show 2 ^ (hdrOf τ).getD t 0 = _; rw [tab.hdl]
  rw [hh']
  unfold PhiT
  rw [prod_swap]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  apply List.map_congr_left
  intro r hr
  exact (phiOf_eqG τ t tab.hdl tab.hlog tab.hbase r (List.mem_range.mp hr) α γ i).symm

/-- Per table, under vanishing constraints: the send (receive) finals multiply to the
send (receive) factor products. -/
theorem table_sides (hg : 1 ≤ g) {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk A (pg g) l = true)
    (hfl : (finalsOf τ).length = ((layOf A (pg g) τ).map fun L => L.sendG + L.recvG).sum)
    (α γ : Fp8)
    (hz : ∀ t, t < A.tables.length → ∀ r, r < 2 ^ (tl A (pg g) τ t).log →
      ∀ c ∈ csAt A (pg g) τ t α γ (omg (tl A (pg g) τ t).log ^ r), c = 0)
    (t : Nat) (ht : t < A.tables.length) :
    ((finsOf A (pg g) τ t).take (tl A (pg g) τ t).sendG).prod =
      (((tableOf A t).interactions.filter (fun i => i.send == true)).map (PhiT A g τ α γ t)).prod ∧
    ((finsOf A (pg g) τ t).drop (tl A (pg g) τ t).sendG).prod =
      (((tableOf A t).interactions.filter (fun i => i.send == false)).map (PhiT A g τ α γ t)).prod := by
  have tab := tabOk_of hg hl hh t ht
  have := table_side hg (tableOf A t).interactions (finsOf A (pg g) τ t) (PhiT A g τ α γ t)
    (finsOf_length hg hl hh hfl t ht) (fun j hj => table_fins A hg τ t α γ tab.hlog tab.haux
      (finsOf_length hg hl hh hfl t ht) (hz t ht) j hj)
  rw [tab.hsend, ← filter_send_eq, ← filter_recv_eq]
  exact this

end

end ZkFormal.V2.G
