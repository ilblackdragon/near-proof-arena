import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Extract.WalkProof — `WalkViewStmt`

Same method as `SortProof`: row facts from the constraints, segment
decomposition (`ws … we`), the view (one `WalkV` per segment) and its exact
traffic.
-/

namespace ZkFormal.Near.WalkProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.WalkTab

variable {tr : Trace Fp} {pub : List Fp}

theorem con (hL : TableLocal WalkTab.table tr T_WALK pub) {r : Nat} (hr : r < tr.height T_WALK)
    {e : Expr} (he : e ∈ WalkTab.constraints) : e.eval tr T_WALK r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height T_WALK) : (r + 1) % tr.height T_WALK = r + 1 :=
  Nat.mod_eq_of_lt h

variable (hL : TableLocal WalkTab.table tr T_WALK pub)
include hL

theorem isBool {r : Nat} (hr : r < tr.height T_WALK) {x : Nat} (hx : x ∈ [act, ws, we, gK]) :
    tr.cell T_WALK r x = 0 ∨ tr.cell T_WALK r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold WalkTab.constraints
    exact List.mem_append_left _ (List.mem_map_of_mem hx))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem rowFacts {r : Nat} (hr : r < tr.height T_WALK) :
    tr.cell T_WALK r gK = tr.cell T_WALK r act - tr.cell T_WALK r ws ∧
    (tr.cell T_WALK r ws = 1 → tr.cell T_WALK r act = 1 ∧ tr.cell T_WALK r we = 0 ∧
      tr.cell T_WALK r nN = 0 ∧ tr.cell T_WALK r nI = 0 ∧ tr.cell T_WALK r sym = (SYM_START : Nat) ∧
      tr.cell T_WALK r t = 0) ∧
    (tr.cell T_WALK r we = 1 → tr.cell T_WALK r act = 1) := by
  have h0 := con hL hr (e := sub (c gK) (sub (c act) (c ws))) (by simp [WalkTab.constraints])
  have h1 := con hL hr (e := .mul (c ws) (Dsl.not (c act))) (by simp [WalkTab.constraints])
  have h2 := con hL hr (e := .mul (c we) (Dsl.not (c act))) (by simp [WalkTab.constraints])
  have h3 := con hL hr (e := .mul (c ws) (c we)) (by simp [WalkTab.constraints])
  have h4 := con hL hr (e := .mul (c ws) (c nN)) (by simp [WalkTab.constraints])
  have h5 := con hL hr (e := .mul (c ws) (c nI)) (by simp [WalkTab.constraints])
  have h6 := con hL hr (e := .mul (c ws) (sub (c sym) (k SYM_START))) (by simp [WalkTab.constraints])
  have h7 := con hL hr (e := .mul (c ws) (c t)) (by simp [WalkTab.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k] at h0 h1 h2 h3 h4 h5 h6 h7
  refine ⟨by grind, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3 h4 h5 h6 h7
    refine ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at h2; grind

theorem within {r : Nat} (hr : r + 1 < tr.height T_WALK)
    (ha : tr.cell T_WALK r act = 1) (hl : tr.cell T_WALK r we = 0) :
    tr.cell T_WALK (r + 1) act = 1 ∧ tr.cell T_WALK (r + 1) ws = 0 ∧
    tr.cell T_WALK (r + 1) WalkTab.r = tr.cell T_WALK r WalkTab.r ∧
    tr.cell T_WALK (r + 1) nN = tr.cell T_WALK r nN2 ∧ tr.cell T_WALK (r + 1) nI = tr.cell T_WALK r nI2 ∧
    tr.cell T_WALK (r + 1) t = tr.cell T_WALK r t + tr.cell T_WALK r gK := by
  have hr' : r < tr.height T_WALK := by omega
  have h1 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (Dsl.not (n act))) (by simp [WalkTab.constraints])
  have h2 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (n ws)) (by simp [WalkTab.constraints])
  have h3 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n WalkTab.r) (c WalkTab.r)))
    (by simp [WalkTab.constraints])
  have h4 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n nN) (c nN2))) (by simp [WalkTab.constraints])
  have h5 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n nI) (c nI2))) (by simp [WalkTab.constraints])
  have h6 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n t) (.add (c t) (c gK))))
    (by simp [WalkTab.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, nxt hr] at h1 h2 h3 h4 h5 h6
  rw [ha, hl] at h1 h2 h3 h4 h5 h6
  refine ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height T_WALK) (hl : tr.cell T_WALK r we = 1)
    (ha : tr.cell T_WALK (r + 1) act = 1) : tr.cell T_WALK (r + 1) ws = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c we) (n act) (Dsl.not (n ws))) (by simp [WalkTab.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height T_WALK) (ha : tr.cell T_WALK r act = 0) :
    tr.cell T_WALK (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (by simp [WalkTab.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height T_WALK by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height T_WALK) : tr.cell T_WALK 0 ws = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c ws))) (by simp [WalkTab.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1
  grind

theorem lastRow (h0 : 0 < tr.height T_WALK) (ha : tr.cell T_WALK (tr.height T_WALK - 1) act = 1) :
    tr.cell T_WALK (tr.height T_WALK - 1) we = 1 := by
  have h1 := con hL (by omega : tr.height T_WALK - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c we)))) (by simp [WalkTab.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height T_WALK - 1 + 1 = tr.height T_WALK by omega)] at h1
  rw [ha] at h1; grind

end ZkFormal.Near.WalkProof

namespace ZkFormal.Near.WalkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.WalkTab

variable {tr : Trace Fp} {pub : List Fp}

def isOne (tr : Trace Fp) (x : Nat) (r : Nat) : Bool := decide (tr.cell T_WALK r x = 1)

theorem zero_of_not_one (hL : TableLocal WalkTab.table tr T_WALK pub) {r : Nat}
    (hr : r < tr.height T_WALK) {x : Nat} (hx : x ∈ [act, ws, we, gK]) (h : isOne tr x r = false) :
    tr.cell T_WALK r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem segFacts (hL : TableLocal WalkTab.table tr T_WALK pub) :
    SegFacts (tr.height T_WALK) (isOne tr act) (isOne tr ws) (isOne tr we) where
  first_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.1 h).1
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact (rowFacts hL hr).2.2 h
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) (by simp) hl)
    simp [isOne, this.1, this.2.1]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact nextSeg hL hr hl ha
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) (by simp) ha)
    simp [isOne, this]
  start h0 := by simp [isOne, row0 hL h0]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem height_le (hL : TableLocal WalkTab.table tr T_WALK pub) : tr.height T_WALK ≤ 2 ^ 16 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_pos : 0 < tr.height T_WALK := by unfold Trace.height; exact Nat.two_pow_pos _

/-- Facts about one walk segment. -/
theorem segInfo (hL : TableLocal WalkTab.table tr T_WALK pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr ws) (isOne tr we) s ℓ) (hH : s + ℓ ≤ tr.height T_WALK) :
    2 ≤ ℓ ∧
    (∀ j, j < ℓ → tr.cell T_WALK (s + j) act = 1 ∧ tr.cell T_WALK (s + j) WalkTab.r = tr.cell T_WALK s WalkTab.r ∧
      tr.cell T_WALK (s + j) we = (if j + 1 = ℓ then 1 else 0) ∧
      tr.cell T_WALK (s + j) gK = (if j = 0 then 0 else 1) ∧
      (0 < j → tr.cell T_WALK (s + j) t = ((j - 1 : Nat) : Fp))) ∧
    tr.cell T_WALK s nN = 0 ∧ tr.cell T_WALK s nI = 0 ∧ tr.cell T_WALK s sym = (SYM_START : Nat) ∧
    (∀ j, j + 1 < ℓ → tr.cell T_WALK (s + j + 1) nN = tr.cell T_WALK (s + j) nN2 ∧
      tr.cell T_WALK (s + j + 1) nI = tr.cell T_WALK (s + j) nI2) := by
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have hws : tr.cell T_WALK s ws = 1 := by simpa [isOne] using hfs
  have hs := (rowFacts hL (by omega : s < _)).2.1 hws
  have hℓ : 2 ≤ ℓ := by
    rcases Nat.lt_or_ge ℓ 2 with h | h
    · have : ℓ = 1 := by omega
      subst this
      have := hs.2.1; simp [isOne, show s + 1 - 1 = s by omega, this] at hle
    · exact h
  have hA : ∀ j, j < ℓ → tr.cell T_WALK (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell T_WALK (s + j) we = 0 := fun j hj =>
    zero_of_not_one hL (by omega) (by simp) (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hWS : ∀ j, 0 < j → j < ℓ → tr.cell T_WALK (s + j) ws = 0 := fun j h0 hj => by
    have := (hw (j - 1) (by omega)).2.1; rwa [show s + (j - 1) + 1 = s + j by omega] at this
  have hG : ∀ j, j < ℓ → tr.cell T_WALK (s + j) gK = (if j = 0 then 0 else 1) := fun j hj => by
    rw [(rowFacts hL (by omega : s + j < _)).1, hA j hj]
    by_cases h0 : j = 0
    · subst h0; simp only [Nat.add_zero, if_pos rfl]; rw [hws]; grind
    · rw [hWS j (by omega) hj, if_neg h0]; grind
  have hrr := const_of (f := fun q => tr.cell T_WALK q WalkTab.r) (s := s) (ℓ := ℓ) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have ht := counter_of (f := fun q => tr.cell T_WALK q t) (s := s + 1) (ℓ := ℓ - 1) (v0 := 0)
    (by
      have := (hw 0 (by omega)).2.2.2.2.2
      rw [show s + 0 + 1 = s + 1 by omega, show s + 0 = s by omega, hs.2.2.2.2.2] at this
      rw [this, show s = s + 0 by omega, hG 0 (by omega)]; simp; rfl)
    (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2.2.2
      rw [show s + (q - s) + 1 = q + 1 by omega, show s + (q - s) = q by omega] at this
      rw [this, show q = s + (q - s) by omega, hG (q - s) (by omega), if_neg (by omega)])
  refine ⟨hℓ, fun j hj => ⟨hA j hj, hrr (s + j) (by omega) (by omega), ?_, hG j hj, fun h0 => ?_⟩,
    hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, fun j hj => ⟨(hw j hj).2.2.2.1, (hw j hj).2.2.2.2.1⟩⟩
  · by_cases hl : j + 1 = ℓ
    · rw [if_pos hl]
      have := hle; rw [show s + ℓ - 1 = s + j by omega] at this; simpa [isOne] using this
    · rw [if_neg hl]; exact hW j (by omega)
  · have := ht (s + j) (by omega) (by omega)
    rw [this]; congr 2; omega

end ZkFormal.Near.WalkProof

namespace ZkFormal.Near.WalkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.WalkTab

variable {tr : Trace Fp} {pub : List Fp}

def edgeAt (tr : Trace Fp) (q : Nat) : Msg :=
  [nN, nI, sym, nN2, nI2].map fun x => (tr.cell T_WALK q x).toNat

def walksOf (tr : Trace Fp) (segs : List (Nat × Nat)) : List WalkV :=
  segs.map fun p => ⟨(tr.cell T_WALK p.1 WalkTab.r).toNat,
    (List.range p.2).map fun j => (edgeAt tr (p.1 + j), (tr.cell T_WALK (p.1 + j) u).toNat)⟩

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr T_WALK q pub [c x] 0 = if tr.cell T_WALK q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell T_WALK q x = 1 <;> simp [h]

def cellsE (tr : Trace Fp) (q : Nat) (uu : Fp) : List Fp :=
  [tr.cell T_WALK q nN, tr.cell T_WALK q nI, tr.cell T_WALK q sym, tr.cell T_WALK q nN2,
   tr.cell T_WALK q nI2, uu]

theorem rowT (q : Nat) (b : Nat) (sd : Bool) :
    rowTraffic WalkTab.interactions tr T_WALK q pub b sd =
      (if b = B_KEYNIB ∧ sd = false ∧ tr.cell T_WALK q gK = 1 then
        [[tr.cell T_WALK q WalkTab.r, tr.cell T_WALK q t, tr.cell T_WALK q sym, tr.cell T_WALK q we]] else []) ++
      (if b = B_EDGE ∧ sd = false ∧ tr.cell T_WALK q act = 1 then [cellsE tr q (tr.cell T_WALK q u)] else []) ++
      (if b = B_EDGE ∧ sd = true ∧ tr.cell T_WALK q act = 1 then [cellsE tr q (tr.cell T_WALK q u + 1)]
        else []) ++
      (if b = B_FINAL ∧ sd = true ∧ tr.cell T_WALK q we = 1 then
        [[tr.cell T_WALK q WalkTab.r, tr.cell T_WALK q nN2]] else []) := by
  simp only [rowTraffic, WalkTab.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, WalkTab.edge, List.map_cons,
    List.map_nil, eval_c, eval_add, eval_k, cellsE, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ ?_)) <;> (split <;> split <;> simp_all [eq_comm]) <;> grind

end ZkFormal.Near.WalkProof

namespace ZkFormal.Near.WalkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.WalkTab

variable {tr : Trace Fp} {pub : List Fp}

theorem natCast_toNat (a : Fp) : ((a.toNat : Nat) : Fp) = a := Fp.ofNat_toNat a

theorem ite01 (p : Prop) [Decidable p] : (Fp.ofNat (if p then 1 else 0)) = (if p then 1 else 0 : Fp) := by
  split <;> rfl

theorem walkSends_flat (ws : List WalkV) (b : Nat) :
    walkSends ws b = ws.flatMap fun w => walkSends [w] b := by
  unfold walkSends; split
  · simp
  · split
    · simp [map_eq_flatMap]
    · simp

theorem walkRecvs_flat (ws : List WalkV) (b : Nat) :
    walkRecvs ws b = ws.flatMap fun w => walkRecvs [w] b := by
  unfold walkRecvs; split
  · simp
  · split <;> simp

def walkOfSeg (tr : Trace Fp) (p : Nat × Nat) : WalkV :=
  ⟨(tr.cell T_WALK p.1 WalkTab.r).toNat,
    (List.range p.2).map fun j => (edgeAt tr (p.1 + j), (tr.cell T_WALK (p.1 + j) u).toNat)⟩

theorem cellsE_eq (q : Nat) (uu : Nat) :
    Msg.toFp (edgeAt tr q ++ [uu]) = cellsE tr q (Fp.ofNat uu) := by
  simp [Msg.toFp, edgeAt, cellsE, Fp.ofNat_toNat]

theorem rowT_key (q : Nat) : rowTraffic WalkTab.interactions tr T_WALK q pub B_KEYNIB false =
    if tr.cell T_WALK q gK = 1 then
      [[tr.cell T_WALK q WalkTab.r, tr.cell T_WALK q t, tr.cell T_WALK q sym, tr.cell T_WALK q we]] else [] := by
  rw [rowT]; simp [B_KEYNIB, B_EDGE, B_FINAL]

theorem rowT_edgeR (q : Nat) : rowTraffic WalkTab.interactions tr T_WALK q pub B_EDGE false =
    if tr.cell T_WALK q act = 1 then [cellsE tr q (tr.cell T_WALK q u)] else [] := by
  rw [rowT]; simp [B_KEYNIB, B_EDGE, B_FINAL]

theorem rowT_edgeS (q : Nat) : rowTraffic WalkTab.interactions tr T_WALK q pub B_EDGE true =
    if tr.cell T_WALK q act = 1 then [cellsE tr q (tr.cell T_WALK q u + 1)] else [] := by
  rw [rowT]; simp [B_KEYNIB, B_EDGE, B_FINAL]

theorem rowT_final (q : Nat) : rowTraffic WalkTab.interactions tr T_WALK q pub B_FINAL true =
    if tr.cell T_WALK q we = 1 then [[tr.cell T_WALK q WalkTab.r, tr.cell T_WALK q nN2]] else [] := by
  rw [rowT]; simp [B_KEYNIB, B_EDGE, B_FINAL]

theorem rowT_recv_other (q b : Nat) (h1 : b ≠ B_EDGE) (h2 : b ≠ B_KEYNIB) :
    rowTraffic WalkTab.interactions tr T_WALK q pub b false = [] := by
  rw [rowT]; simp [h1, h2]

theorem rowT_send_other (q b : Nat) (h1 : b ≠ B_EDGE) (h2 : b ≠ B_FINAL) :
    rowTraffic WalkTab.interactions tr T_WALK q pub b true = [] := by
  rw [rowT]; simp [h1, h2]

theorem segRecv (hL : TableLocal WalkTab.table tr T_WALK pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr ws) (isOne tr we) s ℓ) (hH : s + ℓ ≤ tr.height T_WALK)
    (b : Nat) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic WalkTab.interactions tr T_WALK q pub b false) =
      (walkRecvs [walkOfSeg tr (s, ℓ)] b).map Msg.toFp := by
  obtain ⟨h2, hrow, -, -, -, -⟩ := segInfo hL hseg hH
  by_cases hE : b = B_EDGE
  · subst hE
    simp only [rowT_edgeR, walkRecvs, ite_true, walkOfSeg, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_map]
    rw [flatMap_range'_single _ (fun j => cellsE tr (s + j) (tr.cell T_WALK (s + j) u)) s ℓ (fun j hj => by
      simp [(hrow j hj).1])]
    apply List.map_congr_left; intro j _
    simp [cellsE_eq, Fp.ofNat_toNat]
  · by_cases hK : b = B_KEYNIB
    · subst hK
      simp only [rowT_key, walkRecvs, if_neg (by decide : ¬ B_KEYNIB = B_EDGE), ite_true, walkOfSeg,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map, List.length_range]
      have hs : List.range' s ℓ = [s] ++ List.range' (s + 1) (ℓ - 1) := by
        rw [show ℓ = 1 + (ℓ - 1) by omega, ← List.range'_append_1]; simp
      rw [hs, List.flatMap_append]
      have h0 := hrow 0 (by omega)
      rw [Nat.add_zero] at h0
      rw [List.flatMap_singleton, h0.2.2.2.1, if_pos rfl, if_neg fp_zero_ne_one, List.nil_append]
      rw [flatMap_range'_single _ (fun j => [tr.cell T_WALK (s + 1 + j) WalkTab.r, tr.cell T_WALK (s + 1 + j) t,
        tr.cell T_WALK (s + 1 + j) sym, tr.cell T_WALK (s + 1 + j) we]) (s + 1) (ℓ - 1) (fun j hj => by
          have := hrow (j + 1) (by have := h2; omega)
          rw [show s + (j + 1) = s + 1 + j by omega] at this
          rw [this.2.2.2.1, if_neg (Nat.succ_ne_zero j)]; simp)]
      simp only [List.map_map]
      apply List.map_congr_left; intro j hj
      rw [List.mem_range] at hj
      have := hrow (j + 1) (by omega)
      rw [show s + (j + 1) = s + 1 + j by omega] at this
      obtain ⟨-, hr, hw, -, ht⟩ := this
      simp only [Function.comp, Msg.toFp, List.map_cons, List.map_nil, WalkV.edge, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (show j + 1 < ℓ by omega), Option.map_some, Option.getD_some,
        edgeAt, Fp.ofNat_toNat]
      rw [hr, hw, ht (by omega), ite01]
      simp [show j + 1 - 1 = j by omega, show s + (j + 1) = s + 1 + j by omega, natCast_eq,
        show (j + 1 + 1 = ℓ) ↔ (j + 2 = ℓ) by omega]
      exact (Fp.ofNat_toNat _).symm
    · simp only [rowT_recv_other _ _ hE hK]
      rw [flatMap_range'_nil _ _ _ (fun _ _ => rfl)]
      simp [walkRecvs, hE, hK]

theorem segSend (hL : TableLocal WalkTab.table tr T_WALK pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr ws) (isOne tr we) s ℓ) (hH : s + ℓ ≤ tr.height T_WALK)
    (b : Nat) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic WalkTab.interactions tr T_WALK q pub b true) =
      (walkSends [walkOfSeg tr (s, ℓ)] b).map Msg.toFp := by
  obtain ⟨h2, hrow, -, -, -, -⟩ := segInfo hL hseg hH
  by_cases hE : b = B_EDGE
  · subst hE
    simp only [rowT_edgeS, walkSends, ite_true, walkOfSeg, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_map]
    rw [flatMap_range'_single _ (fun j => cellsE tr (s + j) (tr.cell T_WALK (s + j) u + 1)) s ℓ (fun j hj => by
      simp [(hrow j hj).1])]
    apply List.map_congr_left; intro j _
    simp only [Function.comp, cellsE_eq]
    congr 1
    rw [← natCast_eq, natCast_add, natCast_toNat]; rfl
  · by_cases hF : b = B_FINAL
    · subst hF
      simp only [rowT_final, walkSends, if_neg (by decide : ¬ B_FINAL = B_EDGE), ite_true, walkOfSeg,
        List.map_cons, List.map_nil, List.length_map, List.length_range]
      have hs : List.range' s ℓ = List.range' s (ℓ - 1) ++ [s + (ℓ - 1)] := by
        have := range'_succ' s (ℓ - 1); rwa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at this
      rw [hs, List.flatMap_append, flatMap_range'_nil _ s (ℓ - 1) (fun j (hj : j < ℓ - 1) => by
        rw [(hrow j (Nat.lt_of_lt_of_le hj (Nat.sub_le ℓ 1))).2.2.1,
          if_neg (Nat.ne_of_lt (Nat.add_lt_of_lt_sub hj)), if_neg fp_zero_ne_one])]
      have hl := hrow (ℓ - 1) (by omega)
      rw [List.flatMap_singleton, hl.2.2.1, if_pos (show ℓ - 1 + 1 = ℓ by omega), if_pos rfl,
        List.nil_append]
      simp only [Msg.toFp, List.map_cons, List.map_nil, WalkV.edge, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (show ℓ - 1 < ℓ by omega), Option.map_some,
        Option.getD_some, edgeAt, Fp.ofNat_toNat]
      rw [hl.2.1]
      simp [Fp.ofNat_toNat]
    · simp only [rowT_send_other _ _ hE hF]
      rw [flatMap_range'_nil _ _ _ (fun _ _ => rfl)]
      simp [walkSends, hE, hF]

end ZkFormal.Near.WalkProof


namespace ZkFormal.Near
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.WalkTab WalkProof

/-- **The walk table's view.** -/
theorem walk_view : WalkViewStmt := by
  intro tr pub hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (segFacts hL) height_pos
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height T_WALK := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ b sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height T_WALK →
      rowTraffic WalkTab.interactions tr T_WALK q pub b sd = [] := by
    intro b sd q h1 h2
    have := zero_of_not_one hL h2 (by simp) (hpad q h1 h2)
    have hw : tr.cell T_WALK q we = 0 := by
      rcases isBool hL h2 (x := we) (by simp) with h | h
      · exact h
      · have := (rowFacts hL h2).2.2 h; simp_all
    have hg : tr.cell T_WALK q gK = 0 := by
      rw [(rowFacts hL h2).1, this]
      rcases isBool hL h2 (x := ws) (by simp) with h | h
      · rw [h]; grind
      · have := ((rowFacts hL h2).2.1 h).1; simp_all
    rw [rowT]; simp [this, hw, hg]
  refine ⟨segs.map (walkOfSeg tr), ⟨?_, ?_, ?_, ?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · -- nonempty: row 0 is active
    intro h
    rw [List.map_eq_nil_iff] at h
    subst h
    have := hpad 0 (by simp [segEnd]) height_pos
    have h0 := ((rowFacts hL height_pos).2.1 (row0 hL height_pos)).1
    simp [isOne, h0] at this
  · intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    obtain ⟨h2, -⟩ := segInfo hL (hall p hp) (hH p hp)
    refine ⟨by simp [walkOfSeg]; omega, fun st hst => ?_, Fp.toNat_lt _⟩
    simp only [walkOfSeg, List.mem_map, List.mem_range] at hst
    obtain ⟨j, -, rfl⟩ := hst
    exact ⟨by simp [edgeAt], Fp.toNat_lt _⟩
  · intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    obtain ⟨h2, -, hN, hI, hS, -⟩ := segInfo hL (hall p hp) (hH p hp)
    simp [walkOfSeg, WalkV.edge, edgeAt, List.getElem?_range (show 0 < p.2 by omega), hN, hI, hS,
      Fp.toNat_zero, natCast_eq, Fp.toNat_ofNat, SYM_START, P]
  · intro w hw i hi
    simp only [List.mem_map] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    obtain ⟨-, -, -, -, -, hch⟩ := segInfo hL (hall p hp) (hH p hp)
    simp only [walkOfSeg, List.length_map, List.length_range] at hi
    have := hch i hi
    have e : p.1 + (i + 1) = p.1 + i + 1 := by omega
    simp [walkOfSeg, WalkV.edge, edgeAt, List.getElem?_range hi, List.getElem?_range (show i < p.2 by omega),
      e, this.1, this.2]
  · intro w hw st hst x hx
    simp only [List.mem_map] at hw
    obtain ⟨p, -, rfl⟩ := hw
    simp only [walkOfSeg, List.mem_map, List.mem_range] at hst
    obtain ⟨j, -, rfl⟩ := hst
    simp only [edgeAt, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact Fp.toNat_lt _
  · simp only [walkTraffic]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b true),
      flatMap_segs segs _ _ (fun p hp => segSend hL (hall p hp) (hH p hp) b), walkSends_flat]
    simp [List.map_flatMap, walkOfSeg, List.flatMap_map]
  · simp only [walkTraffic]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b false),
      flatMap_segs segs _ _ (fun p hp => segRecv hL (hall p hp) (hH p hp) b), walkRecvs_flat]
    simp [List.map_flatMap, walkOfSeg, List.flatMap_map]

end ZkFormal.Near
