import ZkFormal.NearV3.Extract.WalkView
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.NearV3.Extract.WalkProof — `WalkV3ViewStmt`

Adapted from v1 `Extract/WalkProof.lean` (`walk_view`): row facts, segment decomposition
(`ws … we`), one `WalkR` per segment, exact traffic.  New: the four row modes, the `BMAP`
lookups, the bit/one-hot facts of the branch terminal, the `FINAL` contents.
-/

namespace ZkFormal.NearV3.WalkProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.WalkV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem con (hL : TableLocal WalkV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ WalkV3.constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

theorem mem_tail {e : Expr} (h : e ∈ ([ sub (c gK) (sub (c act) (c ws)),
    sub (sum (modes.map c)) (c act),
    .mul (c ws) (Dsl.not (c act)), .mul (c we) (Dsl.not (c act)),
    .mul (c ws) (c we),
    .mul (c ws) (Dsl.not (c mS)),
    .mul (c ws) (sub (c nI) (c tau)), .mul (c ws) (sub (c sym) (k SYM_START)),
    .mul (c ws) (c t),
    .mul .isFirst (Dsl.not (c ws)),
    .mul .isLast (.mul (c act) (Dsl.not (c we))),
    mul3 (c act) (Dsl.not (c we)) (Dsl.not (n act)),
    mul3 (c act) (Dsl.not (c we)) (n ws),
    mul3 (c act) (Dsl.not (c we)) (sub (n w) (c w)),
    mul3 (c act) (Dsl.not (c we)) (sub (n tau) (c tau)),
    mul3 (c act) (Dsl.not (c we)) (sub (n t) (.add (c t) (c gK))),
    mul3 (c mS) (Dsl.not (c we)) (sub (n nN) (c nN2)),
    mul3 (c mS) (Dsl.not (c we)) (sub (n nI) (c nI2)),
    mul3 (c mS) (Dsl.not (c we)) (n mD),
    .mul (.add absE (c mD)) (.mul (Dsl.not (c we)) (Dsl.not (n mD))),
    .mul (c we) (sub (c sym) (k SYM_END)),
    .mul (c mS) (sub (c nib) (c sym)),
    mul3 (c mS) (Dsl.not (c we)) (.mul (c ek) (sub (c ek) (k 1))),
    mul3 (c mS) (c we) (sub (c ek) (k EK_VAL)),
    .mul (c mK) (.mul (sub (c ek) (k EK_KEY)) (sub (c ek) (k EK_LEND))),
    .mul (c mK) (sub (.mul (sub (c sym) (c nib)) (c inv)) (k 1)),
    .mul (c mB) (c nI),
    mul3 (c mB) (c we) (c hv),
    sub selSum (.mul (c mB) (Dsl.not (c we))),
    mul3 (c mB) (Dsl.not (c we)) (sub selIdx (c sym)),
    selBit,
    .mul (c we) (sub (c fk) (.add absE (c mD))),
    .mul (c we) (sub (c kk) (.mul (c mS) (c nN2))),
    mul3 (c we) (n act) (Dsl.not (n ws)),
    mul3 .isTransition (Dsl.not (c act)) (n act) ] : List Expr)) : e ∈ WalkV3.constraints := by
  unfold WalkV3.constraints; exact List.mem_append_right _ h

theorem isBool (hL : TableLocal WalkV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ boolCols) : tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold WalkV3.constraints
    exact List.mem_append_left _ (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem bc_act : act ∈ boolCols := by simp [boolCols]
theorem bc_ws : ws ∈ boolCols := by simp [boolCols]
theorem bc_we : we ∈ boolCols := by simp [boolCols]
theorem bc_gK : gK ∈ boolCols := by simp [boolCols]
theorem bc_mS : mS ∈ boolCols := by simp [boolCols]
theorem bc_mK : mK ∈ boolCols := by simp [boolCols]
theorem bc_mB : mB ∈ boolCols := by simp [boolCols]
theorem bc_mD : mD ∈ boolCols := by simp [boolCols]
theorem bc_hv : hv ∈ boolCols := by simp [boolCols]
theorem bc_bmb (j : Nat) (hj : j < 16) : bmb j ∈ boolCols := by
  simp only [boolCols, List.mem_append, List.mem_map, List.mem_range]; exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
theorem bc_sel (j : Nat) (hj : j < 16) : sel j ∈ boolCols := by
  simp only [boolCols, List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨j, hj, rfl⟩

section
variable (hL : TableLocal WalkV3.table tr tt pub)
include hL

/-- Start / end / gate facts of a row. -/
theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r gK = tr.cell tt r act - tr.cell tt r ws ∧
    tr.cell tt r mS + (tr.cell tt r mK + (tr.cell tt r mB + (tr.cell tt r mD + 0))) = tr.cell tt r act ∧
    (tr.cell tt r ws = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r we = 0 ∧ tr.cell tt r mS = 1 ∧
      tr.cell tt r nI = tr.cell tt r tau ∧ tr.cell tt r sym = (SYM_START : Nat) ∧ tr.cell tt r t = 0) ∧
    (tr.cell tt r we = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r sym = (SYM_END : Nat) ∧
      tr.cell tt r fk = tr.cell tt r mK + tr.cell tt r mB + tr.cell tt r mD ∧
      tr.cell tt r kk = tr.cell tt r mS * tr.cell tt r nN2) := by
  have h0 := con hL hr (e := sub (c gK) (sub (c act) (c ws))) (mem_tail (by simp))
  have h0' := con hL hr (e := sub (sum (modes.map c)) (c act)) (mem_tail (by simp))
  have h1 := con hL hr (e := .mul (c ws) (Dsl.not (c act))) (mem_tail (by simp))
  have h2 := con hL hr (e := .mul (c we) (Dsl.not (c act))) (mem_tail (by simp))
  have h3 := con hL hr (e := .mul (c ws) (c we)) (mem_tail (by simp))
  have h3' := con hL hr (e := .mul (c ws) (Dsl.not (c mS))) (mem_tail (by simp))
  have h5 := con hL hr (e := .mul (c ws) (sub (c nI) (c tau))) (mem_tail (by simp))
  have h6 := con hL hr (e := .mul (c ws) (sub (c sym) (k SYM_START))) (mem_tail (by simp))
  have h7 := con hL hr (e := .mul (c ws) (c t)) (mem_tail (by simp))
  have h8 := con hL hr (e := .mul (c we) (sub (c sym) (k SYM_END))) (mem_tail (by simp))
  have h9 := con hL hr (e := .mul (c we) (sub (c fk) (.add absE (c mD)))) (mem_tail (by simp))
  have h10 := con hL hr (e := .mul (c we) (sub (c kk) (.mul (c mS) (c nN2)))) (mem_tail (by simp))
  simp only [modes, List.map_cons, List.map_nil, eval_sum_cons, eval_sum_nil, absE, eval_mul, eval_c,
    eval_not, eval_sub, eval_k, eval_add] at h0 h0' h1 h2 h3 h3' h5 h6 h7 h8 h9 h10
  refine ⟨by grind, by grind, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3 h3' h5 h6 h7
    refine ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at h2 h8 h9 h10
    refine ⟨by grind, by grind, by grind, by grind⟩

/-- Mode facts of a row. -/
theorem modeFacts {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r mS = 1 → tr.cell tt r nib = tr.cell tt r sym ∧
      (tr.cell tt r we = 0 → tr.cell tt r ek * (tr.cell tt r ek - 1) = 0) ∧
      (tr.cell tt r we = 1 → tr.cell tt r ek = (EK_VAL : Nat))) ∧
    (tr.cell tt r mK = 1 → (tr.cell tt r ek - (EK_KEY : Nat)) * (tr.cell tt r ek - (EK_LEND : Nat)) = 0 ∧
      (tr.cell tt r sym - tr.cell tt r nib) * tr.cell tt r inv = 1) ∧
    (tr.cell tt r mB = 1 → tr.cell tt r nI = 0 ∧ (tr.cell tt r we = 1 → tr.cell tt r hv = 0)) ∧
    selSum.eval tr tt r pub = tr.cell tt r mB * (1 - tr.cell tt r we) ∧
    tr.cell tt r mB * (1 - tr.cell tt r we) * (selIdx.eval tr tt r pub - tr.cell tt r sym) = 0 ∧
    selBit.eval tr tt r pub = 0 := by
  have h1 := con hL hr (e := .mul (c mS) (sub (c nib) (c sym))) (mem_tail (by simp))
  have h2 := con hL hr (e := mul3 (c mS) (Dsl.not (c we)) (.mul (c ek) (sub (c ek) (k 1)))) (mem_tail (by simp))
  have h3 := con hL hr (e := mul3 (c mS) (c we) (sub (c ek) (k EK_VAL))) (mem_tail (by simp))
  have h4 := con hL hr (e := .mul (c mK) (.mul (sub (c ek) (k EK_KEY)) (sub (c ek) (k EK_LEND))))
    (mem_tail (by simp))
  have h5 := con hL hr (e := .mul (c mK) (sub (.mul (sub (c sym) (c nib)) (c inv)) (k 1))) (mem_tail (by simp))
  have h6 := con hL hr (e := .mul (c mB) (c nI)) (mem_tail (by simp))
  have h7 := con hL hr (e := mul3 (c mB) (c we) (c hv)) (mem_tail (by simp))
  have h8 := con hL hr (e := sub selSum (.mul (c mB) (Dsl.not (c we)))) (mem_tail (by simp))
  have h9 := con hL hr (e := mul3 (c mB) (Dsl.not (c we)) (sub selIdx (c sym))) (mem_tail (by simp))
  have h10 := con hL hr (e := selBit) (mem_tail (by simp))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, by grind, by grind, h10⟩
  · rw [h] at h1 h2 h3
    refine ⟨by grind, fun hw => ?_, fun hw => ?_⟩
    · rw [hw] at h2; grind
    · rw [hw] at h3; grind
  · rw [h] at h4 h5; exact ⟨by grind, by grind⟩
  · rw [h] at h6 h7; exact ⟨by grind, fun hw => by rw [hw] at h7; grind⟩

theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl : tr.cell tt r we = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) ws = 0 ∧
    tr.cell tt (r + 1) w = tr.cell tt r w ∧ tr.cell tt (r + 1) tau = tr.cell tt r tau ∧
    tr.cell tt (r + 1) t = tr.cell tt r t + tr.cell tt r gK ∧
    (tr.cell tt r mS = 1 → tr.cell tt (r + 1) nN = tr.cell tt r nN2 ∧
      tr.cell tt (r + 1) nI = tr.cell tt r nI2 ∧ tr.cell tt (r + 1) mD = 0) ∧
    (tr.cell tt r mS = 0 → tr.cell tt (r + 1) mD = 1) := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (Dsl.not (n act))) (mem_tail (by simp))
  have h2 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (n ws)) (mem_tail (by simp))
  have h3 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n w) (c w))) (mem_tail (by simp))
  have h3' := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n tau) (c tau))) (mem_tail (by simp))
  have h4 := con hL hr' (e := mul3 (c act) (Dsl.not (c we)) (sub (n t) (.add (c t) (c gK)))) (mem_tail (by simp))
  have h5 := con hL hr' (e := mul3 (c mS) (Dsl.not (c we)) (sub (n nN) (c nN2))) (mem_tail (by simp))
  have h6 := con hL hr' (e := mul3 (c mS) (Dsl.not (c we)) (sub (n nI) (c nI2))) (mem_tail (by simp))
  have h7 := con hL hr' (e := mul3 (c mS) (Dsl.not (c we)) (n mD)) (mem_tail (by simp))
  have h8 := con hL hr' (e := .mul (.add absE (c mD)) (.mul (Dsl.not (c we)) (Dsl.not (n mD))))
    (mem_tail (by simp))
  have hm := (rowFacts hL hr').2.1
  simp only [absE, eval_mul3, eval_mul, eval_add, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h1 h2 h3 h3' h4 h5 h6 h7 h8
  rw [ha, hl] at h1 h2 h3 h3' h4
  rw [hl] at h5 h6 h7 h8
  refine ⟨by grind, by grind, by grind, by grind, by grind, fun hs => ?_, fun hs => ?_⟩
  · rw [hs] at h5 h6 h7; exact ⟨by grind, by grind, by grind⟩
  · rw [hs, ha] at hm
    have : tr.cell tt r mK + (tr.cell tt r mB + tr.cell tt r mD) = 1 := by grind
    have : tr.cell tt r mK + tr.cell tt r mB + tr.cell tt r mD = 1 := by grind
    rw [this] at h8; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r we = 1)
    (ha : tr.cell tt (r + 1) act = 1) : tr.cell tt (r + 1) ws = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c we) (n act) (Dsl.not (n ws))) (mem_tail (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act)) (mem_tail (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 ws = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c ws))) (mem_tail (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1
  grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) we = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c we)))) (mem_tail (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

end

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem zero_of_not_one (hL : TableLocal WalkV3.table tr tt pub) {r : Nat}
    (hr : r < tr.height tt) {x : Nat} (hx : x ∈ boolCols) (h : isOne tr tt x r = false) :
    tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem segFacts (hL : TableLocal WalkV3.table tr tt pub) :
    SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt ws) (isOne tr tt we) where
  first_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.2.1 h).1
  last_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.2.2 h).1
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) bc_we hl)
    simp [isOne, this.1, this.2.1]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact nextSeg hL hr hl ha
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) bc_act ha)
    simp [isOne, this]
  start h0 := by simp [isOne, row0 hL h0]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem height_le (hL : TableLocal WalkV3.table tr tt pub) : tr.height tt ≤ 2 ^ 21 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_pos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _

/-- Facts about one walk segment. -/
theorem segInfo (hL : TableLocal WalkV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt ws) (isOne tr tt we) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    2 ≤ ℓ ∧
    (∀ j, j < ℓ → tr.cell tt (s + j) act = 1 ∧ tr.cell tt (s + j) w = tr.cell tt s w ∧
      tr.cell tt (s + j) tau = tr.cell tt s tau ∧
      tr.cell tt (s + j) we = (if j + 1 = ℓ then 1 else 0) ∧
      tr.cell tt (s + j) gK = (if j = 0 then 0 else 1) ∧
      (0 < j → tr.cell tt (s + j) t = ((j - 1 : Nat) : Fp))) ∧
    tr.cell tt s mS = 1 ∧ tr.cell tt s nI = tr.cell tt s tau ∧ tr.cell tt s sym = (SYM_START : Nat) ∧
    (∀ j, j + 1 < ℓ →
      (tr.cell tt (s + j) mS = 1 → tr.cell tt (s + j + 1) nN = tr.cell tt (s + j) nN2 ∧
        tr.cell tt (s + j + 1) nI = tr.cell tt (s + j) nI2 ∧ tr.cell tt (s + j + 1) mD = 0) ∧
      (tr.cell tt (s + j) mS = 0 → tr.cell tt (s + j + 1) mD = 1)) := by
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have hws : tr.cell tt s ws = 1 := by simpa [isOne] using hfs
  have hs := (rowFacts hL (by omega : s < _)).2.2.1 hws
  have hℓ : 2 ≤ ℓ := by
    rcases Nat.lt_or_ge ℓ 2 with h | h
    · have : ℓ = 1 := by omega
      subst this
      have := hs.2.1; simp [isOne, show s + 1 - 1 = s by omega, this] at hle
    · exact h
  have hA : ∀ j, j < ℓ → tr.cell tt (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell tt (s + j) we = 0 := fun j hj =>
    zero_of_not_one hL (by omega) bc_we (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hWS : ∀ j, 0 < j → j < ℓ → tr.cell tt (s + j) ws = 0 := fun j h0 hj => by
    have := (hw (j - 1) (by omega)).2.1; rwa [show s + (j - 1) + 1 = s + j by omega] at this
  have hG : ∀ j, j < ℓ → tr.cell tt (s + j) gK = (if j = 0 then 0 else 1) := fun j hj => by
    rw [(rowFacts hL (by omega : s + j < _)).1, hA j hj]
    by_cases h0 : j = 0
    · subst h0; simp only [Nat.add_zero, if_pos rfl]; rw [hws]; grind
    · rw [hWS j (by omega) hj, if_neg h0]; grind
  have hrr := const_of (f := fun q => tr.cell tt q w) (s := s) (ℓ := ℓ) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have hta := const_of (f := fun q => tr.cell tt q tau) (s := s) (ℓ := ℓ) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have ht := counter_of (f := fun q => tr.cell tt q t) (s := s + 1) (ℓ := ℓ - 1) (v0 := 0)
    (by
      have := (hw 0 (by omega)).2.2.2.2.1
      rw [show s + 0 + 1 = s + 1 by omega, show s + 0 = s by omega, hs.2.2.2.2.2] at this
      rw [this, show s = s + 0 by omega, hG 0 (by omega)]; simp; rfl)
    (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2.2.1
      rw [show s + (q - s) + 1 = q + 1 by omega, show s + (q - s) = q by omega] at this
      rw [this, show q = s + (q - s) by omega, hG (q - s) (by omega), if_neg (by omega)])
  refine ⟨hℓ, fun j hj => ⟨hA j hj, hrr (s + j) (by omega) (by omega), hta (s + j) (by omega) (by omega),
    ?_, hG j hj, fun h0 => ?_⟩, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
    fun j hj => ⟨(hw j hj).2.2.2.2.2.1, (hw j hj).2.2.2.2.2.2⟩⟩
  · by_cases hl : j + 1 = ℓ
    · rw [if_pos hl]
      have := hle; rw [show s + ℓ - 1 = s + j by omega] at this; simpa [isOne] using this
    · rw [if_neg hl]; exact hW j (by omega)
  · have := ht (s + j) (by omega) (by omega)
    rw [this]; congr 2; omega

/-! ## Sums of one-hot selectors -/

theorem evsum (n : Nat) (f : Nat → Expr) (v : Nat → Nat) {r : Nat}
    (h : ∀ j, j < n → (f j).eval tr tt r pub = ((v j : Nat) : Fp)) :
    (sum ((List.range n).map f)).eval tr tt r pub = ((((List.range n).map v).sum : Nat) : Fp) := by
  induction n with
  | zero => simp; rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, eval_sum_append,
      ih (fun j hj => h j (by omega)), List.sum_append]
    simp only [List.map_cons, List.map_nil, eval_sum_cons, eval_sum_nil, List.sum_cons, List.sum_nil,
      h n (by omega), natCast_add]
    grind

theorem sum_map_zero {α : Type} (f : α → Nat) : ∀ (l : List α), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, h a (by simp), sum_map_zero f l (fun x hx => h x (by simp [hx]))]

theorem le_sum_mem {α : Type} (f : α → Nat) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_mem f l x h; omega

theorem onehot : ∀ (n : Nat) (a : Nat → Nat), (∀ j, j < n → a j ≤ 1) → ((List.range n).map a).sum = 1 →
    ∃ j0, j0 < n ∧ a j0 = 1 ∧ ((List.range n).map fun j => j * a j).sum = j0 ∧
      ∀ b : Nat → Nat, ((List.range n).map fun j => a j * b j).sum = b j0
  | 0, a, _, h => by simp at h
  | n + 1, a, hb, h => by
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero] at h ⊢
    have han := hb n (by omega)
    by_cases hn : a n = 1
    · -- all earlier are zero
      have h0 : ((List.range n).map a).sum = 0 := by omega
      have hz : ∀ j, j < n → a j = 0 := by
        intro j hj
        have := le_sum_mem a (List.range n) j (List.mem_range.2 hj)
        omega
      have e1 : ((List.range n).map fun j => j * a j).sum = 0 :=
        sum_map_zero _ _ (fun j hj => by rw [hz j (List.mem_range.1 hj)]; simp)
      refine ⟨n, by omega, hn, by rw [e1, hn]; simp, fun b => ?_⟩
      have e2 : ((List.range n).map fun j => a j * b j).sum = 0 :=
        sum_map_zero _ _ (fun j hj => by rw [hz j (List.mem_range.1 hj)]; simp)
      rw [e2, hn]; simp
    · have hn0 : a n = 0 := by omega
      rw [hn0] at h
      obtain ⟨j0, hj0, ha0, hs, hb'⟩ := onehot n a (fun j hj => hb j (by omega)) (by simpa using h)
      refine ⟨j0, by omega, ha0, by rw [hs, hn0]; simp, fun b => ?_⟩
      rw [hb' b, hn0]; simp

theorem bitsVal_bit (v : Nat → Nat) : ∀ (n j : Nat), (∀ i, i < n → v i ≤ 1) → j < n →
    bitsVal v 0 n / 2 ^ j % 2 = v j
  | 0, j, _, hj => by omega
  | n + 1, j, hb, hj => by
    simp only [bitsVal, Nat.zero_add]
    have hlt := bitsVal_lt v 0 n (fun i hi => by simpa using hb i (by omega))
    have hvn := hb n (by omega)
    by_cases hjn : j = n
    · subst hjn
      rw [Nat.mul_comm (2 ^ j) (v j), Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hlt]
      simp; omega
    · have hj' : j < n := by omega
      have ih := bitsVal_bit v n j (fun i hi => hb i (by omega)) hj'
      -- 2^n * v n is a multiple of 2^(j+1)
      have hdiv : 2 ^ n * v n = 2 ^ j * (2 * (2 ^ (n - j - 1) * v n)) := by
        have : 2 ^ n = 2 ^ j * 2 * 2 ^ (n - j - 1) := by
          rw [← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega
        rw [this]; simp only [Nat.mul_assoc]
      rw [hdiv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_left, ih]

end ZkFormal.NearV3.WalkProof
