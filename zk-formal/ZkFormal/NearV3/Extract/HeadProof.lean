import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Tables.Head

/-!
# ZkFormal.NearV3.Extract.HeadProof — the `headV3` view (`HeadViewStmt`, `head_view`)

One `HeadE` per 32-row head segment: instance, root record id / length / walk target, the
`START` edge use count, and the pre/post root digests (the shift registers on the first row).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure HeadE where
  tau : Nat
  rid : Nat
  rlen : Nat
  rres : Nat
  mE : Nat
  pre : List Nat
  post : List Nat
  deriving Repr, Inhabited

structure HeadWf (hs : List HeadE) : Prop where
  len : ∀ h ∈ hs, h.pre.length = 32 ∧ h.post.length = 32
  canon : ∀ h ∈ hs, h.tau < P ∧ h.rid < P ∧ h.rlen < P ∧ h.rres < P ∧ h.mE < P ∧
    (∀ x ∈ h.pre, x < P) ∧ ∀ x ∈ h.post, x < P

def startEdgeMsg (h : HeadE) (u : Nat) : Msg := [0, h.tau, SYM_START, h.rres, 0, EK_DOWN, u]

def headSends (hs : List HeadE) (b : Nat) : List Msg :=
  if b = B_MIDROOT then hs.map fun h => [h.tau] ++ h.post
  else if b = B_PARENT then hs.map fun h => [h.rid, h.tau, 0, h.rlen, h.rres]
  else if b = B_EDGE then hs.map fun h => startEdgeMsg h 0
  else if b = B_DIGS then hs.flatMap fun h => (List.range 32).map fun i => [msgId K_NPRE h.rid, h.tau, i, h.pre.getD i 0]
  else []

def headRecvs (hs : List HeadE) (b : Nat) : List Msg :=
  if b = B_DIGEST then hs.flatMap fun h => [digMsg (msgId K_NPRE h.rid) h.rlen h.pre, digMsg (msgId K_NPOST h.rid) h.rlen h.post]
  else if b = B_ROOT then hs.map fun h => [h.tau] ++ h.pre
  else if b = B_EDGE then hs.map fun h => startEdgeMsg h h.mE
  else []

def headTraffic (hs : List HeadE) : Traffic := ⟨headSends hs, headRecvs hs⟩

/-- **The `headV3` view statement.** -/
def HeadViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal HeadV3.table tr t pub →
    ∃ hs, HeadWf hs ∧ TableTraffic HeadV3.interactions tr t pub (headTraffic hs)

end ZkFormal.NearV3

namespace ZkFormal.NearV3.HeadProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.HeadV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem con (hL : TableLocal HeadV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ HeadV3.constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

theorem mem_c {e : Expr} (h : e ∈ ([ .mul (c hf) (Dsl.not (c act)), .mul (c hl) (Dsl.not (c act)),
    .mul .isFirst (Dsl.not (c hf)),
    .mul .isLast (.mul (c act) (Dsl.not (c hl))),
    .mul (c hf) (c i), .mul (c hl) (sub (c i) (k 31)),
    mul3 (c act) (Dsl.not (c hl)) (Dsl.not (n act)),
    mul3 (c act) (Dsl.not (c hl)) (n hf),
    mul3 (c act) (Dsl.not (c hl)) (sub (n i) (.add (c i) (k 1))) ] : List Expr)) :
    e ∈ HeadV3.constraints := by
  unfold HeadV3.constraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))

theorem mem_tail {e : Expr} (h : e ∈ ([ mul3 (c hl) (n act) (Dsl.not (n hf)),
    mul3 .isTransition (Dsl.not (c act)) (n act) ] : List Expr)) : e ∈ HeadV3.constraints := by
  unfold HeadV3.constraints; exact List.mem_append_right _ h

theorem isBool (hL : TableLocal HeadV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ [act, hf, hl]) : tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold HeadV3.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx)))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem zero_of_not_one (hL : TableLocal HeadV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ [act, hf, hl]) (h : isOne tr tt x r = false) : tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

section
variable (hL : TableLocal HeadV3.table tr tt pub)
include hL

theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r hf = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r i = 0) ∧
    (tr.cell tt r hl = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r i = 31) := by
  have h1 := con hL hr (e := .mul (c hf) (Dsl.not (c act))) (mem_c (by simp))
  have h2 := con hL hr (e := .mul (c hl) (Dsl.not (c act))) (mem_c (by simp))
  have h3 := con hL hr (e := .mul (c hf) (c i)) (mem_c (by simp))
  have h4 := con hL hr (e := .mul (c hl) (sub (c i) (k 31))) (mem_c (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; exact ⟨by grind, by grind⟩
  · rw [h] at h2 h4; exact ⟨by grind, by grind⟩

theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl0 : tr.cell tt r hl = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) hf = 0 ∧ tr.cell tt (r + 1) i = tr.cell tt r i + 1 ∧
    (∀ x ∈ headConst, tr.cell tt (r + 1) x = tr.cell tt r x) ∧
    (∀ j, j < 31 → tr.cell tt (r + 1) (reg j) = tr.cell tt r (reg (j + 1)) ∧
      tr.cell tt (r + 1) (preg j) = tr.cell tt r (preg (j + 1))) := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c act) (Dsl.not (c hl)) (Dsl.not (n act))) (mem_c (by simp))
  have h2 := con hL hr' (e := mul3 (c act) (Dsl.not (c hl)) (n hf)) (mem_c (by simp))
  have h3 := con hL hr' (e := mul3 (c act) (Dsl.not (c hl)) (sub (n i) (.add (c i) (k 1)))) (mem_c (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3
  rw [ha, hl0] at h1 h2 h3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_, fun j hj => ⟨?_, ?_⟩⟩
  · have h5 := con hL hr' (e := mul3 (c act) (Dsl.not (c hl)) (sub (n x) (c x))) (by
      unfold HeadV3.constraints
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun x => mul3 (c act) (Dsl.not (c hl)) (sub (n x) (c x))) hx))))
    simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
    rw [ha, hl0] at h5; grind
  · have h5 := con hL hr' (e := mul3 (c act) (Dsl.not (c hl)) (sub (n (reg j)) (c (reg (j + 1))))) (by
      unfold HeadV3.constraints
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨j, hj, by simp⟩)
    simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
    rw [ha, hl0] at h5; grind
  · have h5 := con hL hr' (e := mul3 (c act) (Dsl.not (c hl)) (sub (n (preg j)) (c (preg (j + 1))))) (by
      unfold HeadV3.constraints
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨j, hj, by simp⟩)
    simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
    rw [ha, hl0] at h5; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl1 : tr.cell tt r hl = 1)
    (ha : tr.cell tt (r + 1) act = 1) : tr.cell tt (r + 1) hf = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c hl) (n act) (Dsl.not (n hf))) (mem_tail (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl1] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) : tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act)) (mem_tail (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 hf = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c hf))) (mem_c (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1
  grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) hl = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c hl)))) (mem_c (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem segFacts : SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt hf) (isOne tr tt hl) where
  first_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).1 h).1
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2 h).1
  cont r hr ha hl' := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) (by simp) hl')
    simp [isOne, this.1, this.2.1]
  next r hr hl' ha := by
    simp only [isOne, decide_eq_true_eq] at hl' ha ⊢
    exact nextSeg hL hr hl' ha
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) (by simp) ha)
    simp [isOne, this]
  start h0 := by simp [isOne, row0 hL h0]
  stop h0 ha := by simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem height_le : tr.height tt ≤ 2 ^ 11 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

/-- A head is 32 rows; `i` counts, the constants stay, the registers shift. -/
theorem seg32 {s ℓ : Nat} (hseg : IsSeg (isOne tr tt act) (isOne tr tt hf) (isOne tr tt hl) s ℓ)
    (hH : s + ℓ ≤ tr.height tt) :
    ℓ = 32 ∧ ∀ j, j < 32 → tr.cell tt (s + j) act = 1 ∧ tr.cell tt (s + j) i = ((j : Nat) : Fp) ∧
      (∀ x ∈ headConst, tr.cell tt (s + j) x = tr.cell tt s x) ∧
      tr.cell tt (s + j) (reg 0) = tr.cell tt s (reg j) := by
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  have hpos := hseg.1
  have hsf : tr.cell tt s hf = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hsl : tr.cell tt (s + ℓ - 1) hl = 1 := by have := hseg.2.2.1; simpa [isOne] using this
  have hA : ∀ r, s ≤ r → r < s + ℓ → tr.cell tt r act = 1 := fun r h1 h2 => by
    have := hseg.2.2.2.1 r h1 h2; simpa [isOne] using this
  have hW : ∀ r, s ≤ r → r + 1 < s + ℓ → tr.cell tt r hl = 0 := fun r h1 h2 =>
    zero_of_not_one hL (by omega) (by simp) (hseg.2.2.2.2.2 r h1 h2)
  have hw : ∀ r, s ≤ r → r + 1 < s + ℓ → _ := fun r h1 h2 =>
    within hL (r := r) (by omega) (hA r h1 (by omega)) (hW r h1 h2)
  have hi := counter_of (f := fun r => tr.cell tt r i) (s := s) (ℓ := ℓ) (v0 := 0)
    ((rowFacts hL (by omega : s < _)).1 hsf).2 (fun r h1 h2 => (hw r h1 h2).2.2.1)
  have hend := ((rowFacts hL (by omega : s + ℓ - 1 < _)).2 hsl).2
  have h31 : ℓ - 1 = 31 := by
    have e := hi (s + ℓ - 1) (by omega) (by omega)
    rw [hend, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at e
    exact (ofNat_inj (a := 31) (b := ℓ - 1) (by unfold P; omega) (by omega) e).symm
  have hℓ : ℓ = 32 := by omega
  subst hℓ
  -- register shift: reg 0 at row s + j is reg j at row s
  have hshift : ∀ j, j < 32 → ∀ m, m + j < 32 → tr.cell tt (s + j) (reg m) = tr.cell tt s (reg (m + j)) := by
    intro j
    induction j with
    | zero => intro _ m _; rfl
    | succ j ih =>
      intro hj m hm
      have := ((hw (s + j) (by omega) (by omega)).2.2.2.2 m (by omega)).1
      rw [show s + j + 1 = s + (j + 1) by omega] at this
      rw [this, ih (by omega) (m + 1) (by omega)]; congr 2; omega
  refine ⟨rfl, fun j hj => ⟨hA (s + j) (by omega) (by omega), ?_, fun x hx => ?_, ?_⟩⟩
  · have := hi (s + j) (by omega) (by omega)
    simpa [show 0 + (s + j - s) = j by omega] using this
  · exact const_of (f := fun r => tr.cell tt r x) (s := s) (ℓ := 32)
      (fun r h1 h2 => (hw r h1 h2).2.2.2.1 x hx) (s + j) (by omega) (by omega)
  · rw [hshift j hj 0 (by omega)]; simp

end

/-! ## View and traffic -/

def headOf (tr : Trace Fp) (tt : Nat) (p : Nat × Nat) : HeadE :=
  ⟨(tr.cell tt p.1 tau).toNat, (tr.cell tt p.1 rid).toNat, (tr.cell tt p.1 rlen).toNat,
    (tr.cell tt p.1 rres).toNat, (tr.cell tt p.1 mE).toNat,
    (List.range 32).map fun j => (tr.cell tt p.1 (reg j)).toNat,
    (List.range 32).map fun j => (tr.cell tt p.1 (preg j)).toNat⟩

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

def regsAt (tr : Trace Fp) (tt q : Nat) : List Fp := (List.range 32).map fun j => tr.cell tt q (reg j)
def pregsAt (tr : Trace Fp) (tt q : Nat) : List Fp := (List.range 32).map fun j => tr.cell tt q (preg j)

theorem rowT (q : Nat) (b : Nat) (sd : Bool) :
    rowTraffic HeadV3.interactions tr tt q pub b sd =
      (if b = B_DIGEST ∧ sd = false ∧ tr.cell tt q hf = 1 then
        [[(K_NPRE : Fp) + 16 * tr.cell tt q rid, tr.cell tt q rlen] ++ regsAt tr tt q] else []) ++
      (if b = B_DIGEST ∧ sd = false ∧ tr.cell tt q hf = 1 then
        [[(K_NPOST : Fp) + 16 * tr.cell tt q rid, tr.cell tt q rlen] ++ pregsAt tr tt q] else []) ++
      (if b = B_ROOT ∧ sd = false ∧ tr.cell tt q hf = 1 then [[tr.cell tt q tau] ++ regsAt tr tt q] else []) ++
      (if b = B_MIDROOT ∧ sd = true ∧ tr.cell tt q hf = 1 then [[tr.cell tt q tau] ++ pregsAt tr tt q] else []) ++
      (if b = B_PARENT ∧ sd = true ∧ tr.cell tt q hf = 1 then
        [[tr.cell tt q rid, tr.cell tt q tau, 0, tr.cell tt q rlen, tr.cell tt q rres]] else []) ++
      (if b = B_EDGE ∧ sd = true ∧ tr.cell tt q hf = 1 then
        [[0, tr.cell tt q tau, (SYM_START : Fp), tr.cell tt q rres, 0, (EK_DOWN : Fp), 0]] else []) ++
      (if b = B_EDGE ∧ sd = false ∧ tr.cell tt q hf = 1 then
        [[0, tr.cell tt q tau, (SYM_START : Fp), tr.cell tt q rres, 0, (EK_DOWN : Fp), tr.cell tt q mE]] else []) ++
      (if b = B_DIGS ∧ sd = true ∧ tr.cell tt q act = 1 then
        [[(K_NPRE : Fp) + 16 * tr.cell tt q rid, tr.cell tt q tau, tr.cell tt q i, tr.cell tt q (reg 0)]] else []) := by
  simp only [rowTraffic, HeadV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, HeadV3.regs, HeadV3.pregs,
    HeadV3.startEdge, List.map_cons, List.map_nil, List.map_append, List.map_map, eval_c, eval_k, eval_mid,
    regsAt, pregsAt, List.append_assoc, Function.comp_def]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_)))))) <;>
    (split <;> split <;> simp_all [eq_comm]) <;> grind

end ZkFormal.NearV3.HeadProof

namespace ZkFormal.NearV3.HeadProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.HeadV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- First-row messages of a head on bus `b`, side `sd`. -/
def firstMsgs (tr : Trace Fp) (tt q b : Nat) (sd : Bool) : List (List Fp) :=
  (if b = B_DIGEST ∧ sd = false then
    [[(K_NPRE : Fp) + 16 * tr.cell tt q rid, tr.cell tt q rlen] ++ regsAt tr tt q] else []) ++
  (if b = B_DIGEST ∧ sd = false then
    [[(K_NPOST : Fp) + 16 * tr.cell tt q rid, tr.cell tt q rlen] ++ pregsAt tr tt q] else []) ++
  (if b = B_ROOT ∧ sd = false then [[tr.cell tt q tau] ++ regsAt tr tt q] else []) ++
  (if b = B_MIDROOT ∧ sd = true then [[tr.cell tt q tau] ++ pregsAt tr tt q] else []) ++
  (if b = B_PARENT ∧ sd = true then [[tr.cell tt q rid, tr.cell tt q tau, 0, tr.cell tt q rlen, tr.cell tt q rres]]
    else []) ++
  (if b = B_EDGE ∧ sd = true then [[0, tr.cell tt q tau, (SYM_START : Fp), tr.cell tt q rres, 0, (EK_DOWN : Fp), 0]]
    else []) ++
  (if b = B_EDGE ∧ sd = false then
    [[0, tr.cell tt q tau, (SYM_START : Fp), tr.cell tt q rres, 0, (EK_DOWN : Fp), tr.cell tt q mE]] else [])

def digsMsg (tr : Trace Fp) (tt q : Nat) : List Fp :=
  [(K_NPRE : Fp) + 16 * tr.cell tt q rid, tr.cell tt q tau, tr.cell tt q i, tr.cell tt q (reg 0)]

theorem rowT' (q : Nat) (b : Nat) (sd : Bool) (ha : tr.cell tt q act = 1) (hf01 : tr.cell tt q hf = 0 ∨ tr.cell tt q hf = 1) :
    rowTraffic HeadV3.interactions tr tt q pub b sd =
      (if tr.cell tt q hf = 1 then firstMsgs tr tt q b sd else []) ++
      (if b = B_DIGS ∧ sd = true then [digsMsg tr tt q] else []) := by
  rw [rowT]
  have hD1 : B_DIGEST ≠ B_DIGS := by decide
  have hD2 : B_ROOT ≠ B_DIGS := by decide
  have hD3 : B_MIDROOT ≠ B_DIGS := by decide
  have hD4 : B_PARENT ≠ B_DIGS := by decide
  have hD5 : B_EDGE ≠ B_DIGS := by decide
  rcases hf01 with h | h
  · simp [h, ha, firstMsgs, digsMsg]
  · by_cases hb : b = B_DIGS
    · subst hb; simp [h, ha, firstMsgs, digsMsg, hD1.symm, hD2.symm, hD3.symm, hD4.symm, hD5.symm]
    · simp [h, ha, firstMsgs, digsMsg, hb]

theorem segTraffic (hL : TableLocal HeadV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt hf) (isOne tr tt hl) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (b : Nat) (sd : Bool) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic HeadV3.interactions tr tt q pub b sd) =
      firstMsgs tr tt s b sd ++
        (if b = B_DIGS ∧ sd = true then (List.range 32).map fun j => digsMsg tr tt (s + j) else []) := by
  obtain ⟨h32, hrow⟩ := seg32 hL hseg hH
  subst h32
  have hf0 : tr.cell tt s hf = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hfj : ∀ j, 0 < j → j < 32 → tr.cell tt (s + j) hf = 0 := fun j h0 hj =>
    zero_of_not_one hL (by omega) (by simp) (hseg.2.2.2.2.1 (s + j) (by omega) (by omega))
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [show (32 : Nat) = 1 + 31 from rfl, List.range_add, List.flatMap_append]
  simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
  rw [rowT' s b sd (by simpa using (hrow 0 (by omega)).1) (Or.inr hf0), if_pos hf0]
  have hrest : (List.map (fun x => 1 + x) (List.range 31)).flatMap
      (fun j => rowTraffic HeadV3.interactions tr tt (s + j) pub b sd) =
      if b = B_DIGS ∧ sd = true then (List.range 31).map fun j => digsMsg tr tt (s + (1 + j)) else [] := by
    rw [List.flatMap_map]
    split
    · rename_i hb
      rw [map_eq_flatMap]
      apply flatMap_congr'
      intro j hj
      have hj' := List.mem_range.1 hj
      rw [rowT' (s + (1 + j)) b sd (hrow (1 + j) (by omega)).1 (Or.inl (hfj (1 + j) (by omega) (by omega))),
        if_neg (by rw [hfj (1 + j) (by omega) (by omega)]; exact fp_zero_ne_one), if_pos hb]; rfl
    · rename_i hb
      rw [flatMap_nil_fun' _ _ (fun j hj => by
        rw [rowT' (s + (1 + j)) b sd (hrow (1 + j) (by have := List.mem_range.1 hj; omega)).1
          (Or.inl (hfj (1 + j) (by omega) (by have := List.mem_range.1 hj; omega))),
          if_neg (by rw [hfj (1 + j) (by omega) (by have := List.mem_range.1 hj; omega)]; exact fp_zero_ne_one),
          if_neg hb]; rfl)]
  rw [hrest, List.append_assoc]
  congr 1
  split
  · simp [List.range_add, List.map_map, Function.comp_def]
  · rfl
where
  flatMap_nil_fun' {α β : Type} (l : List α) (f : α → List β) (h : ∀ a ∈ l, f a = []) : l.flatMap f = [] := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

end ZkFormal.NearV3.HeadProof

namespace ZkFormal.NearV3.HeadProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.HeadV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem toFp_mid (kk : Nat) (x : Fp) : Fp.ofNat (msgId kk x.toNat) = (kk : Fp) + 16 * x := by
  unfold msgId
  rw [← natCast_eq, natCast_add, natCast_mul, natCast_eq x.toNat, Fp.ofNat_toNat]; rfl

theorem toFp_regs (q : Nat) :
    ((List.range 32).map fun j => (tr.cell tt q (reg j)).toNat).map Fp.ofNat = regsAt tr tt q := by
  simp [regsAt, Fp.ofNat_toNat]

theorem toFp_pregs (q : Nat) :
    ((List.range 32).map fun j => (tr.cell tt q (preg j)).toNat).map Fp.ofNat = pregsAt tr tt q := by
  simp [pregsAt, Fp.ofNat_toNat]

theorem o0 : Fp.ofNat 0 = 0 := rfl

theorem segView (hL : TableLocal HeadV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt hf) (isOne tr tt hl) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (b : Nat) (sd : Bool) :
    firstMsgs tr tt s b sd ++
        (if b = B_DIGS ∧ sd = true then (List.range 32).map fun j => digsMsg tr tt (s + j) else []) =
      ((if sd then headSends [headOf tr tt (s, ℓ)] b else headRecvs [headOf tr tt (s, ℓ)] b)).map Msg.toFp := by
  obtain ⟨-, hrow⟩ := seg32 hL hseg hH
  have d1 : B_DIGEST ≠ B_ROOT := by decide
  have d2 : B_DIGEST ≠ B_MIDROOT := by decide
  have d3 : B_DIGEST ≠ B_PARENT := by decide
  have d4 : B_DIGEST ≠ B_EDGE := by decide
  have d5 : B_DIGEST ≠ B_DIGS := by decide
  have d6 : B_ROOT ≠ B_MIDROOT := by decide
  have d7 : B_ROOT ≠ B_PARENT := by decide
  have d8 : B_ROOT ≠ B_EDGE := by decide
  have d9 : B_ROOT ≠ B_DIGS := by decide
  have d10 : B_MIDROOT ≠ B_PARENT := by decide
  have d11 : B_MIDROOT ≠ B_EDGE := by decide
  have d12 : B_MIDROOT ≠ B_DIGS := by decide
  have d13 : B_PARENT ≠ B_EDGE := by decide
  have d14 : B_PARENT ≠ B_DIGS := by decide
  have d15 : B_EDGE ≠ B_DIGS := by decide
  cases sd
  · -- receives
    simp only [firstMsgs, headRecvs, headOf, Bool.false_eq_true, and_false, if_false, and_true,
      List.append_nil, if_neg (show ¬ (false = true) by decide)]
    by_cases hb1 : b = B_DIGEST
    · subst hb1
      simp [d1, d2, d3, d4, digMsg, Msg.toFp, toFp_mid, toFp_regs, toFp_pregs, Fp.ofNat_toNat, regsAt, pregsAt, Function.comp_def]
    · by_cases hb2 : b = B_ROOT
      · subst hb2
        simp [d1.symm, d6, d7, d8, Msg.toFp, toFp_regs, Fp.ofNat_toNat, regsAt, Function.comp_def]
      · by_cases hb3 : b = B_EDGE
        · subst hb3
          simp [d4.symm, d8.symm, d11.symm, d13.symm, startEdgeMsg, Msg.toFp, Fp.ofNat_toNat, o0, natCast_eq]
        · simp [hb1, hb2, hb3]
  · -- sends
    simp only [firstMsgs, headSends, headOf, and_false, if_false, and_true, List.nil_append,
      List.append_nil]
    by_cases hb1 : b = B_MIDROOT
    · subst hb1
      simp [d2.symm, d6.symm, d10, d11, d12, Msg.toFp, toFp_pregs, Fp.ofNat_toNat, pregsAt, Function.comp_def]
    · by_cases hb2 : b = B_PARENT
      · subst hb2
        simp [d3.symm, d7.symm, d10.symm, d13, d14, Msg.toFp, Fp.ofNat_toNat, o0]
      · by_cases hb3 : b = B_EDGE
        · subst hb3
          simp [d4.symm, d8.symm, d11.symm, d13.symm, d15, startEdgeMsg, Msg.toFp, Fp.ofNat_toNat, o0, natCast_eq]
        · by_cases hb4 : b = B_DIGS
          · subst hb4
            simp only [d5.symm, d9.symm, d12.symm, d14.symm, d15.symm, if_false, if_true, and_self,
              List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
            apply List.map_congr_left
            intro j hj
            have hj' := List.mem_range.1 hj
            obtain ⟨-, hi, hk, hr0⟩ := hrow j hj'
            simp only [digsMsg, Function.comp, Msg.toFp, List.map_cons, List.map_nil, toFp_mid,
              hk rid (by simp [headConst]), hk tau (by simp [headConst]), hi, hr0, Fp.ofNat_toNat,
              List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj', Option.map_some,
              Option.getD_some, natCast_eq]
          · simp [hb1, hb2, hb3, hb4]

end ZkFormal.NearV3.HeadProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HeadProof

theorem headSends_flat (hs : List HeadE) (b : Nat) : headSends hs b = hs.flatMap fun h => headSends [h] b := by
  unfold headSends
  repeat' split
  all_goals simp [map_eq_flatMap]

theorem headRecvs_flat (hs : List HeadE) (b : Nat) : headRecvs hs b = hs.flatMap fun h => headRecvs [h] b := by
  unfold headRecvs
  repeat' split
  all_goals simp [map_eq_flatMap]

/-- **The `headV3` view.** -/
theorem head_view : HeadViewStmt := by
  intro tr pub tt hL
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (segFacts hL) hpos
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ b sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic HeadV3.interactions tr tt q pub b sd = [] := by
    intro b sd q h1 h2
    have h0 := zero_of_not_one hL h2 (by simp) (hpad q h1 h2)
    have hf0 : tr.cell tt q HeadV3.hf = 0 := by
      rcases isBool hL h2 (x := HeadV3.hf) (by simp) with h | h
      · exact h
      · have := ((rowFacts hL h2).1 h).1; rw [h0] at this; exact absurd this (by decide)
    rw [rowT]; simp [h0, hf0]
  refine ⟨segs.map (headOf tr tt), ⟨fun h hh => ?_, fun h hh => ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh; simp [headOf]
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, fun x hx => ?_, fun x hx => ?_⟩ <;>
    · simp only [headOf, List.mem_map] at hx; obtain ⟨j, -, rfl⟩ := hx; exact Fp.toNat_lt _
  · simp only [headTraffic]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b true),
      flatMap_segs segs _ _ (fun p hp => (segTraffic hL (hall p hp) (hH p hp) b true).trans
        (segView hL (hall p hp) (hH p hp) b true)), headSends_flat]
    simp [List.map_flatMap, List.flatMap_map]
  · simp only [headTraffic]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b false),
      flatMap_segs segs _ _ (fun p hp => (segTraffic hL (hall p hp) (hH p hp) b false).trans
        (segView hL (hall p hp) (hH p hp) b false)), headRecvs_flat]
    simp [List.map_flatMap, List.flatMap_map]

end ZkFormal.NearV3
