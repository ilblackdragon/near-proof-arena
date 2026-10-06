import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Tables.Uniq

/-!
# ZkFormal.NearV3.Extract.UniqProof — `UniqViewStmt` (the `uniqV3` view)

Adapted from v1 `Extract/SortProof.lean` (`sort_view`): same segment decomposition,
32-row segments, delay line and carry chain; new are the segment constants
`eid, peid, τ, st, eq`, the instance step, the equal case and the `DUP` send.

View (`UniqWf`): the entries in table order; for consecutive entries `a, b`:
* `b.peid = a.eid`, `b.τ = a.τ + b.st` (in `Fp`), `st, eq ∈ {0,1}`, the first entry has `eq = 0`;
* `b.eq = 1` ⇒ `b.st = 0` and (for byte values) `b.bytes = a.bytes`;
* `b.eq = 0`, `b.st = 0` ⇒ (for byte values) `le256 a.bytes < le256 b.bytes`.
Traffic: `DIGS (eid, τ, i, bytes[i])` received for `i < 32`; `DUP (eid, peid)` sent by
every entry with `eq = 1`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- One entry of `uniqV3` (values as canonical naturals). -/
structure UniqE where
  eid : Nat
  peid : Nat
  tau : Nat
  st : Nat
  eq : Nat
  bytes : List Nat
  deriving Repr, Inhabited

structure UniqWf (es : List UniqE) : Prop where
  len : ∀ e ∈ es, e.bytes.length = 32
  canon : ∀ e ∈ es, e.eid < P ∧ e.peid < P ∧ e.tau < P ∧ e.st ≤ 1 ∧ e.eq ≤ 1 ∧ ∀ y ∈ e.bytes, y < P
  first : ∀ e, es.head? = some e → e.eq = 0
  link : ∀ t (ht : t + 1 < es.length),
    es[t + 1].peid = es[t].eid ∧ es[t + 1].tau = (es[t].tau + es[t + 1].st) % P ∧
    (es[t + 1].eq = 1 → es[t + 1].st = 0 ∧
      ((∀ y ∈ es[t].bytes ++ es[t + 1].bytes, y < 256) → es[t + 1].bytes = es[t].bytes)) ∧
    (es[t + 1].eq = 0 → es[t + 1].st = 0 →
      (∀ y ∈ es[t].bytes ++ es[t + 1].bytes, y < 256) → le256 es[t].bytes < le256 es[t + 1].bytes)

def uniqSends (es : List UniqE) (b : Nat) : List Msg :=
  if b = B_DUP then (es.filter fun e => e.eq == 1).map fun e => [e.eid, e.peid] else []

def uniqRecvs (es : List UniqE) (b : Nat) : List Msg :=
  if b = B_DIGS then es.flatMap fun e => (List.range 32).map fun j => [e.eid, e.tau, j, e.bytes.getD j 0]
  else []

def uniqTraffic (es : List UniqE) : Traffic := ⟨uniqSends es, uniqRecvs es⟩

/-- **The `uniqV3` view statement** (any table index `t`). -/
def UniqViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal Uniq.table tr t pub →
    ∃ es, UniqWf es ∧ TableTraffic Uniq.interactions tr t pub (uniqTraffic es)

end ZkFormal.NearV3

namespace ZkFormal.NearV3.UniqProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.Uniq

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem con (hL : TableLocal Uniq.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ Uniq.constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

def boolList : List Nat := [act, sf, sl, ft, st, eq, cin, cout] ++ (List.range 8).map dbit

theorem isBool (hL : TableLocal Uniq.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ boolList) : tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold Uniq.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx)))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem zero_of_not_one (hL : TableLocal Uniq.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ boolList) (h : isOne tr tt x r = false) : tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

section
variable (hL : TableLocal Uniq.table tr tt pub)
include hL

theorem first_act {r : Nat} (hr : r < tr.height tt) (h : tr.cell tt r sf = 1) : tr.cell tt r act = 1 := by
  have := con hL hr (e := .mul (c sf) (Dsl.not (c act))) (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c, eval_not] at this
  rw [h] at this; grind

theorem last_act {r : Nat} (hr : r < tr.height tt) (h : tr.cell tt r sl = 1) : tr.cell tt r act = 1 := by
  have := con hL hr (e := .mul (c sl) (Dsl.not (c act))) (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c, eval_not] at this
  rw [h] at this; grind

theorem cont {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl : tr.cell tt r sl = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) sf = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (Dsl.not (n act)))
    (by simp [Uniq.constraints])
  have h2 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (n sf))
    (by simp [Uniq.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1 h2
  rw [ha, hl] at h1 h2
  constructor <;> grind

theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl : tr.cell tt r sl = 0) :
    tr.cell tt (r + 1) i = tr.cell tt r i + 1 ∧ tr.cell tt (r + 1) cin = tr.cell tt r cout ∧
    ∀ x ∈ segConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have h3 := con hL (by omega : r < _)
    (e := mul3 (c act) (Dsl.not (c sl)) (sub (n i) (.add (c i) (k 1)))) (by simp [Uniq.constraints])
  have h4 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (sub (n cin) (c cout)))
    (by simp [Uniq.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h3 h4
  rw [ha, hl] at h3 h4
  refine ⟨by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (sub (n x) (c x)))
    (by
      unfold Uniq.constraints
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun x => mul3 (c act) (Dsl.not (c sl)) (sub (n x) (c x))) hx))))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
  rw [ha, hl] at h5; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r sl = 1)
    (ha : tr.cell tt (r + 1) act = 1) :
    tr.cell tt (r + 1) sf = 1 ∧ tr.cell tt (r + 1) ft = 0 ∧ tr.cell tt (r + 1) peid = tr.cell tt r eid ∧
    tr.cell tt (r + 1) tau = tr.cell tt r tau + tr.cell tt (r + 1) st := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c sl) (n act) (Dsl.not (n sf)))
    (by simp [Uniq.constraints])
  have h2 := con hL (by omega : r < _) (e := .mul .isTransition (mul3 (c sl) (n act) (n ft)))
    (by simp [Uniq.constraints])
  have h3 := con hL (by omega : r < _)
    (e := .mul (mul3 (c sl) (n act) .isTransition) (sub (n peid) (c eid))) (by simp [Uniq.constraints])
  have h4 := con hL (by omega : r < _)
    (e := .mul (mul3 (c sl) (n act) .isTransition) (sub (n tau) (.add (c tau) (n st))))
    (by simp [Uniq.constraints])
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, nxt hr, eval_isTransition,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1 h2 h3 h4
  rw [ha, hl] at h1 h2 h3 h4
  refine ⟨by grind, by grind, by grind, by grind⟩

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) : tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (by simp [Uniq.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 sf = 1 ∧ tr.cell tt 0 ft = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c sf))) (by simp [Uniq.constraints])
  have h2 := con hL h0 (e := .mul .isFirst (Dsl.not (c ft))) (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1 h2
  constructor <;> grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) sl = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c sl)))) (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem segFields {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r sf = 1 → tr.cell tt r i = 0 ∧ tr.cell tt r cin = 1 - tr.cell tt r eq) ∧
    (tr.cell tt r sl = 1 → tr.cell tt r i = 31 ∧ tr.cell tt r cout = 0) := by
  have h1 := con hL hr (e := .mul (c sf) (c i)) (by simp [Uniq.constraints])
  have h2 := con hL hr (e := .mul (c sl) (sub (c i) (k 31))) (by simp [Uniq.constraints])
  have h3 := con hL hr (e := .mul (c sf) (sub (c cin) (Dsl.not (c eq)))) (by simp [Uniq.constraints])
  have h4 := con hL hr (e := .mul (c sl) (c cout)) (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; constructor <;> grind
  · rw [h] at h2 h4; constructor <;> grind

theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r ft * tr.cell tt r eq = 0 ∧ tr.cell tt r eq * tr.cell tt r st = 0 ∧
    tr.cell tt r eq * diffE.eval tr tt r pub = 0 := by
  have h1 := con hL hr (e := .mul (c ft) (c eq)) (by simp [Uniq.constraints])
  have h2 := con hL hr (e := .mul (c eq) (c st)) (by simp [Uniq.constraints])
  have h3 := con hL hr (e := .mul (c eq) diffE) (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem delay {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) :
    tr.cell tt (r + 1) (d 0) = tr.cell tt r bb ∧
    ∀ j, j < 31 → tr.cell tt (r + 1) (d (j + 1)) = tr.cell tt r (d j) := by
  have h1 := con hL (by omega : r < _) (e := .mul (c act) (sub (n (d 0)) (c bb)))
    (by simp [Uniq.constraints])
  simp only [eval_mul, eval_c, eval_sub, eval_n, nxt hr] at h1
  rw [ha] at h1
  refine ⟨by grind, fun j hj => ?_⟩
  have h2 := con hL (by omega : r < _) (e := .mul (c act) (sub (n (d (j + 1))) (c (d j))))
    (by simp only [Uniq.constraints, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨j, hj, rfl⟩)
  simp only [eval_mul, eval_c, eval_sub, eval_n, nxt hr] at h2
  rw [ha] at h2; grind

theorem chainEq {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1)
    (hf : tr.cell tt r ft = 0) (hs : tr.cell tt r st = 0) :
    tr.cell tt r bb + 256 * tr.cell tt r cout =
      tr.cell tt r (d 31) + diffE.eval tr tt r pub + tr.cell tt r cin := by
  have h1 := con hL hr (e := .mul cmpG
      (sub (c bb) (sub (.add (c (d 31)) (.add diffE (c cin))) (smul 256 (c cout)))))
    (by simp [Uniq.constraints])
  simp only [cmpG, eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_smul] at h1
  rw [ha, hf, hs] at h1
  grind

theorem segFacts : SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt sf) (isOne tr tt sl) where
  first_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact first_act hL hr h
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact last_act hL hr h
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have hl' := zero_of_not_one hL (by omega) (by simp [boolList]) hl
    have := cont hL hr ha hl'
    simp [isOne, this.1, this.2]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact (nextSeg hL hr hl ha).1
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) (by simp [boolList]) ha)
    simp [isOne, this]
  start h0 := by simp [isOne, (row0 hL h0).1]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem seg_step {s ℓ : Nat} (hseg : IsSeg (isOne tr tt act) (isOne tr tt sf) (isOne tr tt sl) s ℓ)
    (hH : s + ℓ ≤ tr.height tt) {r : Nat} (h1 : s ≤ r) (h2 : r + 1 < s + ℓ) :
    tr.cell tt r act = 1 ∧ tr.cell tt r sl = 0 := by
  obtain ⟨_, _, _, hact, _, hlast⟩ := hseg
  have ha := hact r h1 (by omega)
  have hl := hlast r h1 h2
  simp only [isOne, decide_eq_true_eq] at ha
  exact ⟨ha, zero_of_not_one hL (by omega) (by simp [boolList]) hl⟩

theorem height_le : tr.height tt ≤ 2 ^ 22 := by
  have := hL.log_le
  unfold Trace.height
  exact Nat.pow_le_pow_right (by omega) this

/-- A segment is 32 rows with `i = 0 … 31` and constant `segConst` columns. -/
theorem seg32 {s ℓ : Nat} (hseg : IsSeg (isOne tr tt act) (isOne tr tt sf) (isOne tr tt sl) s ℓ)
    (hH : s + ℓ ≤ tr.height tt) :
    ℓ = 32 ∧ ∀ j, j < ℓ → tr.cell tt (s + j) i = ((j : Nat) : Fp) ∧
      ∀ x ∈ segConst, tr.cell tt (s + j) x = tr.cell tt s x := by
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  have hpos := hseg.1
  have hsf : tr.cell tt s sf = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hsl : tr.cell tt (s + ℓ - 1) sl = 1 := by have := hseg.2.2.1; simpa [isOne] using this
  have hw : ∀ r, s ≤ r → r + 1 < s + ℓ → _ := fun r h1 h2 =>
    within hL (by omega) (seg_step hL hseg hH h1 h2).1 (seg_step hL hseg hH h1 h2).2
  have hi := counter_of (f := fun r => tr.cell tt r i) (s := s) (ℓ := ℓ) (v0 := 0)
    ((segFields hL (by omega : s < _)).1 hsf).1 (fun r h1 h2 => (hw r h1 h2).1)
  have hend := ((segFields hL (by omega : s + ℓ - 1 < _)).2 hsl).1
  have h31 : ℓ - 1 = 31 := by
    have e := hi (s + ℓ - 1) (by have := hseg.1; omega) (by have := hseg.1; omega)
    rw [hend, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by have := hseg.1; omega] at e
    have hb : (31 : Nat) < P := by unfold P; omega
    have ha : ℓ - 1 < P := by omega
    exact (ofNat_inj (a := 31) (b := ℓ - 1) hb ha e).symm
  refine ⟨by omega, fun j hj => ⟨?_, fun x hx => ?_⟩⟩
  · have := hi (s + j) (by omega) (by omega)
    simpa [show 0 + (s + j - s) = j by omega] using this
  · exact const_of (f := fun r => tr.cell tt r x) (s := s) (ℓ := ℓ)
      (fun r h1 h2 => (hw r h1 h2).2.2 x hx) (s + j) (by omega) (by omega)

end

/-! ## Traffic -/

theorem multNat1 (x : Nat) (r : Nat) :
    Interaction.multNat.go tr tt r pub [c x] 0 = if tr.cell tt r x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt r x = 1 <;> simp [h]

theorem multNat2 (x y : Nat) (r : Nat) :
    Interaction.multNat.go tr tt r pub [.mul (c x) (c y)] 0 =
      if tr.cell tt r x * tr.cell tt r y = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_mul, eval_c]
  by_cases h : tr.cell tt r x * tr.cell tt r y = 1 <;> simp [h]

theorem rowT (r : Nat) (b : Nat) (s : Bool) :
    rowTraffic Uniq.interactions tr tt r pub b s =
      (if b = B_DIGS ∧ s = false ∧ tr.cell tt r act = 1 then
        [[tr.cell tt r eid, tr.cell tt r tau, tr.cell tt r i, tr.cell tt r bb]] else []) ++
      (if b = B_DUP ∧ s = true ∧ tr.cell tt r sf * tr.cell tt r eq = 1 then
        [[tr.cell tt r eid, tr.cell tt r peid]] else []) := by
  simp only [rowTraffic, Uniq.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, multNat2, Interaction.msgVal, List.map_cons,
    List.map_nil, eval_c]
  by_cases h1 : B_DIGS = b <;> by_cases h1' : B_DUP = b <;> by_cases h2 : s = false <;>
    by_cases h3 : tr.cell tt r act = 1 <;> by_cases h4 : tr.cell tt r sf * tr.cell tt r eq = 1 <;>
    simp_all [eq_comm, B_DIGS, B_DUP]

/-- The view: one entry per segment. -/
def entriesOf (tr : Trace Fp) (tt : Nat) (segs : List (Nat × Nat)) : List UniqE :=
  segs.map fun p => UniqE.mk (tr.cell tt p.1 eid).toNat (tr.cell tt p.1 peid).toNat
    (tr.cell tt p.1 tau).toNat (tr.cell tt p.1 st).toNat (tr.cell tt p.1 eq).toNat
    ((List.range 32).map fun j => (tr.cell tt (p.1 + j) bb).toNat)

theorem toNat_bool {a : Fp} (h : a = 0 ∨ a = 1) : a.toNat = 0 ∨ a.toNat = 1 := by
  rcases h with rfl | rfl <;> decide

theorem filter_map_flatMap {α β : Type} (q : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter q).map f = l.flatMap fun a => if q a then [f a] else []
  | [] => rfl
  | a :: l => by
    by_cases h : q a = true
    · simp [List.filter_cons, h, filter_map_flatMap q f l]
    · simp [List.filter_cons, h, filter_map_flatMap q f l]

theorem traffic (hL : TableLocal Uniq.table tr tt pub) (segs : List (Nat × Nat))
    (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ tr.height tt)
    (hall : ∀ p ∈ segs, IsSeg (isOne tr tt act) (isOne tr tt sf) (isOne tr tt sl) p.1 p.2)
    (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt act r = false) :
    TableTraffic Uniq.interactions tr tt pub (uniqTraffic (entriesOf tr tt segs)) := by
  intro b m
  rw [tableBusCount_eq, tableBusCount_eq]
  have hsplit : ∀ (sd : Bool), (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Uniq.interactions tr tt r pub b sd) =
      segs.flatMap (fun p => (List.range' p.1 p.2).flatMap
        (fun r => rowTraffic Uniq.interactions tr tt r pub b sd)) := by
    intro sd
    have e1 : List.range (tr.height tt) =
        List.range' 0 (segEnd 0 segs - 0) ++ List.range' (segEnd 0 segs) (tr.height tt - segEnd 0 segs) := by
      rw [List.range_eq_range', Nat.sub_zero]; exact range'_split _ _ hend
    rw [e1, List.flatMap_append, range'_segs segs 0 hc, List.flatMap_assoc,
      flatMap_range'_nil _ _ _ (fun j hj => by
        rw [rowT]
        have hpj := hpad (segEnd 0 segs + j) (by omega) (by omega)
        have h0 := zero_of_not_one hL (by omega) (by simp [boolList]) hpj
        have hsf0 : tr.cell tt (segEnd 0 segs + j) sf = 0 := by
          rcases isBool hL (r := segEnd 0 segs + j) (by omega) (x := sf) (by simp [boolList]) with h | h
          · exact h
          · have := first_act hL (by omega) h; rw [h0] at this; exact absurd this (by decide)
        simp only [h0, hsf0]; grind), List.append_nil]
  -- per segment facts
  have hfacts : ∀ p ∈ segs, p.2 = 32 ∧ p.1 + 32 ≤ tr.height tt ∧
      (∀ j, j < 32 → tr.cell tt (p.1 + j) act = 1 ∧ tr.cell tt (p.1 + j) i = ((j : Nat) : Fp) ∧
        (∀ x ∈ segConst, tr.cell tt (p.1 + j) x = tr.cell tt p.1 x) ∧
        tr.cell tt (p.1 + j) sf = (if j = 0 then 1 else 0)) := by
    intro p hp
    have hH : p.1 + p.2 ≤ tr.height tt := by have := seg_le_end segs 0 hc p hp; omega
    obtain ⟨h32, hcol⟩ := seg32 hL (hall p hp) hH
    refine ⟨h32, by omega, fun j hj => ⟨?_, (hcol j (by omega)).1, (hcol j (by omega)).2, ?_⟩⟩
    · have := (hall p hp).2.2.2.1 (p.1 + j) (by omega) (by omega); simpa [isOne] using this
    · by_cases hj0 : j = 0
      · subst hj0; have := (hall p hp).2.1; simpa [isOne] using this
      · have := (hall p hp).2.2.2.2.1 (p.1 + j) (by omega) (by omega)
        simp only [if_neg hj0]
        exact zero_of_not_one hL (by omega) (by simp [boolList]) this
  have hDU : B_DIGS ≠ B_DUP := by decide
  by_cases hbD : b = B_DIGS
  · subst hbD
    have hseg : ∀ p ∈ segs, ∀ (sd : Bool), (List.range' p.1 p.2).flatMap
        (fun r => rowTraffic Uniq.interactions tr tt r pub B_DIGS sd) =
        if sd = false then (List.range 32).map
          (fun j => [tr.cell tt p.1 eid, tr.cell tt p.1 tau, ((j : Nat) : Fp), tr.cell tt (p.1 + j) bb])
        else [] := by
      intro p hp sd
      obtain ⟨h32, -, hrow⟩ := hfacts p hp
      rw [h32]
      split
      · rename_i hsd
        apply flatMap_range'_single
        intro j hj
        obtain ⟨ha, hi, hk, -⟩ := hrow j hj
        rw [rowT, if_pos ⟨rfl, hsd, ha⟩, if_neg (fun h => hDU h.1), List.append_nil, hi,
          hk eid (by simp [segConst]), hk tau (by simp [segConst])]
      · rename_i hsd
        apply flatMap_range'_nil
        intro j hj
        rw [rowT, if_neg (fun h => hsd h.2.1), if_neg (fun h => hDU h.1)]; rfl
    constructor
    · rw [hsplit, flatMap_segs segs _ _ (fun p hp => (hseg p hp true))]
      simp [uniqTraffic, uniqSends, hDU, flatMap_nil_fun]
    · rw [hsplit, flatMap_segs segs _ _ (fun p hp => (hseg p hp false))]
      simp only [uniqTraffic, uniqRecvs, entriesOf, if_true, List.flatMap_map, List.map_flatMap,
        List.map_map]
      congr 1
      apply flatMap_segs
      intro p hp
      simp [Function.comp, Msg.toFp, Fp.ofNat_toNat]
      intro a ha
      rw [List.getElem?_range ha]
      simp [Fp.ofNat_toNat, natCast_eq]
  · by_cases hbU : b = B_DUP
    · subst hbU
      have hseg : ∀ p ∈ segs, ∀ (sd : Bool), (List.range' p.1 p.2).flatMap
          (fun r => rowTraffic Uniq.interactions tr tt r pub B_DUP sd) =
          if sd = true ∧ tr.cell tt p.1 eq = 1 then [[tr.cell tt p.1 eid, tr.cell tt p.1 peid]] else [] := by
        intro p hp sd
        obtain ⟨h32, -, hrow⟩ := hfacts p hp
        rw [h32, List.range'_succ, List.flatMap_cons,
          flatMap_range'_nil _ _ _ (fun j hj => by
            obtain ⟨-, -, -, hsf⟩ := hrow (j + 1) (by omega)
            rw [rowT, if_neg (fun h => hDU h.1.symm), show p.1 + 1 + j = p.1 + (j + 1) by omega, hsf]
            have e0 : ¬ (0 : Fp) * tr.cell tt (p.1 + (j + 1)) eq = 1 := by grind
            simp [e0])]
        obtain ⟨-, -, -, hsf0⟩ := hrow 0 (by omega)
        rw [List.append_nil, rowT, if_neg (fun h => hDU h.1.symm)]
        simp only [Nat.add_zero] at hsf0
        rw [hsf0]
        have e1 : (1 : Fp) * tr.cell tt p.1 eq = tr.cell tt p.1 eq := by grind
        simp only [List.nil_append, true_and, if_true, ite_true, e1]
      constructor
      · rw [hsplit, flatMap_segs segs _ _ (fun p hp => (hseg p hp true))]
        simp only [uniqTraffic, uniqSends, if_true, entriesOf, filter_map_flatMap, List.flatMap_map,
          List.map_flatMap]
        congr 1
        apply flatMap_segs
        intro p hp
        simp only [true_and, beq_iff_eq]
        have hb := isBool hL (r := p.1) (by have := (hfacts p hp).2.1; omega) (x := eq) (by simp [boolList])
        have t0 : (0 : Fp).toNat = 0 := rfl
        have t1 : (1 : Fp).toNat = 1 := rfl
        rcases hb with h | h <;> simp [h, Msg.toFp, Fp.ofNat_toNat, t0, t1]
      · rw [hsplit, flatMap_segs segs _ _ (fun p hp => (hseg p hp false))]
        simp [uniqTraffic, uniqRecvs, hDU.symm, flatMap_nil_fun]
    · have hrow0 : ∀ (sd : Bool) r, rowTraffic Uniq.interactions tr tt r pub b sd = [] := by
        intro sd r; rw [rowT, if_neg (fun h => hbD h.1), if_neg (fun h => hbU h.1)]; rfl
      simp only [hrow0, flatMap_nil_fun, List.count_nil]
      simp [uniqTraffic, uniqSends, uniqRecvs, hbD, hbU]


theorem delayK (hL : TableLocal Uniq.table tr tt pub) :
    ∀ k, k < 32 → ∀ r, k + 1 ≤ r → r < tr.height tt →
      (∀ q, r - 1 - k ≤ q → q < r → tr.cell tt q act = 1) →
      tr.cell tt r (d k) = tr.cell tt (r - 1 - k) bb := by
  intro k
  induction k with
  | zero =>
    intro _ r h1 h2 ha
    have := (delay hL (r := r - 1) (by omega) (ha (r - 1) (by omega) (by omega))).1
    rwa [show r - 1 + 1 = r by omega] at this
  | succ k ih =>
    intro hk r h1 h2 ha
    have := (delay hL (r := r - 1) (by omega) (ha (r - 1) (by omega) (by omega))).2 k (by omega)
    rw [show r - 1 + 1 = r by omega] at this
    rw [this, ih (by omega) (r - 1) (by omega) (by omega) (fun q hq1 hq2 => ha q (by omega) (by omega))]
    congr 1; omega

theorem dbit_bool (hL : TableLocal Uniq.table tr tt pub) {r : Nat} (hr : r < tr.height tt) :
    ∀ b, b < 8 → tr.cell tt r (dbit (0 + b)) = 0 ∨ tr.cell tt r (dbit (0 + b)) = 1 :=
  fun b hb => isBool hL hr (List.mem_append_right _ (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, by simp⟩))

theorem le256_inj : ∀ (a b : List Nat), a.length = b.length → (∀ y ∈ a, y < 256) → (∀ y ∈ b, y < 256) →
    le256 a = le256 b → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | x :: a, y :: b, h, ha, hb, he => by
    simp only [le256] at he
    have hx := ha x (by simp)
    have hy := hb y (by simp)
    have h1 : x = y := by omega
    have h2 : le256 a = le256 b := by omega
    rw [h1, le256_inj a b (by simpa using h) (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz])) h2]

/-- The link between consecutive entries. -/
theorem linkFacts (hL : TableLocal Uniq.table tr tt pub) (segs : List (Nat × Nat))
    (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ tr.height tt)
    (hall : ∀ p ∈ segs, IsSeg (isOne tr tt act) (isOne tr tt sf) (isOne tr tt sl) p.1 p.2) :
    UniqWf (entriesOf tr tt segs) := by
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  have hlen : ∀ p ∈ segs, p.2 = 32 := fun p hp =>
    (seg32 hL (hall p hp) (by have := seg_le_end segs 0 hc p hp; omega)).1
  have t0 : (0 : Fp).toNat = 0 := rfl
  have t1 : (1 : Fp).toNat = 1 := rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun e he => ?_, fun t ht => ?_⟩
  · simp only [entriesOf, List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    simp
  · simp only [entriesOf, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hr : p.1 < tr.height tt := by
      have := seg_le_end segs 0 hc p hp; have := (hall p hp).1; omega
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, ?_, ?_, fun y hy => ?_⟩
    · rcases isBool hL hr (x := st) (by simp [boolList]) with h | h <;> simp [h, t0, t1]
    · rcases isBool hL hr (x := eq) (by simp [boolList]) with h | h <;> simp [h, t0, t1]
    · simp only [List.mem_map] at hy; obtain ⟨j, -, rfl⟩ := hy; exact Fp.toNat_lt _
  · -- the first entry: ft = 1 on row 0
    cases segs with
    | nil => simp [entriesOf] at he
    | cons p rest =>
      simp only [entriesOf, List.map_cons, List.head?_cons, Option.some.injEq] at he
      subst he
      have hp0 : p.1 = 0 := hc.1
      have h0 : 0 < tr.height tt := by
        have := seg_le_end (p :: rest) 0 hc p (by simp); have := (hall p (by simp)).1; omega
      have hft := (row0 hL h0).2
      have := (rowFacts hL h0).1
      rw [hft] at this
      have heq : tr.cell tt 0 eq = 0 := by grind
      simp [hp0, heq, t0]
  · simp only [entriesOf, List.length_map] at ht
    simp only [entriesOf, List.getElem_map]
    have hp0 : segs[t] ∈ segs := List.getElem_mem (by omega)
    have hp1 : segs[t + 1] ∈ segs := List.getElem_mem ht
    have hs1 := consec_get segs 0 hc t ht
    rw [hlen _ hp0] at hs1
    have hb0 := seg_le_end segs 0 hc _ hp1
    rw [hs1, hlen _ hp1] at hb0
    have hseg0 := hall _ hp0
    have hseg1 := hall _ hp1
    rw [hlen _ hp0] at hseg0
    rw [hs1, hlen _ hp1] at hseg1
    obtain ⟨-, hcol0⟩ := seg32 hL (hall _ hp0) (by rw [hlen _ hp0]; omega)
    obtain ⟨-, hcol1⟩ := seg32 hL (hall _ hp1) (by rw [hlen _ hp1]; omega)
    rw [hlen _ hp1, hs1] at hcol1
    rw [hlen _ hp0] at hcol0
    rw [hs1]
    generalize hs : segs[t].1 = s at hs1 hb0 hseg0 hseg1 hcol1 hcol0
    have hact : ∀ q, s ≤ q → q < s + 64 → tr.cell tt q act = 1 := by
      intro q h1 h2
      rcases Nat.lt_or_ge q (s + 32) with h | h
      · have := hseg0.2.2.2.1 q h1 (by omega); simpa [isOne] using this
      · have := hseg1.2.2.2.1 q (by omega) (by omega); simpa [isOne] using this
    have hsl0 : tr.cell tt (s + 31) sl = 1 := by have := hseg0.2.2.1; simpa [isOne] using this
    obtain ⟨hsf1, hft1, hpe, hta⟩ := nextSeg hL (r := s + 31) (by omega) hsl0 (hact _ (by omega) (by omega))
    rw [show s + 31 + 1 = s + 32 by omega] at hsf1 hft1 hpe hta
    have hk0 : ∀ x ∈ segConst, tr.cell tt (s + 31) x = tr.cell tt s x := (hcol0 31 (by omega)).2
    rw [hk0 eid (by simp [segConst])] at hpe
    rw [hk0 tau (by simp [segConst])] at hta
    have hr1 : s + 32 < tr.height tt := by omega
    have hbst := isBool hL hr1 (x := st) (by simp [boolList])
    have hbeq := isBool hL hr1 (x := eq) (by simp [boolList])
    obtain ⟨_, hes, hed⟩ := rowFacts hL hr1
    -- the carry chain for st = 0
    have chain : tr.cell tt (s + 32) st = 0 →
        le256 ((List.range 32).map fun j => (tr.cell tt (s + 32 + j) bb).toNat) =
          le256 ((List.range 32).map fun j => (tr.cell tt (s + j) bb).toNat) +
          le256 ((List.range 32).map fun j =>
            bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8) +
          (tr.cell tt (s + 32) cin).toNat ∨
        ¬ ((∀ j, j < 32 → (tr.cell tt (s + 32 + j) bb).toNat < 256) ∧
           (∀ j, j < 32 → (tr.cell tt (s + j) bb).toNat < 256)) := by
      intro hst0
      by_cases hbytes : (∀ j, j < 32 → (tr.cell tt (s + 32 + j) bb).toNat < 256) ∧
           (∀ j, j < 32 → (tr.cell tt (s + j) bb).toNat < 256)
      · left
        obtain ⟨hB, hD⟩ := hbytes
        let ci : Nat → Nat := fun j => if j < 32 then cv tr tt (s + 32 + j) cin else 0
        have hcc : ∀ j, j < 32 → (tr.cell tt (s + 32 + j) bb).toNat + 256 * ci (j + 1) =
            (tr.cell tt (s + j) bb).toNat + bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8 + ci j := by
          intro j hj
          have hr : s + 32 + j < tr.height tt := by omega
          have hk1 : ∀ x ∈ segConst, tr.cell tt (s + 32 + j) x = tr.cell tt (s + 32) x := (hcol1 j hj).2
          have hftj : tr.cell tt (s + 32 + j) ft = 0 := by rw [hk1 ft (by simp [segConst])]; exact hft1
          have hstj : tr.cell tt (s + 32 + j) st = 0 := by rw [hk1 st (by simp [segConst])]; exact hst0
          have e := chainEq hL hr (hact _ (by omega) (by omega)) hftj hstj
          have hd31 := delayK hL 31 (by omega) (s + 32 + j) (by omega) hr
            (fun q h1 h2 => hact q (by omega) (by omega))
          rw [show diffE = bits (fun j => c (dbit j)) 0 8 from rfl] at e
          rw [hd31, show s + 32 + j - 1 - 31 = s + j by omega,
            eval_bits tr tt (s + 32 + j) pub dbit 0 8 (dbit_bool hL hr)] at e
          have hco : (tr.cell tt (s + 32 + j) cout).toNat = ci (j + 1) := by
            by_cases hj' : j + 1 < 32
            · have hw := within hL (r := s + 32 + j) (by omega) (hact _ (by omega) (by omega))
                (by
                  rcases isBool hL hr (x := sl) (by simp [boolList]) with h | h
                  · exact h
                  · exfalso
                    have := hseg1.2.2.2.2.2 (s + 32 + j) (by omega) (by omega)
                    simp [isOne, h] at this)
              simp only [ci, if_pos hj', cv]
              rw [show s + 32 + (j + 1) = s + 32 + j + 1 by omega, hw.2.1]
            · have hj31 : j = 31 := by omega
              subst hj31
              have hsl1 : tr.cell tt (s + 32 + 31) sl = 1 := by
                have := hseg1.2.2.1
                simpa [isOne, show s + 32 + 32 - 1 = s + 32 + 31 by omega] using this
              rw [((segFields hL hr).2 hsl1).2]
              simp [ci]; rfl
          have hcib : ci j ≤ 1 := by
            simp only [ci, if_pos hj]; exact cv_bool (isBool hL hr (by simp [boolList]))
          have hcob : (tr.cell tt (s + 32 + j) cout).toNat ≤ 1 := cv_bool (isBool hL hr (by simp [boolList]))
          have hF : bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8 < 256 :=
            bitsVal_lt _ _ _ (fun b hb => cv_bool (dbit_bool hL hr b hb))
          have hBj := hB j hj
          have hDj := hD j hj
          rw [← hco]
          apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
          rw [natCast_add, natCast_mul, natCast_add, natCast_add]
          simp only [ci, if_pos hj, cv, natCast_eq, Fp.ofNat_toNat] at e ⊢
          exact e
        have key := carry_chain ((List.range 32).map fun j => (tr.cell tt (s + 32 + j) bb).toNat)
          ((List.range 32).map fun j => (tr.cell tt (s + j) bb).toNat)
          ((List.range 32).map fun j => bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8) ci
          (by simp) (by simp) (fun j hj => by simp at hj; simpa [hj] using hcc j hj)
        simp only [List.length_map, List.length_range, ci, Nat.lt_irrefl, if_false, Nat.mul_zero,
          Nat.add_zero, show (0 : Nat) < 32 by omega, if_true, cv] at key
        exact key
      · exact Or.inr hbytes
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hpe]
    · rw [hta]; exact Fp.toNat_add _ _
    · intro heq1
      have heqF : tr.cell tt (s + 32) eq = 1 := by
        rcases hbeq with h | h
        · rw [h] at heq1; simp [t0] at heq1
        · exact h
      have hst0 : tr.cell tt (s + 32) st = 0 := by rw [heqF] at hes; grind
      refine ⟨by simp [hst0, t0], fun hbytes => ?_⟩
      have hB : ∀ j, j < 32 → (tr.cell tt (s + 32 + j) bb).toNat < 256 := fun j hj =>
        hbytes _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
      have hD : ∀ j, j < 32 → (tr.cell tt (s + j) bb).toNat < 256 := fun j hj =>
        hbytes _ (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
      rcases chain hst0 with key | key
      · -- eq: no difference bytes, carry-in 0
        have hF0 : ∀ j, j < 32 → bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8 = 0 := by
          intro j hj
          have hr : s + 32 + j < tr.height tt := by omega
          have hk1 : ∀ x ∈ segConst, tr.cell tt (s + 32 + j) x = tr.cell tt (s + 32) x := (hcol1 j hj).2
          have h3 := (rowFacts hL hr).2.2
          rw [hk1 eq (by simp [segConst]), heqF] at h3
          rw [show diffE = bits (fun j => c (dbit j)) 0 8 from rfl,
            eval_bits tr tt (s + 32 + j) pub dbit 0 8 (dbit_bool hL hr)] at h3
          have hF : bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8 < 256 :=
            bitsVal_lt _ _ _ (fun b hb => cv_bool (dbit_bool hL hr b hb))
          have h3' : ((bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8 : Nat) : Fp) = ((0 : Nat) : Fp) := by
            have : (1 : Fp) * _ = 0 := h3; grind
          exact ofNat_inj (by unfold P; omega) (by unfold P; omega) h3'
        have hle0 : le256 ((List.range 32).map fun j => bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8) = 0 := by
          have : ((List.range 32).map fun j => bitsVal (fun b => cv tr tt (s + 32 + j) (dbit b)) 0 8) =
              (List.range 32).map fun _ => 0 := by
            apply List.map_congr_left; intro j hj; exact hF0 j (List.mem_range.1 hj)
          rw [this]; decide
        have hcin : (tr.cell tt (s + 32) cin).toNat = 0 := by
          have := ((segFields hL hr1).1 hsf1).2
          rw [heqF] at this
          have : tr.cell tt (s + 32) cin = 0 := by rw [this]; grind
          rw [this]; rfl
        rw [hle0, hcin] at key
        apply le256_inj _ _ (by simp) (fun y hy => by
            simp only [List.mem_map, List.mem_range] at hy; obtain ⟨j, hj, rfl⟩ := hy; exact hB j hj)
          (fun y hy => by
            simp only [List.mem_map, List.mem_range] at hy; obtain ⟨j, hj, rfl⟩ := hy; exact hD j hj)
        simpa [show (0 : Nat) = 0 from rfl] using key
      · exact absurd ⟨hB, hD⟩ key
    · intro heq0 hst0 hbytes
      have hB : ∀ j, j < 32 → (tr.cell tt (s + 32 + j) bb).toNat < 256 := fun j hj =>
        hbytes _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
      have hD : ∀ j, j < 32 → (tr.cell tt (s + j) bb).toNat < 256 := fun j hj =>
        hbytes _ (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
      have heqF : tr.cell tt (s + 32) eq = 0 := by
        rcases hbeq with h | h
        · exact h
        · rw [h] at heq0; simp [t1] at heq0
      have hstF : tr.cell tt (s + 32) st = 0 := by
        rcases hbst with h | h
        · exact h
        · rw [h] at hst0; simp [t1] at hst0
      rcases chain hstF with key | key
      · have hcin : (tr.cell tt (s + 32) cin).toNat = 1 := by
          have := ((segFields hL hr1).1 hsf1).2
          rw [heqF] at this
          have : tr.cell tt (s + 32) cin = 1 := by rw [this]; grind
          rw [this]; rfl
        rw [hcin] at key
        omega
      · exact absurd ⟨hB, hD⟩ key

end ZkFormal.NearV3.UniqProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Near

/-- **The `uniqV3` view.** -/
theorem uniq_view : UniqViewStmt := by
  intro tr pub t hL
  have hpos : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (UniqProof.segFacts hL) hpos
  exact ⟨UniqProof.entriesOf tr t segs, UniqProof.linkFacts hL segs hc hend hall,
    UniqProof.traffic hL segs hc hend hall hpad⟩

end ZkFormal.NearV3
