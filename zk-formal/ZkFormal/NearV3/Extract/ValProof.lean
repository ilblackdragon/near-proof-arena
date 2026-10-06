import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Tables.Val

/-!
# ZkFormal.NearV3.Extract.ValProof — the `valV3` view (`ValViewStmt`, `val_view`)

One `ValE` per value-record segment (`vf … vl`), then the `SUM` row.  An empty value
(`vz`) is one row whose byte is `0` and which emits no byte; its `ENT` message is the marker
`(eid, 0, 0, 0)`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure ValE where
  vid : Nat
  len : Nat
  vz : Bool
  dup : Bool
  hd : Bool
  repE : Nat
  bytes : List Nat
  deriving Repr, Inhabited

structure ValWf (es : List ValE) : Prop where
  shape : ∀ e ∈ es, (e.vz = true → e.len = 0 ∧ e.bytes = []) ∧ (e.vz = false → e.bytes.length = e.len ∧ 0 < e.len)
  canon : ∀ e ∈ es, e.vid < P ∧ e.len < P ∧ e.repE < P ∧ ∀ x ∈ e.bytes, x < P
  /-- consecutive ids -/
  ids : ∀ t (ht : t + 1 < es.length), es[t + 1].vid = (es[t].vid + 1) % P
  /-- rows -/
  rows : (es.map fun e => if e.vz then 1 else e.len).sum + 1 ≤ 2 ^ 22

def eidV (e : ValE) : Nat := msgId K_VPRE e.vid

/-- `ENT` payloads `(len, pos, byte)` of a record. -/
def ValE.entRows (e : ValE) : List Msg :=
  if e.vz then [[0, 0, 0]] else (List.range e.len).map fun p => [e.len, p, e.bytes.getD p 0]

def valSends (es : List ValE) (b : Nat) : List Msg :=
  if b = B_BYTES then es.flatMap fun e => if e.vz then [] else emitAt (eidV e) 0 e.bytes
  else if b = B_ENT then es.flatMap fun e => if e.hd then e.entRows.map (eidV e :: ·) else []
  else if b = B_SIZE then [[1, ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum]]
  else []

def valRecvs (es : List ValE) (b : Nat) : List Msg :=
  if b = B_VBYTES then es.flatMap fun e => if e.vz then [] else
    (List.range e.bytes.length).map fun p => [e.vid, p, e.bytes.getD p 0]
  else if b = B_VPARENT then es.map fun e => [e.vid, e.len]
  else if b = B_DUP then es.flatMap fun e => if e.dup then [[eidV e, e.repE]] else []
  else if b = B_ENT then es.flatMap fun e => if e.dup then e.entRows.map (e.repE :: ·) else []
  else []

def valTraffic (es : List ValE) : Traffic := ⟨valSends es, valRecvs es⟩

/-- **The `valV3` view statement.** -/
def ValViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal ValV3.table tr t pub →
    ∃ es, ValWf es ∧ TableTraffic ValV3.interactions tr t pub (valTraffic es)

end ZkFormal.NearV3

namespace ZkFormal.NearV3.ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem con (hL : TableLocal ValV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ ValV3.constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

def bools : List Nat := [act, vf, vl, vz, dup, hd, sumr, gb, gdu]

theorem isBool (hL : TableLocal ValV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ bools) : tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold ValV3.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx)))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem mem_a {e : Expr} (h : e ∈ ([ sub (c gb) (.mul (c act) (Dsl.not (c vz))), sub (c gdu) (.mul (c vf) (c dup)),
    .mul (c dup) (Dsl.not (c act)), .mul (c hd) (Dsl.not (c act)) ] : List Expr)) : e ∈ ValV3.constraints := by
  unfold ValV3.constraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))

theorem mem_b {e : Expr} (h : e ∈ ([ .mul (c vf) (Dsl.not (c act)), .mul (c vl) (Dsl.not (c act)),
    .mul (c act) (c sumr),
    .mul .isFirst (sub (.add (c act) (c sumr)) (k 1)), .mul .isFirst (sub (c act) (c vf)),
    .mul .isFirst (c sz),
    .mul .isLast (c act),
    .mul (c vf) (c pos),
    .mul (c vz) (Dsl.not (c vf)), .mul (c vz) (Dsl.not (c vl)), .mul (c vz) (c len), .mul (c vz) (c b),
    .mul (.mul (c vl) (Dsl.not (c vz))) (sub (.add (c pos) (k 1)) (c len)),
    mul3 (c act) (Dsl.not (c vl)) (Dsl.not (n act)),
    mul3 (c act) (Dsl.not (c vl)) (n vf),
    mul3 (c act) (Dsl.not (c vl)) (sub (n pos) (.add (c pos) (k 1))) ] : List Expr)) :
    e ∈ ValV3.constraints := by
  unfold ValV3.constraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_c {e : Expr} (h : e ∈ ([ .mul (c vl) (sub (k 1) (.add (n act) (n sumr))),
    mul3 (c vl) (n act) (Dsl.not (n vf)),
    mul3 (c vl) (n act) (sub (n vid) (.add (c vid) (k 1))),
    mul3 .isTransition (c sumr) (n act), mul3 .isTransition (c sumr) (n sumr),
    mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n act),
    mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n sumr),
    .mul .isTransition (sub (n sz) (.add (c sz) (mul3 (c act) (Dsl.not (c vz)) (Dsl.not (c dup))))) ] : List Expr)) :
    e ∈ ValV3.constraints := by
  unfold ValV3.constraints; exact List.mem_append_right _ h

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem zero_of_not_one (hL : TableLocal ValV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {x : Nat} (hx : x ∈ bools) (h : isOne tr tt x r = false) : tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

section
variable (hL : TableLocal ValV3.table tr tt pub)
include hL

theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r gb = tr.cell tt r act * (1 - tr.cell tt r vz) ∧
    tr.cell tt r gdu = tr.cell tt r vf * tr.cell tt r dup ∧
    (tr.cell tt r act = 0 → tr.cell tt r dup = 0 ∧ tr.cell tt r hd = 0 ∧ tr.cell tt r vf = 0 ∧
      tr.cell tt r vl = 0) ∧
    tr.cell tt r act * tr.cell tt r sumr = 0 ∧
    (tr.cell tt r vf = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r pos = 0) ∧
    (tr.cell tt r vl = 1 → tr.cell tt r act = 1) ∧
    (tr.cell tt r vz = 1 → tr.cell tt r vf = 1 ∧ tr.cell tt r vl = 1 ∧ tr.cell tt r len = 0 ∧
      tr.cell tt r b = 0) ∧
    (tr.cell tt r vl = 1 → tr.cell tt r vz = 0 → tr.cell tt r pos + 1 = tr.cell tt r len) := by
  have a1 := con hL hr (e := sub (c gb) (.mul (c act) (Dsl.not (c vz)))) (mem_a (by simp))
  have a2 := con hL hr (e := sub (c gdu) (.mul (c vf) (c dup))) (mem_a (by simp))
  have a3 := con hL hr (e := .mul (c dup) (Dsl.not (c act))) (mem_a (by simp))
  have a4 := con hL hr (e := .mul (c hd) (Dsl.not (c act))) (mem_a (by simp))
  have b1 := con hL hr (e := .mul (c vf) (Dsl.not (c act))) (mem_b (by simp))
  have b2 := con hL hr (e := .mul (c vl) (Dsl.not (c act))) (mem_b (by simp))
  have b3 := con hL hr (e := .mul (c act) (c sumr)) (mem_b (by simp))
  have b4 := con hL hr (e := .mul (c vf) (c pos)) (mem_b (by simp))
  have b5 := con hL hr (e := .mul (c vz) (Dsl.not (c vf))) (mem_b (by simp))
  have b6 := con hL hr (e := .mul (c vz) (Dsl.not (c vl))) (mem_b (by simp))
  have b7 := con hL hr (e := .mul (c vz) (c len)) (mem_b (by simp))
  have b8 := con hL hr (e := .mul (c vz) (c b)) (mem_b (by simp))
  have b9 := con hL hr (e := .mul (.mul (c vl) (Dsl.not (c vz))) (sub (.add (c pos) (k 1)) (c len))) (mem_b (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k] at a1 a2 a3 a4 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have hvf := isBool hL hr (x := vf) (by simp [bools])
  have hvl := isBool hL hr (x := vl) (by simp [bools])
  refine ⟨by grind, by grind, fun h => ?_, by grind, fun h => ?_, fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · rw [h] at a3 a4 b1 b2; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h] at b1 b4; exact ⟨by grind, by grind⟩
  · rw [h] at b2; grind
  · rw [h] at b5 b6 b7 b8; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h1, h2] at b9; grind

theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl0 : tr.cell tt r vl = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) vf = 0 ∧ tr.cell tt (r + 1) pos = tr.cell tt r pos + 1 ∧
    ∀ x ∈ valConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c act) (Dsl.not (c vl)) (Dsl.not (n act))) (mem_b (by simp))
  have h2 := con hL hr' (e := mul3 (c act) (Dsl.not (c vl)) (n vf)) (mem_b (by simp))
  have h3 := con hL hr' (e := mul3 (c act) (Dsl.not (c vl)) (sub (n pos) (.add (c pos) (k 1)))) (mem_b (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3
  rw [ha, hl0] at h1 h2 h3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL hr' (e := mul3 (c act) (Dsl.not (c vl)) (sub (n x) (c x))) (by
    unfold ValV3.constraints
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem (f := fun x => mul3 (c act) (Dsl.not (c vl)) (sub (n x) (c x))) hx)))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
  rw [ha, hl0] at h5; grind

theorem afterSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl1 : tr.cell tt r vl = 1) :
    tr.cell tt (r + 1) act + tr.cell tt (r + 1) sumr = 1 ∧
    (tr.cell tt (r + 1) act = 1 → tr.cell tt (r + 1) vf = 1 ∧ tr.cell tt (r + 1) vid = tr.cell tt r vid + 1) := by
  have h1 := con hL (by omega : r < _) (e := .mul (c vl) (sub (k 1) (.add (n act) (n sumr)))) (mem_c (by simp))
  have h2 := con hL (by omega : r < _) (e := mul3 (c vl) (n act) (Dsl.not (n vf))) (mem_c (by simp))
  have h3 := con hL (by omega : r < _) (e := mul3 (c vl) (n act) (sub (n vid) (.add (c vid) (k 1)))) (mem_c (by simp))
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3
  rw [hl1] at h1 h2 h3
  refine ⟨by grind, fun ha => ?_⟩
  rw [ha] at h2 h3; exact ⟨by grind, by grind⟩

theorem padFacts {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 ∧ (tr.cell tt r sumr = 0 → tr.cell tt (r + 1) sumr = 0) ∧
    (tr.cell tt r sumr = 1 → tr.cell tt (r + 1) sumr = 0) := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (c sumr) (n act)) (mem_c (by simp))
  have h2 := con hL (by omega : r < _) (e := mul3 .isTransition (c sumr) (n sumr)) (mem_c (by simp))
  have h3 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n act))
    (mem_c (by simp))
  have h4 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n sumr))
    (mem_c (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_add, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1 h2 h3 h4
  rw [ha] at h3 h4
  have hs := isBool hL (r := r) (by omega) (x := sumr) (by simp [bools])
  rcases hs with hs | hs
  · rw [hs] at h1 h2 h3 h4; exact ⟨by grind, fun _ => by grind, fun h => by grind⟩
  · rw [hs] at h1 h2; exact ⟨by grind, fun h => by grind, fun _ => by grind⟩

theorem szStep {r : Nat} (hr : r + 1 < tr.height tt) :
    tr.cell tt (r + 1) sz = tr.cell tt r sz + tr.cell tt r act * (1 - tr.cell tt r vz) * (1 - tr.cell tt r dup) := by
  have h1 := con hL (by omega : r < _)
    (e := .mul .isTransition (sub (n sz) (.add (c sz) (mul3 (c act) (Dsl.not (c vz)) (Dsl.not (c dup))))))
    (mem_c (by simp))
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  grind

theorem row0 (h0 : 0 < tr.height tt) :
    tr.cell tt 0 act + tr.cell tt 0 sumr = 1 ∧ tr.cell tt 0 act = tr.cell tt 0 vf ∧ tr.cell tt 0 sz = 0 := by
  have h1 := con hL h0 (e := .mul .isFirst (sub (.add (c act) (c sumr)) (k 1))) (mem_b (by simp))
  have h2 := con hL h0 (e := .mul .isFirst (sub (c act) (c vf))) (mem_b (by simp))
  have h3 := con hL h0 (e := .mul .isFirst (c sz)) (mem_b (by simp))
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k, eval_isFirst, if_pos rfl] at h1 h2 h3
  exact ⟨by grind, by grind, by grind⟩

theorem lastRow (h0 : 0 < tr.height tt) : tr.cell tt (tr.height tt - 1) act = 0 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _) (e := .mul .isLast (c act)) (mem_b (by simp))
  simp only [eval_mul, eval_c, eval_isLast, if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  grind

theorem segFacts (h0act : tr.cell tt 0 act = 1) :
    SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) where
  first_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.2.2.2.1 h).1
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact (rowFacts hL hr).2.2.2.2.2.1 h
  cont r hr ha hl' := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) (by simp [bools]) hl')
    simp [isOne, this.1, this.2.1]
  next r hr hl' ha := by
    simp only [isOne, decide_eq_true_eq] at hl' ha ⊢
    exact ((afterSeg hL hr hl').2 ha).1
  pad r hr ha := by
    have := (padFacts hL hr (zero_of_not_one hL (by omega) (by simp [bools]) ha)).1
    simp [isOne, this]
  start h0 := by
    simp only [isOne, decide_eq_true_eq]
    rw [← (row0 hL h0).2.1, h0act]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢
    rw [lastRow hL h0] at ha; exact absurd ha (by decide)

end

end ZkFormal.NearV3.ValProof

namespace ZkFormal.NearV3.ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem height_le (hL : TableLocal ValV3.table tr tt pub) : tr.height tt ≤ 2 ^ 22 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

/-- Facts about one value-record segment. -/
theorem segInfo (hL : TableLocal ValV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    (∀ j, j < ℓ → tr.cell tt (s + j) act = 1 ∧ tr.cell tt (s + j) pos = ((j : Nat) : Fp) ∧
      (∀ x ∈ valConst, tr.cell tt (s + j) x = tr.cell tt s x) ∧
      tr.cell tt (s + j) vf = (if j = 0 then 1 else 0)) ∧
    ((tr.cell tt s vz = 1 ∧ ℓ = 1 ∧ tr.cell tt s len = 0 ∧ tr.cell tt s b = 0) ∨
     (tr.cell tt s vz = 0 ∧ tr.cell tt s len = ((ℓ : Nat) : Fp))) := by
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  have hpos := hseg.1
  have hsf : tr.cell tt s vf = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hsl : tr.cell tt (s + ℓ - 1) vl = 1 := by have := hseg.2.2.1; simpa [isOne] using this
  have hA : ∀ r, s ≤ r → r < s + ℓ → tr.cell tt r act = 1 := fun r h1 h2 => by
    have := hseg.2.2.2.1 r h1 h2; simpa [isOne] using this
  have hW : ∀ r, s ≤ r → r + 1 < s + ℓ → tr.cell tt r vl = 0 := fun r h1 h2 =>
    zero_of_not_one hL (by omega) (by simp [bools]) (hseg.2.2.2.2.2 r h1 h2)
  have hw : ∀ r, s ≤ r → r + 1 < s + ℓ → _ := fun r h1 h2 =>
    within hL (r := r) (by omega) (hA r h1 (by omega)) (hW r h1 h2)
  have hi := counter_of (f := fun r => tr.cell tt r pos) (s := s) (ℓ := ℓ) (v0 := 0)
    ((rowFacts hL (by omega : s < _)).2.2.2.2.1 hsf).2 (fun r h1 h2 => (hw r h1 h2).2.2.1)
  have hk : ∀ j, j < ℓ → ∀ x ∈ valConst, tr.cell tt (s + j) x = tr.cell tt s x := fun j hj x hx =>
    const_of (f := fun r => tr.cell tt r x) (s := s) (ℓ := ℓ) (fun r h1 h2 => (hw r h1 h2).2.2.2 x hx)
      (s + j) (by omega) (by omega)
  refine ⟨fun j hj => ⟨hA (s + j) (by omega) (by omega), ?_, hk j hj, ?_⟩, ?_⟩
  · have := hi (s + j) (by omega) (by omega); simpa [show 0 + (s + j - s) = j by omega] using this
  · by_cases h0 : j = 0
    · subst h0; simpa using hsf
    · have := hseg.2.2.2.2.1 (s + j) (by omega) (by omega)
      rw [if_neg h0]; exact zero_of_not_one hL (by omega) (by simp [bools]) this
  · rcases isBool hL (r := s) (by omega) (x := vz) (by simp [bools]) with hz | hz
    · right
      refine ⟨hz, ?_⟩
      have hzl : tr.cell tt (s + ℓ - 1) vz = 0 := by
        rw [show s + ℓ - 1 = s + (ℓ - 1) by omega, hk (ℓ - 1) (by omega) vz (by simp [valConst]), hz]
      have e := (rowFacts hL (by omega : s + ℓ - 1 < _)).2.2.2.2.2.2.2 hsl hzl
      have hp := hi (s + ℓ - 1) (by omega) (by omega)
      rw [show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at hp
      have hl2 : tr.cell tt (s + ℓ - 1) len = tr.cell tt s len := by
        rw [show s + ℓ - 1 = s + (ℓ - 1) by omega]; exact hk (ℓ - 1) (by omega) len (by simp [valConst])
      rw [← hl2, ← e, hp]
      have : ((ℓ - 1 : Nat) : Fp) + 1 = (((ℓ - 1) + 1 : Nat) : Fp) := by rw [natCast_add]; rfl
      rw [this]; congr 1; omega
    · left
      obtain ⟨-, hvl, hlen, hb⟩ := (rowFacts hL (by omega : s < _)).2.2.2.2.2.2.1 hz
      refine ⟨hz, ?_, hlen, hb⟩
      rcases Nat.lt_or_ge 1 ℓ with h1 | h1
      · have := hW s (by omega) (by omega)
        rw [hvl] at this; exact absurd this (by decide)
      · omega

end ZkFormal.NearV3.ValProof

namespace ZkFormal.NearV3.ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

def eidF (tr : Trace Fp) (tt q : Nat) : Fp := (K_VPRE : Fp) + 16 * tr.cell tt q vid

theorem rowT (q : Nat) (bb : Nat) (sd : Bool) :
    rowTraffic ValV3.interactions tr tt q pub bb sd =
      (if bb = B_BYTES ∧ sd = true ∧ tr.cell tt q gb = 1 then [[eidF tr tt q, tr.cell tt q pos, tr.cell tt q b]] else []) ++
      (if bb = B_VBYTES ∧ sd = false ∧ tr.cell tt q gb = 1 then [[tr.cell tt q vid, tr.cell tt q pos, tr.cell tt q b]]
        else []) ++
      (if bb = B_VPARENT ∧ sd = false ∧ tr.cell tt q vf = 1 then [[tr.cell tt q vid, tr.cell tt q len]] else []) ++
      (if bb = B_DUP ∧ sd = false ∧ tr.cell tt q gdu = 1 then [[eidF tr tt q, tr.cell tt q repE]] else []) ++
      (if bb = B_ENT ∧ sd = true ∧ tr.cell tt q hd = 1 then
        [[eidF tr tt q, tr.cell tt q len, tr.cell tt q pos, tr.cell tt q b]] else []) ++
      (if bb = B_ENT ∧ sd = false ∧ tr.cell tt q dup = 1 then
        [[tr.cell tt q repE, tr.cell tt q len, tr.cell tt q pos, tr.cell tt q b]] else []) ++
      (if bb = B_SIZE ∧ sd = true ∧ tr.cell tt q sumr = 1 then [[1, tr.cell tt q sz]] else []) := by
  simp only [rowTraffic, ValV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, ValV3.entMsg, List.map_cons,
    List.map_nil, eval_c, eval_k, eval_mid, eidF, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))))) <;> (split <;> split <;> simp_all [eq_comm]) <;> grind

def valOf (tr : Trace Fp) (tt : Nat) (p : Nat × Nat) : ValE :=
  ⟨(tr.cell tt p.1 vid).toNat, (tr.cell tt p.1 len).toNat, decide (tr.cell tt p.1 vz = 1),
    decide (tr.cell tt p.1 dup = 1), decide (tr.cell tt p.1 hd = 1), (tr.cell tt p.1 repE).toNat,
    if tr.cell tt p.1 vz = 1 then [] else (List.range p.2).map fun j => (tr.cell tt (p.1 + j) b).toNat⟩

theorem toFp_eid (x : Fp) : Fp.ofNat (msgId K_VPRE x.toNat) = (K_VPRE : Fp) + 16 * x := by
  unfold msgId
  rw [← natCast_eq, natCast_add, natCast_mul, natCast_eq x.toNat, Fp.ofNat_toNat]; rfl

theorem o0 : Fp.ofNat 0 = 0 := rfl
theorem o1 : Fp.ofNat 1 = 1 := rfl

end ZkFormal.NearV3.ValProof

namespace ZkFormal.NearV3.ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem flatMap_nil' {α β : Type} (l : List α) (f : α → List β) (h : ∀ a ∈ l, f a = []) : l.flatMap f = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Messages of a segment's rows, per bus and side. -/
theorem segTraffic (hL : TableLocal ValV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (bb : Nat) (sd : Bool) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic ValV3.interactions tr tt q pub bb sd) =
      (if bb = B_SIZE then [] else
        ((if sd then valSends [valOf tr tt (s, ℓ)] bb else valRecvs [valOf tr tt (s, ℓ)] bb)).map Msg.toFp) := by
  obtain ⟨hrow, hz⟩ := segInfo hL hseg hH
  have hr : ∀ j, j < ℓ → s + j < tr.height tt := fun j hj => by omega
  have hfacts : ∀ j, j < ℓ → tr.cell tt (s + j) sumr = 0 ∧
      tr.cell tt (s + j) gb = 1 - tr.cell tt s vz ∧
      tr.cell tt (s + j) gdu = (if j = 0 then tr.cell tt s dup else 0) := by
    intro j hj
    obtain ⟨ha, -, hk, hvf⟩ := hrow j hj
    obtain ⟨hgb, hgdu, -, has, -⟩ := rowFacts hL (hr j hj)
    refine ⟨by rw [ha] at has; grind, by rw [hgb, ha, hk vz (by simp [valConst])]; grind, ?_⟩
    rw [hgdu, hvf, hk dup (by simp [valConst])]
    split <;> grind
  have bD : ∀ x : Fp, x = 0 ∨ x = 1 → (Fp.ofNat (if x = 1 then 1 else 0)) = x := by
    intro x hx; rcases hx with rfl | rfl <;> rfl
  have hvzb := isBool hL (r := s) (hr 0 hseg.1) (x := vz) (by simp [bools])
  have hdub := isBool hL (r := s) (hr 0 hseg.1) (x := dup) (by simp [bools])
  have hhdb := isBool hL (r := s) (hr 0 hseg.1) (x := hd) (by simp [bools])
  -- the segment's row messages
  rw [List.range'_eq_map_range, List.flatMap_map]
  have hrowT : ∀ j, j < ℓ → rowTraffic ValV3.interactions tr tt (s + j) pub bb sd =
      (if bb = B_BYTES ∧ sd = true ∧ tr.cell tt s vz = 0 then
        [[eidF tr tt s, ((j : Nat) : Fp), tr.cell tt (s + j) b]] else []) ++
      (if bb = B_VBYTES ∧ sd = false ∧ tr.cell tt s vz = 0 then
        [[tr.cell tt s vid, ((j : Nat) : Fp), tr.cell tt (s + j) b]] else []) ++
      (if bb = B_VPARENT ∧ sd = false ∧ j = 0 then [[tr.cell tt s vid, tr.cell tt s len]] else []) ++
      (if bb = B_DUP ∧ sd = false ∧ j = 0 ∧ tr.cell tt s dup = 1 then [[eidF tr tt s, tr.cell tt s repE]] else []) ++
      (if bb = B_ENT ∧ sd = true ∧ tr.cell tt s hd = 1 then
        [[eidF tr tt s, tr.cell tt s len, ((j : Nat) : Fp), tr.cell tt (s + j) b]] else []) ++
      (if bb = B_ENT ∧ sd = false ∧ tr.cell tt s dup = 1 then
        [[tr.cell tt s repE, tr.cell tt s len, ((j : Nat) : Fp), tr.cell tt (s + j) b]] else []) := by
    intro j hj
    obtain ⟨-, hpos, hk, hvf⟩ := hrow j hj
    obtain ⟨hsum, hgb, hgdu⟩ := hfacts j hj
    rw [rowT, hsum, hgb, hgdu, hvf, hpos]
    simp only [eidF, hk vid (by simp [valConst]), hk len (by simp [valConst]), hk repE (by simp [valConst]),
      hk hd (by simp [valConst]), hk dup (by simp [valConst])]
    have e7 : (if bb = B_SIZE ∧ sd = true ∧ (0 : Fp) = 1 then [[(1 : Fp), tr.cell tt (s + j) sz]] else []) = [] := by
      simp
    rw [e7, List.append_nil]
    have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
      intro a b c d h1 h2; rw [h1, h2]
    refine ap (ap (ap (ap (ap ?_ ?_) ?_) ?_) ?_) ?_
    · have s0 : (1 : Fp) - 0 = 1 := by grind
      have s1 : ¬ ((1 : Fp) - 1 = 1) := by grind
      rcases hvzb with h | h <;> simp [h, s0, s1]
    · have s0 : (1 : Fp) - 0 = 1 := by grind
      have s1 : ¬ ((1 : Fp) - 1 = 1) := by grind
      rcases hvzb with h | h <;> simp [h, s0, s1]
    · by_cases h0 : j = 0 <;> simp [h0]
    · by_cases h0 : j = 0 <;> rcases hdub with h | h <;> simp [h0, h]
    · rfl
    · rfl
  rw [flatMap_congr' (fun j hj => hrowT j (List.mem_range.1 hj))]
  have hℓ := hseg.1
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  have dB : ∀ x y : Nat, x ≠ y → (x = y) = False := fun x y h => by simp [h]
  have hlenN : tr.cell tt s vz = 0 → (tr.cell tt s len).toNat = ℓ := by
    intro h0
    rcases hz with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [h0] at h1; exact absurd h1 (by decide)
    · rw [h2, toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  have hvz1 : tr.cell tt s vz = 1 → ℓ = 1 ∧ tr.cell tt s len = 0 ∧ tr.cell tt s b = 0 := by
    intro h1
    rcases hz with ⟨-, h2, h3, h4⟩ | ⟨h0, -⟩
    · exact ⟨h2, h3, h4⟩
    · rw [h0] at h1; exact absurd h1 (by decide)
  have nZ : ∀ x : Fp, x = 0 → ¬ x = 1 := fun x h e => by rw [h] at e; exact absurd e (by decide)
  by_cases hS : bb = B_SIZE
  · subst hS
    rw [if_pos rfl]
    apply flatMap_nil'; intro j _
    simp [B_SIZE, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT]
  · rw [if_neg hS]
    cases sd
    · -- receives: VBYTES, VPARENT, DUP, ENT
      simp only [valRecvs, valOf, Bool.false_eq_true, and_false, false_and, if_false, and_true,
        List.nil_append, List.append_nil, if_neg (show ¬ (false = true) by decide)]
      by_cases hb1 : bb = B_VBYTES
      · subst hb1
        simp only [if_pos rfl, show B_VBYTES ≠ B_VPARENT by decide, show B_VBYTES ≠ B_DUP by decide,
          show B_VBYTES ≠ B_ENT by decide, false_and, if_false, List.append_nil, true_and,
          List.flatMap_cons, List.flatMap_nil]
        rcases hvzb with h | h
        · simp only [h, if_true, decide_false, Bool.false_eq_true, if_false, nZ 0 rfl, List.length_map,
            List.length_range, List.map_map]
          rw [map_eq_flatMap]
          apply flatMap_congr'; intro j hj
          simp [Msg.toFp, Fp.ofNat_toNat, List.getElem?_range (List.mem_range.1 hj), natCast_eq]
        · simp only [h, fp_one_ne_zero, if_false, decide_true, if_true]
          apply flatMap_nil'; intro j _; rfl
      · by_cases hb2 : bb = B_VPARENT
        · subst hb2
          simp only [if_pos rfl, show B_VPARENT ≠ B_VBYTES by decide, show B_VPARENT ≠ B_DUP by decide,
            show B_VPARENT ≠ B_ENT by decide, false_and, if_false, List.nil_append, List.append_nil, true_and,
            List.map_cons, List.map_nil]
          rw [show ℓ = 1 + (ℓ - 1) by omega, List.range_add, List.flatMap_append]
          simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos rfl]
          rw [flatMap_nil' _ _ (fun j hj => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hj; simp)]
          simp [Msg.toFp, Fp.ofNat_toNat]
        · by_cases hb3 : bb = B_DUP
          · subst hb3
            simp only [if_pos rfl, show B_DUP ≠ B_VBYTES by decide, show B_DUP ≠ B_VPARENT by decide,
              show B_DUP ≠ B_ENT by decide, false_and, if_false, List.nil_append, List.append_nil, true_and,
              List.flatMap_cons, List.flatMap_nil]
            rw [show ℓ = 1 + (ℓ - 1) by omega, List.range_add, List.flatMap_append]
            simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, true_and]
            rw [flatMap_nil' _ _ (fun j hj => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hj; simp)]
            rcases hdub with h | h <;> simp [h, Msg.toFp, Fp.ofNat_toNat, eidV, toFp_eid, eidF]
          · by_cases hb4 : bb = B_ENT
            · subst hb4
              simp only [if_pos rfl, show B_ENT ≠ B_VBYTES by decide, show B_ENT ≠ B_VPARENT by decide,
                show B_ENT ≠ B_DUP by decide, false_and, if_false, List.nil_append, List.append_nil, true_and,
                List.flatMap_cons, List.flatMap_nil]
              rcases hdub with hd0 | hd1
              · simp only [hd0, nZ 0 rfl, if_false, decide_false]
                apply flatMap_nil'; intro j _; rfl
              · simp only [hd1, if_true, decide_true, ValE.entRows]
                rcases hvzb with h | h
                · simp only [h, nZ 0 rfl, decide_false, Bool.false_eq_true, if_false, List.map_map]
                  rw [hlenN h, map_eq_flatMap]
                  apply flatMap_congr'; intro j hj
                  have hj' := List.mem_range.1 hj
                  simp [Msg.toFp, Fp.ofNat_toNat, List.getElem?_range hj', natCast_eq, hlenN h]
                  rw [← hlenN h]; exact (Fp.ofNat_toNat _).symm
                · obtain ⟨h1, h2, h3⟩ := hvz1 h
                  subst h1
                  simp [h, h2, h3, Msg.toFp, Fp.ofNat_toNat, o0, natCast_eq]
            · rw [flatMap_nil' _ _ (fun j _ => by simp [hb1, hb2, hb3, hb4])]
              simp [hb1, hb2, hb3, hb4]
    · -- sends: BYTES, ENT
      simp only [valSends, valOf, and_false, false_and, if_false, and_true, true_and,
        List.nil_append, List.append_nil, if_neg hS]
      by_cases hb1 : bb = B_BYTES
      · subst hb1
        simp only [if_pos rfl, show B_BYTES ≠ B_ENT by decide, false_and, if_false, List.append_nil, true_and,
          List.flatMap_cons, List.flatMap_nil]
        rcases hvzb with h | h
        · simp only [h, if_true, decide_false, Bool.false_eq_true, if_false, nZ 0 rfl, emitAt,
            List.length_map, List.length_range, List.map_map]
          rw [map_eq_flatMap]
          apply flatMap_congr'; intro j hj
          simp [Msg.toFp, Fp.ofNat_toNat, List.getElem?_range (List.mem_range.1 hj), natCast_eq, eidV,
            toFp_eid, eidF]
        · simp only [h, fp_one_ne_zero, if_false, decide_true, if_true]
          apply flatMap_nil'; intro j _; rfl
      · by_cases hb4 : bb = B_ENT
        · subst hb4
          simp only [if_pos rfl, show B_ENT ≠ B_BYTES by decide, false_and, if_false, List.nil_append,
            List.append_nil, true_and, List.flatMap_cons, List.flatMap_nil]
          rcases hhdb with hd0 | hd1
          · simp only [hd0, nZ 0 rfl, if_false, decide_false]
            apply flatMap_nil'; intro j _; rfl
          · simp only [hd1, if_true, decide_true, ValE.entRows]
            rcases hvzb with h | h
            · simp only [h, nZ 0 rfl, decide_false, Bool.false_eq_true, if_false, List.map_map]
              rw [hlenN h, map_eq_flatMap]
              apply flatMap_congr'; intro j hj
              have hj' := List.mem_range.1 hj
              simp [Msg.toFp, Fp.ofNat_toNat, List.getElem?_range hj', natCast_eq, hlenN h, eidV, toFp_eid, eidF]
              rw [← hlenN h]; exact (Fp.ofNat_toNat _).symm
            · obtain ⟨h1, h2, h3⟩ := hvz1 h
              subst h1
              simp [h, h2, h3, Msg.toFp, Fp.ofNat_toNat, o0, eidV, toFp_eid, eidF, natCast_eq]
        · rw [flatMap_nil' _ _ (fun j _ => by simp [hb1, hb4])]
          simp [hb1, hb4]

end ZkFormal.NearV3.ValProof

namespace ZkFormal.NearV3.ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Row weight counted by `sz`. -/
def gw (tr : Trace Fp) (tt q : Nat) : Nat :=
  if tr.cell tt q act = 1 ∧ tr.cell tt q vz = 0 ∧ tr.cell tt q dup = 0 then 1 else 0

theorem sz_sum (hL : TableLocal ValV3.table tr tt pub) (hpos : 0 < tr.height tt) :
    ∀ r, r < tr.height tt → tr.cell tt r sz = ((((List.range r).map (gw tr tt)).sum : Nat) : Fp) := by
  intro r
  induction r with
  | zero => intro _; rw [(row0 hL hpos).2.2]; rfl
  | succ r ih =>
    intro hr
    rw [szStep hL hr, ih (by omega), List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, natCast_add]
    congr 1
    have ha := isBool hL (r := r) (by omega) (x := act) (by simp [bools])
    have hz := isBool hL (r := r) (by omega) (x := vz) (by simp [bools])
    have hd' := isBool hL (r := r) (by omega) (x := dup) (by simp [bools])
    unfold gw
    rcases ha with h1 | h1 <;> rcases hz with h2 | h2 <;> rcases hd' with h3 | h3 <;>
      simp [h1, h2, h3] <;> first | rfl | grind

theorem sum_map_zero' {α : Type} : ∀ (l : List α), (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by simp [sum_map_zero' l]

theorem sum_map_one {α : Type} : ∀ (l : List α), (l.map fun _ => (1 : Nat)).sum = l.length
  | [] => rfl
  | _ :: l => by simp [sum_map_one l]; omega

theorem sum_filter_map {α β : Type} (f : α → Nat) (h : α → β) (g : β → Bool) (len : β → Nat) :
    ∀ (l : List α), (∀ p ∈ l, f p = if g (h p) then len (h p) else 0) →
      (l.map f).sum = (((l.map h).filter g).map len).sum
  | [], _ => rfl
  | p :: l, hf => by
    have ih := sum_filter_map f h g len l (fun q hq => hf q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, hf p (by simp), ih]
    by_cases hg : g (h p) = true <;> simp [hg, List.filter_cons]

theorem sum_flatMap {α : Type} (f : Nat → Nat) (g : α → List Nat) : ∀ (segs : List α),
    ((segs.flatMap g).map f).sum = (segs.map fun p => ((g p).map f).sum).sum
  | [] => rfl
  | p :: r => by simp [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap f g r]

end ZkFormal.NearV3.ValProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ValProof

theorem valSends_flat (es : List ValE) (b : Nat) (hb : b ≠ B_SIZE) :
    valSends es b = es.flatMap fun e => valSends [e] b := by
  unfold valSends
  by_cases h1 : b = B_BYTES
  · simp [h1]
  · by_cases h2 : b = B_ENT
    · simp [h2, show B_ENT ≠ B_BYTES by decide]
    · simp [h1, h2, hb]

theorem valRecvs_flat (es : List ValE) (b : Nat) : valRecvs es b = es.flatMap fun e => valRecvs [e] b := by
  unfold valRecvs
  repeat' split
  all_goals simp [map_eq_flatMap]

/-- **The `valV3` view.** -/
theorem val_view : ValViewStmt := by
  intro tr pub tt hL
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  -- segments (none if row 0 is inactive)
  obtain ⟨segs, hc, hend, hall, hpad⟩ : ∃ segs : List (Nat × Nat), Consec 0 segs ∧
      segEnd 0 segs ≤ tr.height tt ∧
      (∀ p ∈ segs, IsSeg (isOne tr tt ValV3.act) (isOne tr tt ValV3.vf) (isOne tr tt ValV3.vl) p.1 p.2) ∧
      (∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt ValV3.act r = false) := by
    by_cases h0 : tr.cell tt 0 ValV3.act = 1
    · exact segments_of (segFacts hL h0) hpos
    · refine ⟨[], trivial, by simp [segEnd], by simp, fun r _ hr => ?_⟩
      have : ∀ r, r < tr.height tt → tr.cell tt r ValV3.act = 0 := by
        intro r
        induction r with
        | zero =>
          intro _
          rcases isBool hL hpos (x := ValV3.act) (by simp [bools]) with h | h
          · exact h
          · exact absurd h h0
        | succ r ih => intro hr; exact (padFacts hL hr (ih (by omega))).1
      simp [isOne, this r hr]
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hinact : ∀ r, segEnd 0 segs ≤ r → r < tr.height tt → tr.cell tt r ValV3.act = 0 := fun r h1 h2 =>
    zero_of_not_one hL h2 (by simp [bools]) (hpad r h1 h2)
  obtain ⟨A, hA⟩ : ∃ A, A = segEnd 0 segs := ⟨_, rfl⟩
  have hlastSeg : segs ≠ [] → ∃ q ∈ segs, q.1 + q.2 = A := by
    intro hne
    obtain ⟨p, rest, rfl⟩ : ∃ p rest, segs = p :: rest := by
      cases segs with
      | nil => exact absurd rfl hne
      | cons p rest => exact ⟨p, rest, rfl⟩
    exact ⟨(p :: rest)[(p :: rest).length - 1]'(by simp), List.getElem_mem _,
      by rw [hA, segEnd_last (p :: rest) 0 hc (by simp)]⟩
  -- the SUM row is row A
  have hAlt : A < tr.height tt := by
    rcases Nat.lt_or_ge A (tr.height tt) with h | h
    · exact h
    · exfalso
      have hlast := lastRow hL hpos
      by_cases hne : segs = []
      · subst hne; simp [segEnd] at hA; omega
      · obtain ⟨q, hq, hqe⟩ := hlastSeg hne
        have hqa := (hall q hq).2.2.2.1 (q.1 + q.2 - 1) (by have := (hall q hq).1; omega)
          (by have := (hall q hq).1; omega)
        simp only [isOne, decide_eq_true_eq] at hqa
        have : q.1 + q.2 - 1 = tr.height tt - 1 := by have := hH q hq; have := (hall q hq).1; omega
        rw [this, hlast] at hqa; exact absurd hqa (by decide)
  have hsumA : tr.cell tt A ValV3.sumr = 1 := by
    have ha := hinact A (by omega) hAlt
    by_cases hne : segs = []
    · subst hne
      have h0 : A = 0 := by simp [segEnd] at hA; exact hA
      subst h0
      have := (row0 hL hpos).1
      rw [ha] at this; grind
    · obtain ⟨q, hq, hqe⟩ := hlastSeg hne
      have hvl : tr.cell tt (q.1 + q.2 - 1) ValV3.vl = 1 := by
        have := (hall q hq).2.2.1; simpa [isOne] using this
      have e : q.1 + q.2 - 1 + 1 = A := by have := (hall q hq).1; omega
      have := (afterSeg hL (r := q.1 + q.2 - 1) (by omega) hvl).1
      rw [e, ha] at this; grind
  have hsumAfter : ∀ r, A < r → r < tr.height tt → tr.cell tt r ValV3.sumr = 0 := by
    intro r h1 h2
    induction r with
    | zero => omega
    | succ r ih =>
      by_cases hr : r = A
      · subst hr; exact (padFacts hL h2 (hinact _ (by omega) (by omega))).2.2 hsumA
      · exact (padFacts hL h2 (hinact _ (by omega) (by omega))).2.1 (ih (by omega) (by omega))
  -- rows other than the segments and the SUM row carry nothing
  have hrow0 : ∀ bb sd r, A ≤ r → r < tr.height tt → bb ≠ B_SIZE ∨ r ≠ A →
      rowTraffic ValV3.interactions tr tt r pub bb sd = [] := by
    intro bb sd r h1 h2 h3
    have ha := hinact r (by omega) h2
    obtain ⟨hgb, hgdu, hz, -⟩ := rowFacts hL h2
    obtain ⟨hdu, hhd, hvf, -⟩ := hz ha
    have hs : bb ≠ B_SIZE ∨ tr.cell tt r ValV3.sumr = 0 := by
      rcases h3 with h | h
      · exact Or.inl h
      · exact Or.inr (hsumAfter r (by omega) h2)
    rw [rowT, hgb, hgdu, ha, hdu, hhd, hvf]
    have z1 : ∀ x : Fp, ¬ (0 : Fp) * x = 1 := fun x e => by grind
    rcases hs with h | h <;> simp [h, z1]
  -- sums over the segments
  have hsumℓ : (segs.map fun p => p.2).sum = A := by
    have := congrArg List.length (range'_segs segs 0 hc)
    simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at this
    rw [hA, this]
  have hP2 : A < P := by omega
  have hsplit : List.range (tr.height tt) = (segs.flatMap fun p => List.range' p.1 p.2) ++
      ([A] ++ List.range' (A + 1) (tr.height tt - A - 1)) := by
    rw [List.range_eq_range', range'_split A _ (by omega), hA, ← range'_segs segs 0 hc, Nat.sub_zero, ← hA]
    congr 1
    rw [show tr.height tt - A = 1 + (tr.height tt - A - 1) by omega, ← List.range'_append_1]
    simp
  have hrest : ∀ bb sd, (List.range' (A + 1) (tr.height tt - A - 1)).flatMap
      (fun q => rowTraffic ValV3.interactions tr tt q pub bb sd) = [] :=
    fun bb sd => flatMap_nil' _ _ (fun q hq => by
      have := List.mem_range'.1 hq
      exact hrow0 bb sd q (by omega) (by omega) (Or.inr (by omega)))
  have hsegs : ∀ bb sd, (segs.flatMap fun p => List.range' p.1 p.2).flatMap
      (fun q => rowTraffic ValV3.interactions tr tt q pub bb sd) =
      segs.flatMap fun p => if bb = B_SIZE then [] else
        ((if sd then valSends [valOf tr tt p] bb else valRecvs [valOf tr tt p] bb)).map Msg.toFp := by
    intro bb sd
    rw [List.flatMap_assoc]
    exact flatMap_congr' (fun p hp => segTraffic hL (hall p hp) (hH p hp) bb sd)
  -- the SUM value
  have hgw : ∀ p ∈ segs, ((List.range' p.1 p.2).map (gw tr tt)).sum =
      if tr.cell tt p.1 ValV3.vz = 0 ∧ tr.cell tt p.1 ValV3.dup = 0 then p.2 else 0 := by
    intro p hp
    obtain ⟨hrow, -⟩ := segInfo hL (hall p hp) (hH p hp)
    rw [List.range'_eq_map_range, List.map_map]
    have : ∀ j ∈ List.range p.2, (gw tr tt ∘ fun j => p.1 + j) j =
        if tr.cell tt p.1 ValV3.vz = 0 ∧ tr.cell tt p.1 ValV3.dup = 0 then 1 else 0 := by
      intro j hj
      obtain ⟨ha, -, hk, -⟩ := hrow j (List.mem_range.1 hj)
      simp [gw, ha, hk ValV3.vz (by simp [ValV3.valConst]), hk ValV3.dup (by simp [ValV3.valConst])]
    rw [List.map_congr_left this]
    by_cases hcnd : tr.cell tt p.1 ValV3.vz = 0 ∧ tr.cell tt p.1 ValV3.dup = 0
    · simp only [hcnd, and_self, if_true]
      rw [sum_map_one]; simp
    · simp only [hcnd, if_false]; exact sum_map_zero' _
  have hszA : tr.cell tt A ValV3.sz =
      ((((segs.map (valOf tr tt)).filter fun e => !e.vz && !e.dup).map ValE.len).sum : Nat) := by
    rw [sz_sum hL hpos A hAlt, List.range_eq_range', hA, ← Nat.sub_zero (segEnd 0 segs),
      range'_segs segs 0 hc, sum_flatMap]
    congr 1
    rw [List.map_congr_left hgw]
    apply sum_filter_map
    intro p hp
    obtain ⟨-, hz⟩ := segInfo hL (hall p hp) (hH p hp)
    have hvzb := isBool hL (r := p.1) (by have := (hall p hp).1; have := hH p hp; omega) (x := ValV3.vz) (by simp [bools])
    have hdub := isBool hL (r := p.1) (by have := (hall p hp).1; have := hH p hp; omega) (x := ValV3.dup) (by simp [bools])
    rcases hvzb with h1 | h1 <;> rcases hdub with h2 | h2
    · rcases hz with ⟨h, -⟩ | ⟨-, hl⟩
      · rw [h1] at h; exact absurd h (by decide)
      · simp [valOf, h1, h2, hl, toNat_natCast, Nat.mod_eq_of_lt (show p.2 < P by have := hH p hp; omega)]
    all_goals simp [valOf, h1, h2]
  have hA0 : tr.cell tt A ValV3.act = 0 := hinact A (by omega) hAlt
  obtain ⟨hgbA, hgduA, hzA, -⟩ := rowFacts hL hAlt
  obtain ⟨hduA, hhdA, hvfA, -⟩ := hzA hA0
  have hgbA0 : tr.cell tt A ValV3.gb = 0 := by rw [hgbA, hA0]; grind
  have hgduA0 : tr.cell tt A ValV3.gdu = 0 := by rw [hgduA, hvfA]; grind
  refine ⟨segs.map (valOf tr tt), ⟨?_, ?_, ?_, ?_⟩, fun bb m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    obtain ⟨-, hz⟩ := segInfo hL (hall p hp) (hH p hp)
    have hpos' := (hall p hp).1
    rcases hz with ⟨h1, -, h3, -⟩ | ⟨h1, h2⟩
    · refine ⟨fun _ => ⟨by simp [valOf, h3]; rfl, by simp [valOf, h1]⟩, fun h => by simp [valOf, h1] at h⟩
    · refine ⟨fun h => by simp [valOf, h1] at h, fun _ => ⟨?_, ?_⟩⟩
      · simp [valOf, h1, h2, toNat_natCast, Nat.mod_eq_of_lt (show p.2 < P by have := hH p hp; omega)]
      · simp [valOf, h2, toNat_natCast, Nat.mod_eq_of_lt (show p.2 < P by have := hH p hp; omega)]; omega
  · intro e he
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, fun x hx => ?_⟩
    simp only [valOf] at hx
    split at hx
    · simp at hx
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact Fp.toNat_lt _
  · intro t ht
    simp only [List.length_map] at ht
    simp only [List.getElem_map]
    have hp0 : segs[t] ∈ segs := List.getElem_mem (by omega)
    have hp1 : segs[t + 1] ∈ segs := List.getElem_mem ht
    have hs1 := consec_get segs 0 hc t ht
    obtain ⟨hrow0', -⟩ := segInfo hL (hall _ hp0) (hH _ hp0)
    have hl0 := (hall _ hp0).1
    have hvl : tr.cell tt (segs[t].1 + segs[t].2 - 1) ValV3.vl = 1 := by
      have := (hall _ hp0).2.2.1; simpa [isOne] using this
    have hact1 : tr.cell tt segs[t + 1].1 ValV3.act = 1 := by
      have := (hall _ hp1).2.2.2.1 segs[t + 1].1 (Nat.le_refl _) (by have := (hall _ hp1).1; omega)
      simpa [isOne] using this
    have hH1 := hH _ hp1
    have e1 : segs[t].1 + segs[t].2 - 1 + 1 = segs[t + 1].1 := by omega
    have := ((afterSeg hL (r := segs[t].1 + segs[t].2 - 1) (by have := (hall _ hp1).1; omega) hvl).2
      (by rw [e1]; exact hact1)).2
    rw [e1] at this
    have hk := (hrow0' (segs[t].2 - 1) (by omega)).2.2.1 ValV3.vid (by simp [ValV3.valConst])
    rw [show segs[t].1 + (segs[t].2 - 1) = segs[t].1 + segs[t].2 - 1 by omega] at hk
    simp only [valOf]
    rw [this, hk]; exact Fp.toNat_add _ _
  · rw [List.map_map]
    have : ((segs.map fun p => if tr.cell tt p.1 ValV3.vz = 1 then 1 else (tr.cell tt p.1 ValV3.len).toNat)) =
        segs.map fun p => p.2 := by
      apply List.map_congr_left
      intro p hp
      obtain ⟨-, hz⟩ := segInfo hL (hall p hp) (hH p hp)
      rcases hz with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, h2, toNat_natCast, Nat.mod_eq_of_lt (show p.2 < P by have := hH p hp; omega)]
    simp only [Function.comp_def, valOf, decide_eq_true_eq]
    rw [this, hsumℓ]
    have := height_le hL; omega
  · -- sends
    simp only [valTraffic]
    rw [tableBusCount_eq, hsplit, List.flatMap_append, List.flatMap_append, hrest, hsegs, List.append_nil,
      List.flatMap_singleton]
    by_cases hS : bb = B_SIZE
    · subst hS
      rw [rowT]
      simp only [hgbA0, hgduA0, hvfA, hhdA, hduA, hsumA]
      simp [valSends, hszA, Msg.toFp, natCast_eq, o1, B_SIZE, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT]
      rw [flatMap_nil_fun]; simp
    · rw [hrow0 bb true A (Nat.le_refl _) hAlt (Or.inl hS), valSends_flat _ _ hS]
      simp [hS, List.map_flatMap, List.flatMap_map]
  · -- receives
    simp only [valTraffic]
    rw [tableBusCount_eq, hsplit, List.flatMap_append, List.flatMap_append, hrest, hsegs, List.append_nil,
      List.flatMap_singleton]
    by_cases hS : bb = B_SIZE
    · subst hS
      rw [rowT]
      simp only [hgbA0, hgduA0, hvfA, hhdA, hduA, hsumA]
      simp [valRecvs, B_SIZE, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT]
      rw [flatMap_nil_fun]; simp
    · rw [hrow0 bb false A (Nat.le_refl _) hAlt (Or.inl hS), valRecvs_flat]
      simp [hS, List.map_flatMap, List.flatMap_map]

end ZkFormal.NearV3
