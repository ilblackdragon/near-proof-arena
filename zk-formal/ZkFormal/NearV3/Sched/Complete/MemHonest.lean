import ZkFormal.NearV3.Sched.Complete.MemCons

/-!
# ZkFormal.NearV3.Sched.Complete.MemHonest — honest memory segments (M4)

`SegOk g`: the segment's INIT has `vin = allowed`, and its ops (`OpsOk`) are READs / GRANTs
chained from the INIT values (each op's `vin, wp` are the previous row's `v, w`), with the
READ / GRANT semantics of the replay (`Gen.run`: `sf = [inc ≤ vin]`, `c = al` on links and
`c = sf` on budgets, `ok ⇒ c`, `v = vin − inc` (saturating to `0` when `¬sf`) if `ok`,
links add `ok·inc` to `w`). Then:

* `memVs_ok`: every record of `memVs segs` satisfies `RowOk` and is `Small`;
* `memVs_chain`: consecutive records `X, Y` are a continuation (`¬X.lst`) or a segment
  boundary (`X.lst`, `Y` an INIT); the last record has `lst = 1`; the first is an INIT.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- An honest memory op following a row with value `pv` and granted `pw`. -/
structure OpOk (g : Seg) (pv pw : Nat) (o : MOp) : Prop where
  kind : o.op = OP_READ ∨ o.op = OP_GRANT
  vin : o.vin = pv
  wp : o.wp = pw
  rd : o.op = OP_READ → o.v = o.vin ∧ o.w = o.wp ∧ o.inc = 0 ∧ o.ok = false ∧ o.c = false ∧ o.sf = false
  gr : o.op = OP_GRANT → o.sf = decide (o.inc ≤ o.vin) ∧ o.c = (if g.isL then g.al else o.sf) ∧
    (o.ok = true → o.c = true) ∧ o.v = (if o.ok then (if o.sf then o.vin - o.inc else 0) else o.vin) ∧
    o.w = o.wp + (if g.isL && o.ok then o.inc else 0)

def OpsOk (g : Seg) : Nat → Nat → List MOp → Prop
  | _, _, [] => True
  | pv, pw, o :: os => OpOk g pv pw o ∧ OpsOk g o.v o.w os

/-- An honest memory segment. -/
structure SegOk (g : Seg) : Prop where
  vin0 : g.vin0 = b2n g.al
  ops : OpsOk g g.v0 g.w0 g.ops
  small : SegSmall g

/-! ## One-row facts -/

theorem b2n_eq_one {b : Bool} : b2n b = 1 ↔ b = true := by cases b <;> decide

theorem b2n_beq {x y : Nat} (h : b2n (x == y) = 1) : x = y := beq_iff_eq.1 (b2n_eq_one.1 h)

theorem initV_ok (g : Seg) (hg : SegOk g) : RowOk (initV g) :=
  ⟨Nat.le_refl _, Nat.le_refl _, b2n_le _, Nat.zero_le _, Nat.zero_le _, b2n_le _, b2n_le _,
   Nat.zero_le _, b2n_le _, Nat.zero_le _, rfl, b2n_le _, fun _ => ⟨rfl, hg.vin0, rfl, rfl, rfl, rfl, rfl⟩,
   fun h => absurd h (by simp [initV]), fun h => absurd h (by simp [initV])⟩

theorem opV_ok (g : Seg) (i tp pv pw : Nat) (o : MOp) (ho : OpOk g pv pw o) : RowOk (opV g i tp o) := by
  refine ⟨Nat.le_refl _, Nat.zero_le _, b2n_le _, b2n_le _, b2n_le _, b2n_le _, b2n_le _, b2n_le _,
    b2n_le _, b2n_le _, ?_, b2n_le _, fun h => absurd h (by simp [opV]), fun h => ?_, fun h => ?_⟩
  · show 1 = 0 + b2n (o.op == OP_READ) + b2n (o.op == OP_GRANT)
    rcases ho.kind with h | h <;> rw [h] <;> decide
  · have hr : o.op = OP_READ := b2n_beq h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ho.rd hr
    exact ⟨h1, h2, h3, by show b2n o.ok = 0; rw [h4]; rfl, by show b2n o.c = 0; rw [h5]; rfl,
      by show b2n o.sf = 0; rw [h6]; rfl⟩
  · have hr : o.op = OP_GRANT := b2n_beq h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ho.gr hr
    show (b2n o.c = if b2n g.isL = 1 then b2n g.al else b2n o.sf) ∧
      (o.v = if b2n o.ok = 1 then (if b2n o.sf = 1 then o.vin - o.inc else 0) else o.vin) ∧
      (b2n o.sf = 1 → o.inc ≤ o.vin) ∧ (b2n o.ok = 1 → b2n o.c = 1) ∧
      o.w = o.wp + (if b2n g.isL = 1 ∧ b2n o.ok = 1 then o.inc else 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h2]; cases g.isL <;> cases g.al <;> cases o.sf <;> rfl
    · rw [h4]; cases o.ok <;> cases o.sf <;> rfl
    · intro hs; rw [b2n_eq_one] at hs; rw [hs] at h1; exact of_decide_eq_true h1.symm
    · intro hk; rw [b2n_eq_one] at hk ⊢; exact h3 hk
    · rw [h5]; cases g.isL <;> cases o.ok <;> rfl

/-! ## Smallness -/

theorem one_lt_P : 1 < P := by decide
theorem zero_lt_P : 0 < P := by decide

theorem ite_lt {p : Prop} [Decidable p] {a b : Nat} (ha : a < P) (hb : b < P) : (if p then a else b) < P := by
  split <;> assumption

theorem cell_small {X : MV} (h : X.act < P ∧ X.fst < P ∧ X.lst < P ∧ X.isRd < P ∧ X.isGr < P ∧
    X.addr < P ∧ X.t < P ∧ X.tp < P ∧ X.vin < P ∧ X.v < P ∧ X.wp < P ∧ X.w < P ∧ X.al < P ∧
    X.isL < P ∧ X.inc < P ∧ X.ok < P ∧ X.cc < P ∧ X.sf < P) : X.Small := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  intro c
  unfold MV.cell
  repeat (first | exact zero_lt_P | apply ite_lt (by assumption))


theorem initV_small (g : Seg) (hs : SegSmall g) : (initV g).Small := by
  obtain ⟨ha, hvi, hv, hw, -⟩ := hs
  exact cell_small ⟨one_lt_P, one_lt_P, b2n_lt _, zero_lt_P, zero_lt_P, ha, zero_lt_P, zero_lt_P, hvi,
    hv, hw, hw, b2n_lt _, b2n_lt _, hw, zero_lt_P, b2n_lt _, zero_lt_P⟩

theorem opV_small (g : Seg) (i tp : Nat) (o : MOp) (hs : SegSmall g) (htp : tp < P) (ho : o ∈ g.ops) :
    (opV g i tp o).Small := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs.2.2.2.2 o ho
  exact cell_small ⟨one_lt_P, zero_lt_P, b2n_lt _, b2n_lt _, b2n_lt _, hs.1, h1, htp, h2, h3, h4, h5,
    b2n_lt _, b2n_lt _, h6, b2n_lt _, b2n_lt _, b2n_lt _⟩

theorem padV_small : padV.Small := cell_small (by simp only [padV]; decide)

/-! ## Every record -/

theorem opsVs_ok (g : Seg) (hs : SegSmall g) :
    ∀ (os : List MOp) (k tp pv pw : Nat), (∀ o ∈ os, o ∈ g.ops) → tp < P → OpsOk g pv pw os →
      ∀ V ∈ opsVs g k tp os, RowOk V ∧ V.Small
  | [], _, _, _, _, _, _, _, V, hV => by simp [opsVs] at hV
  | o :: os, k, tp, pv, pw, hm, htp, ⟨ho, hos⟩, V, hV => by
    simp only [opsVs, List.mem_cons] at hV
    rcases hV with rfl | hV
    · exact ⟨opV_ok g _ _ _ _ o ho, opV_small g _ _ o hs htp (hm o List.mem_cons_self)⟩
    · exact opsVs_ok g hs os (k + 1) o.t o.v o.w (fun x hx => hm x (List.mem_cons_of_mem _ hx))
        (hs.2.2.2.2 o (hm o List.mem_cons_self)).1 hos V hV

theorem segVs_ok (g : Seg) (hg : SegOk g) : ∀ V ∈ segVs g, RowOk V ∧ V.Small := by
  intro V hV
  simp only [segVs, List.mem_cons] at hV
  rcases hV with rfl | hV
  · exact ⟨initV_ok g hg, initV_small g hg.small⟩
  · exact opsVs_ok g hg.small g.ops 0 0 g.v0 g.w0 (fun _ h => h) zero_lt_P hg.ops V hV

theorem memVs_ok (segs : List Seg) (hg : ∀ g ∈ segs, SegOk g) : ∀ V ∈ memVs segs, RowOk V ∧ V.Small := by
  intro V hV
  obtain ⟨g, hgm, hV⟩ := List.mem_flatMap.1 hV
  exact segVs_ok g (hg g hgm) V hV

/-! ## Consecutive records -/

/-- A legal successor inside the record list. -/
def Nx (X Y : MV) : Prop := (X.lst = 0 → Cont X Y) ∧ (X.lst = 1 → Y.fst = 1)

def ChainR : List MV → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => Nx x y ∧ ChainR (y :: l)

theorem ChainR.get : ∀ {l : List MV}, ChainR l → ∀ i (h : i + 1 < l.length), Nx l[i] l[i + 1]
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | x :: y :: l, ⟨hxy, hr⟩, i, h => by
    cases i with
    | zero => exact hxy
    | succ i => exact ChainR.get (l := y :: l) hr i (by simp at h ⊢; omega)

theorem ChainR.append : ∀ {a b : List MV}, ChainR a → ChainR b →
    (∀ x ∈ a.getLast?, ∀ y ∈ b.head?, Nx x y) → ChainR (a ++ b)
  | [], b, _, hb, _ => hb
  | [x], [], _, _, _ => trivial
  | [x], y :: b, _, hb, hxy => ⟨hxy x rfl y rfl, hb⟩
  | x :: y :: a, b, ⟨hxy, ha⟩, hb, hl => ⟨hxy, ChainR.append (a := y :: a) ha hb
      (fun u hu v hv => hl u (by simpa using hu) v hv)⟩

/-- Op records chain, the last one carrying `lst`. -/
theorem opsVs_chain (g : Seg) :
    ∀ (os : List MOp) (k tp : Nat) (X : MV), k + os.length = g.ops.length → X.addr = g.addr →
      X.al = b2n g.al → X.isL = b2n g.isL → X.t = tp → X.act = 1 → (os ≠ [] → X.lst = 0) →
      (os = [] → X.lst = 1) → OpsOk g X.v X.w os →
      ChainR (X :: opsVs g k tp os) ∧ ((X :: opsVs g k tp os).getLast?.map MV.lst = some 1)
  | [], k, tp, X, _, _, _, _, _, _, _, hl1, _ => ⟨trivial, by simp [opsVs, hl1 rfl]⟩
  | o :: os, k, tp, X, hk, ha, hal, hisL, ht, hact, hl0, _, ⟨ho, hos⟩ => by
    have hlen : k + 1 + os.length = g.ops.length := by simp at hk; omega
    have ih := opsVs_chain g os (k + 1) o.t (opV g (k + 1) tp o) hlen rfl rfl rfl rfl rfl
      (fun hne => by
        simp only [opV]
        have : (k + 1 == g.ops.length) = false := by
          have : os.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
          simp; omega
        rw [this]; rfl)
      (fun he => by subst he; simp only [opV]; simp at hlen; simp [hlen, b2n])
      hos
    refine ⟨⟨⟨fun _ => ?_, fun h => absurd h (by rw [hl0 (List.cons_ne_nil _ _)]; decide)⟩, ih.1⟩, ?_⟩
    · exact ⟨rfl, rfl, ha.symm, ho.vin, ht.symm, ho.wp, hal.symm, hisL.symm⟩
    · have e : (X :: opsVs g k tp (o :: os)) = X :: (opV g (k + 1) tp o :: opsVs g (k + 1) o.t os) := rfl
      rw [e, List.getLast?_cons_cons]
      exact ih.2

theorem segVs_chain (g : Seg) (hg : SegOk g) :
    ChainR (segVs g) ∧ (segVs g).getLast?.map MV.lst = some 1 := by
  apply opsVs_chain g g.ops 0 0 (initV g) (by omega) rfl rfl rfl rfl rfl
  · intro hne; simp only [initV]
    have : (g.ops.length == 0) = false := by
      have : g.ops.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
      simpa using this
    rw [this]; rfl
  · intro he; simp [initV, he, b2n]
  · exact hg.ops

theorem memVs_head (segs : List Seg) : ∀ y ∈ (memVs segs).head?, y.fst = 1 ∧ y.act = 1 := by
  intro y hy
  cases segs with
  | nil => simp [memVs] at hy
  | cons g segs =>
    simp only [memVs, List.flatMap_cons, segVs, List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hy
    subst hy; exact ⟨rfl, rfl⟩

theorem memVs_chain : ∀ (segs : List Seg), (∀ g ∈ segs, SegOk g) →
    ChainR (memVs segs) ∧ ((memVs segs) ≠ [] → (memVs segs).getLast?.map MV.lst = some 1)
  | [], _ => ⟨trivial, fun h => absurd rfl h⟩
  | g :: segs, hg => by
    have h1 := segVs_chain g (hg g List.mem_cons_self)
    have h2 := memVs_chain segs (fun g' h => hg g' (List.mem_cons_of_mem _ h))
    have e : memVs (g :: segs) = segVs g ++ memVs segs := List.flatMap_cons
    rw [e]
    refine ⟨ChainR.append h1.1 h2.1 (fun x hx y hy => ?_), fun _ => ?_⟩
    · have hl : x.lst = 1 := by
        have := h1.2; rw [hx] at this; simpa using this
      exact ⟨fun h => absurd h (by rw [hl]; decide), fun _ => (memVs_head segs y hy).1⟩
    · by_cases hn : memVs segs = []
      · rw [hn, List.append_nil]; exact h1.2
      · rw [List.getLast?_append]
        have h3 := h2.2 hn
        cases h : (memVs segs).getLast? with
        | none => rw [h] at h3; simp at h3
        | some y => rw [h] at h3; simpa using h3

end ZkFormal.NearV3.Sched.Complete
