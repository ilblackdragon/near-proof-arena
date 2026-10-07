import ZkFormal.NearV3.Sched.Complete.MemHonest
import ZkFormal.NearV3.Sched.Complete.Cmp

/-!
# ZkFormal.NearV3.Sched.Complete.Mem — completeness of the memory `smmV3` (M4)

For a run whose memory segments are honest (`SegOk`: INIT values, ops chained from the
previous row with the READ / GRANT semantics of the replay, values `< P`) and fit the table
(`Σ_g (1 + |ops g|) + 1 ≤ 2^22`), the honest trace `Gen.Mem.trace R`:

* has log height in `[1, maxLog]`;
* satisfies every constraint on every row (`mem_constraints`);
* has boolean multiplicity bits (`mem_bits`);
* has traffic (`mem_traffic`, `mem_complete`): it receives on `SOP` exactly `sopList segs` (per
  segment its INIT message `(addr, 0, OP_INIT, vin₀, v₀, w₀, 0, isL)`, then its op log
  `(addr, t, op, vin, v, inc, ok, c)` in order), sends on `SFIN` exactly `finList segs` (one
  `(addr, vfin, wfin)` per segment), sends on `SCMP` exactly `cmpList segs` (per op
  `(t, tp + 1, 1)`, then `(vin, inc, sf)` for a GRANT), and nothing else.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-! ## Records at every row -/

def vsAt (segs : List Seg) (r : Nat) : MV := (memVs segs).getD r padV

theorem padV_cell (c : Nat) : padV.cell c = 0 := by
  unfold MV.cell padV; simp

theorem opsVs_act (g : Seg) : ∀ k tp os, ∀ V ∈ opsVs g k tp os, V.act = 1
  | _, _, [], V, h => by simp [opsVs] at h
  | k, tp, o :: os, V, h => by
    simp only [opsVs, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact opsVs_act g (k + 1) o.t os V h

theorem memVs_act (segs : List Seg) : ∀ V ∈ memVs segs, V.act = 1 := by
  intro V hV
  obtain ⟨g, -, hV⟩ := List.mem_flatMap.1 hV
  simp only [segVs, List.mem_cons] at hV
  rcases hV with rfl | hV
  · rfl
  · exact opsVs_act g 0 0 g.ops V hV

theorem vsAt_lt {segs : List Seg} {r : Nat} (h : r < (memVs segs).length) :
    vsAt segs r = (memVs segs)[r] := by
  unfold vsAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem vsAt_ge {segs : List Seg} {r : Nat} (h : (memVs segs).length ≤ r) : vsAt segs r = padV := by
  unfold vsAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem vsAt_act (segs : List Seg) (r : Nat) : (vsAt segs r).act = if r < (memVs segs).length then 1 else 0 := by
  by_cases h : r < (memVs segs).length
  · rw [vsAt_lt h, if_pos h]; exact memVs_act segs _ (List.getElem_mem h)
  · rw [vsAt_ge (by omega), if_neg h]; rfl

theorem vsAt_ok (segs : List Seg) (hg : ∀ g ∈ segs, SegOk g) (r : Nat) :
    RowOk (vsAt segs r) ∧ (vsAt segs r).Small := by
  by_cases h : r < (memVs segs).length
  · rw [vsAt_lt h]; exact memVs_ok segs hg _ (List.getElem_mem h)
  · rw [vsAt_ge (by omega)]; exact ⟨padV_ok, padV_small⟩

theorem memRows_size (R : Run) (hs : ∀ g ∈ R.segs, SegSmall g) :
    (Gen.Mem.rows R).size = (memVs R.segs).length := by
  rw [← Array.length_toList]; exact (rows_rel R hs).length

def memPad : Nat → Array Nat := fun _ => zrow Mem.width

theorem mem_cell (R : Run) (hs : ∀ g ∈ R.segs, SegSmall g) (r c : Nat) :
    natCell (Gen.Mem.rows R) memPad r c = (vsAt R.segs r).cell c := by
  unfold natCell
  by_cases h : r < (Gen.Mem.rows R).size
  · rw [natRow_lt _ _ h]
    have hl : r < (memVs R.segs).length := by rw [← memRows_size R hs]; exact h
    rw [vsAt_lt hl]
    have := (rows_rel R hs).get r (by rw [Array.length_toList]; exact h) hl
    rw [Array.getElem_toList] at this
    exact this.cell c
  · rw [natRow_ge _ _ (by omega), vsAt_ge (by rw [← memRows_size R hs]; omega), padV_cell]
    exact gd_zrow _ _

theorem mem_small (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) : HSmall (Gen.Mem.rows R) memPad := by
  intro r c
  rw [mem_cell R (fun g h => (hg g h).small)]
  exact (vsAt_ok R.segs hg r).2 c

/-! ## Constraints -/

section
variable (R : Run) (hg : ∀ g ∈ R.segs, SegOk g)
include hg

theorem mem_len_lt (t : Nat) : (memVs R.segs).length + 1 ≤ (Gen.Mem.trace R).height t := by
  have := mk_rows_le (Gen.Mem.rows R) 1 memPad t
  rw [memRows_size R (fun g h => (hg g h).small)] at this
  exact this

theorem last_lst {r : Nat} (hr : r + 1 = (memVs R.segs).length) : (vsAt R.segs r).lst = 1 := by
  have h := (memVs_chain R.segs hg).2 (by intro e; rw [e] at hr; simp at hr)
  rw [List.getLast?_eq_getElem?, show (memVs R.segs).length - 1 = r by omega,
    List.getElem?_eq_getElem (by omega)] at h
  rw [vsAt_lt (by omega)]
  simpa using h

theorem mem_constraints (t : Nat) (pub : List Fp) (r : Nat) (hr : r < (Gen.Mem.trace R).height t) :
    ∀ e ∈ Mem.constraints, e.eval (Gen.Mem.trace R) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  have hlen := mem_len_lt R hg t
  have hE := mk_env (Gen.Mem.rows R) 1 memPad (mem_small R hg) t hr pub
  have hs : ∀ g ∈ R.segs, SegSmall g := fun g h => (hg g h).small
  have hX : ∀ c, (tenv (Gen.Mem.trace R) t r pub).cur c = (vsAt R.segs r).cell c := fun c => by
    rw [← mem_cell R hs]; exact hE.1 c
  have hY : ∀ c, (tenv (Gen.Mem.trace R) t r pub).nxt c = (vsAt R.segs ((r + 1) % (Gen.Mem.trace R).height t)).cell c := fun c => by
    rw [← mem_cell R hs]; exact hE.2 c
  have hx := (vsAt_ok R.segs hg r).1
  have hyb := (vsAt_ok R.segs hg ((r + 1) % (Gen.Mem.trace R).height t)).1.bact
  have hact := vsAt_act R.segs
  have hchain := (memVs_chain R.segs hg).1
  -- an active row has an in-range successor
  have hnext : ∀ h : r + 1 < (memVs R.segs).length, vsAt R.segs ((r + 1) % (Gen.Mem.trace R).height t) =
      (memVs R.segs)[r + 1]'h := fun h => by
    rw [Nat.mod_eq_of_lt (by omega), vsAt_lt h]
  refine mem_row_ok hX hY hx hyb (fun h1 h2 => ?_) (fun h1 h2 => ?_) ?_ ?_ e he
  · -- continuation
    have hrL : r < (memVs R.segs).length := by
      rw [hact] at h1
      by_cases hc : r < (memVs R.segs).length
      · exact hc
      · rw [if_neg hc] at h1; exact absurd h1 (by decide)
    by_cases h' : r + 1 < (memVs R.segs).length
    · rw [hnext h']
      have := hchain.get r h'
      rw [← vsAt_lt hrL] at this
      exact this.1 h2
    · rw [last_lst R hg (by omega)] at h2; exact absurd h2 (by decide)
  · -- after a last row
    have hrL : r < (memVs R.segs).length := by
      have := hx.lstAct; rw [h1, hact] at this
      by_cases hc : r < (memVs R.segs).length
      · exact hc
      · rw [if_neg hc] at this; omega
    by_cases h' : r + 1 < (memVs R.segs).length
    · rw [hnext h']
      have := hchain.get r h'
      rw [← vsAt_lt hrL] at this
      exact this.2 h1
    · rw [Nat.mod_eq_of_lt (by omega), hact, if_neg h'] at h2; exact absurd h2 (by decide)
  · -- first row
    show (if r = 0 then 1 else 0 : Int) = 0 ∨ ((if r = 0 then 1 else 0 : Int) = 1 ∧ _)
    by_cases h0 : r = 0
    · right; subst h0; refine ⟨rfl, ?_⟩
      by_cases hL0 : 0 < (memVs R.segs).length
      · rw [vsAt_lt hL0]
        have := memVs_head R.segs (memVs R.segs)[0] (by simp [List.head?_eq_getElem?, hL0])
        rw [this.1, this.2]
      · rw [vsAt_ge (by omega)]; rfl
    · left; rw [if_neg h0]
  · -- last row
    show ((if r + 1 = (Gen.Mem.trace R).height t then 1 else 0 : Int) = 0 ∧ _) ∨
      ((if r + 1 = (Gen.Mem.trace R).height t then 1 else 0 : Int) = 1 ∧ _)
    by_cases hl : r + 1 = (Gen.Mem.trace R).height t
    · right; rw [if_pos hl, hact, if_neg (by omega)]; exact ⟨rfl, rfl⟩
    · left; refine ⟨by rw [if_neg hl], fun h0 => ?_⟩
      rw [hact] at h0
      have : ¬ r < (memVs R.segs).length := fun h => by rw [if_pos h] at h0; exact absurd h0 (by decide)
      rw [Nat.mod_eq_of_lt (by omega), hact, if_neg (by omega)]

end

theorem mem_cur (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) {t r : Nat} (hr : r < (Gen.Mem.trace R).height t)
    (pub : List Fp) (c : Nat) : (tenv (Gen.Mem.trace R) t r pub).cur c = (vsAt R.segs r).cell c := by
  have := (mk_env (Gen.Mem.rows R) 1 memPad (mem_small R hg) t hr pub).1 c
  rw [mem_cell R (fun g h => (hg g h).small)] at this
  exact this

/-! ## Multiplicity bits -/

theorem cell_eval (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) {t r : Nat} (hr : r < (Gen.Mem.trace R).height t)
    (pub : List Fp) (c : Nat) :
    (ZkFormal.Chacha.Table.E.c c).eval (Gen.Mem.trace R) t r pub = Fp.ofNat ((vsAt R.segs r).cell c) := by
  show (mkTrace (Gen.Mem.rows R) 1 memPad).cell t r c = _
  rw [mk_cell (Gen.Mem.rows R) 1 memPad t hr, mem_cell R (fun g h => (hg g h).small)]

theorem mem_bits (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) (t r : Nat) (pub : List Fp)
    (hr : r < (Gen.Mem.trace R).height t) :
    ∀ i ∈ Mem.interactions, ∀ b ∈ i.mult,
      b.eval (Gen.Mem.trace R) t r pub = 0 ∨ b.eval (Gen.Mem.trace R) t r pub = 1 := by
  have hx := (vsAt_ok R.segs hg r).1
  intro i hi b hb
  simp only [Mem.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb
  · rw [cell_eval R hg hr]; exact ofNat_bit (by simpa [MV.cell, Mem.act] using hx.bact)
  · rw [cell_eval R hg hr]; exact ofNat_bit (by simpa [MV.cell, Mem.lst] using hx.blst)
  · rw [eval_ofNat (n := (vsAt R.segs r).isRd + (vsAt R.segs r).isGr) (by
      simp only [zev_add, zev_c, mem_cur R hg hr, MV.cell, Mem.isRd, Mem.isGr]
      simp)]
    exact ofNat_bit (by have := hx.kind; have := hx.bact; omega)
  · rw [cell_eval R hg hr]; exact ofNat_bit (by simpa [MV.cell, Mem.isGr] using hx.bgr)

/-! ## Traffic -/

def sopMsg (X : MV) : List Nat := [X.addr, X.t, X.isRd + 2 * X.isGr, X.vin, X.v, X.inc, X.ok, X.cc]
def finMsg (X : MV) : List Nat := [X.addr, X.v, X.w]
def cmpTMsg (X : MV) : List Nat := [X.t, X.tp + 1, 1]
def cmpVMsg (X : MV) : List Nat := [X.vin, X.inc, X.sf]

/-- Messages of a memory row on bus `b` in direction `send`. -/
def rowMsgs (b : Nat) (send : Bool) (X : MV) : List (List Nat) :=
  (if b = B_SOP ∧ send = false ∧ X.act = 1 then [sopMsg X] else []) ++
  (if b = B_SFIN ∧ send = true ∧ X.lst = 1 then [finMsg X] else []) ++
  (if b = B_SCMP ∧ send = true ∧ X.isRd + X.isGr = 1 then [cmpTMsg X] else []) ++
  (if b = B_SCMP ∧ send = true ∧ X.isGr = 1 then [cmpVMsg X] else [])

theorem term_eq {A B : Prop} [Decidable A] [Decidable B] (msg m : List Fp) {β : Nat} (hβ : β ≤ 1) :
    (if A ∧ B ∧ msg = m then β else 0) = (if A ∧ B ∧ β = 1 then [msg] else []).count m := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA, hB, true_and, false_and, if_false]
  · rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl
    · by_cases e : msg = m <;> simp [e]
    · by_cases e : msg = m <;> simp [e]
  all_goals rfl

theorem multNat_one (bus : Nat) (send : Bool) (msg : List Expr) (b : Expr) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) {β : Nat} (hb : b.eval tr t r pub = Fp.ofNat β) (hβ : β ≤ 1) :
    Interaction.multNat { bus := bus, mult := [b], msg := msg, send := send } tr t r pub = β := by
  simp only [Interaction.multNat, Interaction.multNat.go]
  rw [hb]
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;> rfl

theorem fmsgs_append (a b : List (List Nat)) : fmsgs (a ++ b) = fmsgs a ++ fmsgs b := List.map_append

theorem mem_row_count (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) (t r : Nat) (pub : List Fp)
    (hr : r < (Gen.Mem.trace R).height t) (b : Nat) (send : Bool) (m : List Fp) :
    (Mem.interactions.map fun i =>
      if i.bus = b ∧ i.send = send ∧ i.msgVal (Gen.Mem.trace R) t r pub = m then
        i.multNat (Gen.Mem.trace R) t r pub else 0).sum =
      (fmsgs (rowMsgs b send (vsAt R.segs r))).count m := by
  have hs : ∀ g ∈ R.segs, SegSmall g := fun g h => (hg g h).small
  have hx := (vsAt_ok R.segs hg r).1
  have hcur := mem_cur R hg hr pub
  have ec0 : ∀ c, (ZkFormal.Chacha.Table.E.c c).eval (Gen.Mem.trace R) t r pub =
      Fp.ofNat ((vsAt R.segs r).cell c) := fun c => cell_eval R hg hr pub c
  generalize vsAt R.segs r = X at hx hcur ec0 ⊢
  have ev : ∀ (e : Expr) (v : Nat), zev (tenv (Gen.Mem.trace R) t r pub) e = (v : Int) →
      e.eval (Gen.Mem.trace R) t r pub = Fp.ofNat v := fun e v h => eval_ofNat h
  have ec := ec0
  simp only [Mem.interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [multNat_one _ _ _ _ _ _ _ _ (ec Mem.act) (by simpa [MV.cell, Mem.act] using hx.bact),
    multNat_one _ _ _ _ _ _ _ _ (ec Mem.lst) (by simpa [MV.cell, Mem.lst] using hx.blst),
    multNat_one _ _ _ _ _ _ _ _ (ev _ (X.isRd + X.isGr) (by simp [hcur, MV.cell, Mem.isRd, Mem.isGr]))
      (by have := hx.kind; have := hx.bact; omega),
    multNat_one _ _ _ _ _ _ _ _ (ec Mem.isGr) (by simpa [MV.cell, Mem.isGr] using hx.bgr)]
  have hopE : Mem.opE.eval (Gen.Mem.trace R) t r pub = Fp.ofNat (X.isRd + 2 * X.isGr) :=
    ev _ _ (by simp [Mem.opE, hcur, MV.cell, Mem.isRd, Mem.isGr])
  have htp1 : (Expr.add (ZkFormal.Chacha.Table.E.c Mem.tp) (ZkFormal.Chacha.Table.E.k 1)).eval
      (Gen.Mem.trace R) t r pub = Fp.ofNat (X.tp + 1) := ev _ _ (by simp [hcur, MV.cell, Mem.tp])
  have hk1 : (ZkFormal.Chacha.Table.E.k 1).eval (Gen.Mem.trace R) t r pub = Fp.ofNat 1 := ev _ _ (by simp)
  simp only [Interaction.msgVal, List.map_cons, List.map_nil, ec, hopE, htp1, hk1]
  have e1 : [Fp.ofNat (X.cell Mem.addr), Fp.ofNat (X.cell Mem.t), Fp.ofNat (X.isRd + 2 * X.isGr),
      Fp.ofNat (X.cell Mem.vin), Fp.ofNat (X.cell Mem.v), Fp.ofNat (X.cell Mem.inc), Fp.ofNat (X.cell Mem.ok),
      Fp.ofNat (X.cell Mem.cc)] = (sopMsg X).map Fp.ofNat := by
    simp [sopMsg, MV.cell, Mem.addr, Mem.t, Mem.vin, Mem.v, Mem.inc, Mem.ok, Mem.cc]
  have e2 : [Fp.ofNat (X.cell Mem.addr), Fp.ofNat (X.cell Mem.v), Fp.ofNat (X.cell Mem.w)] =
      (finMsg X).map Fp.ofNat := by simp [finMsg, MV.cell, Mem.addr, Mem.v, Mem.w]
  have e3 : [Fp.ofNat (X.cell Mem.t), Fp.ofNat (X.tp + 1), Fp.ofNat 1] = (cmpTMsg X).map Fp.ofNat := by
    simp [cmpTMsg, MV.cell, Mem.t]
  have e4 : [Fp.ofNat (X.cell Mem.vin), Fp.ofNat (X.cell Mem.inc), Fp.ofNat (X.cell Mem.sf)] =
      (cmpVMsg X).map Fp.ofNat := by simp [cmpVMsg, MV.cell, Mem.vin, Mem.inc, Mem.sf]
  rw [e1, e2, e3, e4]
  rw [term_eq _ _ (by simpa [MV.cell, Mem.act] using hx.bact),
    term_eq _ _ (by simpa [MV.cell, Mem.lst] using hx.blst),
    term_eq _ _ (by have := hx.kind; have := hx.bact; omega),
    term_eq _ _ (by simpa [MV.cell, Mem.isGr] using hx.bgr)]
  unfold rowMsgs
  simp only [fmsgs_append, List.count_append]
  have h1 : ∀ (A : Prop) [Decidable A] (x : List Nat), fmsgs (if A then [x] else []) =
      if A then [x.map Fp.ofNat] else [] := fun A _ x => by split <;> rfl
  simp only [h1, MV.cell, Mem.act, Mem.lst, Mem.isGr]
  simp only [eq_comm (a := B_SOP), eq_comm (a := B_SFIN), eq_comm (a := B_SCMP), eq_comm (a := false),
    eq_comm (a := true)]
  simp
  omega

theorem sum_count_flatMap' {α β : Type} [BEq β] (f : α → List β) (m : β) (l : List α) :
    (l.map fun r => (f r).count m).sum = (l.flatMap f).count m := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.count_append, ih]

/-- **Traffic of the memory table** on any bus and direction: the messages of its records. -/
theorem mem_traffic (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) (t : Nat) (pub : List Fp) (b : Nat)
    (send : Bool) (m : List Fp) :
    tableBusCount Mem.interactions (Gen.Mem.trace R) t pub b send m =
      (fmsgs ((memVs R.segs).flatMap (rowMsgs b send))).count m := by
  rw [busCount_sum]
  rw [List.map_congr_left (fun r hr => mem_row_count R hg t r pub (List.mem_range.1 hr) b send m)]
  have hlen := mem_len_lt R hg t
  rw [sum_range_trunc (fun r => (fmsgs (rowMsgs b send (vsAt R.segs r))).count m)
      (len := (memVs R.segs).length) (fun r hr => by
        rw [vsAt_ge hr]; unfold rowMsgs; simp [padV, fmsgs]) _ (by omega)]
  calc ((List.range (memVs R.segs).length).map
        (fun r => (fmsgs (rowMsgs b send (vsAt R.segs r))).count m)).sum
      = ((memVs R.segs).map fun V => (fmsgs (rowMsgs b send V)).count m).sum := by
        rw [← range_map_getD (memVs R.segs) padV]; rfl
    _ = _ := by
        rw [sum_count_flatMap']
        unfold fmsgs
        rw [List.map_flatMap]

end ZkFormal.NearV3.Sched.Complete
