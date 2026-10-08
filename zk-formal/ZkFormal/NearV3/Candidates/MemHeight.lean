import ZkFormal.NearV3.Candidates.SchedHeight
import ZkFormal.NearV3.Sched.Complete.Mem
namespace ZkFormal.NearV3.Candidates.MemHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
def trace (R : Run) : Trace Fp := SchedHeight.trace (Gen.Mem.rows R) memPad
section
variable (R : Run) (hg : ∀ g ∈ R.segs, SegOk g)
include hg
theorem mem_constraints (hrows : (memVs R.segs).length + 1 ≤ 2^22) (t : Nat) (pub : List Fp) (r : Nat) (hr : r < (trace R).height t) :
    ∀ e ∈ Mem.constraints, e.eval (trace R) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  have hlen : (memVs R.segs).length + 1 ≤ (trace R).height t := hrows
  have hE := SchedHeight.env (Gen.Mem.rows R) memPad (mem_small R hg) t r pub
  have hs : ∀ g ∈ R.segs, SegSmall g := fun g h => (hg g h).small
  have hX : ∀ c, (tenv (trace R) t r pub).cur c = (vsAt R.segs r).cell c := fun c => by
    rw [← mem_cell R hs]; exact hE.1 c
  have hY : ∀ c, (tenv (trace R) t r pub).nxt c = (vsAt R.segs ((r + 1) % (trace R).height t)).cell c := fun c => by
    rw [← mem_cell R hs]; exact hE.2 c
  have hx := (vsAt_ok R.segs hg r).1
  have hyb := (vsAt_ok R.segs hg ((r + 1) % (trace R).height t)).1.bact
  have hact := vsAt_act R.segs
  have hchain := (memVs_chain R.segs hg).1
  -- an active row has an in-range successor
  have hnext : ∀ h : r + 1 < (memVs R.segs).length, vsAt R.segs ((r + 1) % (trace R).height t) =
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
    show ((if r + 1 = (trace R).height t then 1 else 0 : Int) = 0 ∧ _) ∨
      ((if r + 1 = (trace R).height t then 1 else 0 : Int) = 1 ∧ _)
    by_cases hl : r + 1 = (trace R).height t
    · right; rw [if_pos hl, hact, if_neg (by omega)]; exact ⟨rfl, rfl⟩
    · left; refine ⟨by rw [if_neg hl], fun h0 => ?_⟩
      rw [hact] at h0
      have : ¬ r < (memVs R.segs).length := fun h => by rw [if_pos h] at h0; exact absurd h0 (by decide)
      rw [Nat.mod_eq_of_lt (by omega), hact, if_neg (by omega)]

end
theorem mem_cur (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) {t r : Nat} (hr : r < (trace R).height t)
    (pub : List Fp) (c : Nat) : (tenv (trace R) t r pub).cur c = (vsAt R.segs r).cell c := by
  have := (SchedHeight.env (Gen.Mem.rows R) memPad (mem_small R hg) t r pub).1 c
  rw [mem_cell R (fun g h => (hg g h).small)] at this
  exact this

/-! ## Multiplicity bits -/

theorem cell_eval (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) {t r : Nat} (hr : r < (trace R).height t)
    (pub : List Fp) (c : Nat) :
    (ZkFormal.Chacha.Table.E.c c).eval (trace R) t r pub = Fp.ofNat ((vsAt R.segs r).cell c) := by
  change Fp.ofNat (natCell (Gen.Mem.rows R) memPad r c) = _
  rw [mem_cell R (fun g h => (hg g h).small)]

theorem mem_bits (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) (t r : Nat) (pub : List Fp)
    (hr : r < (trace R).height t) :
    ∀ i ∈ Mem.interactions, ∀ b ∈ i.mult,
      b.eval (trace R) t r pub = 0 ∨ b.eval (trace R) t r pub = 1 := by
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

end ZkFormal.NearV3.Candidates.MemHeight
