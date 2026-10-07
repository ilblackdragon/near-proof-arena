import ZkFormal.NearV3.Qv.Extract.WalkPhase

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}

theorem WalkChain.start_lt (q : WalkChain tr tt) (i : Nat) (hi : i<q.segs.length) :
    q.segs[i].1<tr.height tt := by
  have hp : q.segs[i]∈q.segs := List.getElem_mem hi
  have hv := (q.valid _ hp).1
  have he := (seg_le_end q.segs 0 q.consecutive _ hp).2
  have hf := q.fits
  omega

theorem WalkChain.first_start (q : WalkChain tr tt) (h : 0<q.segs.length) : q.segs[0].1=0 := by
  have gen : ∀ (l : List (Nat × Nat)), Consec 0 l → ∀ (h : 0<l.length), l[0].1=0 := by
    intro l hc
    cases l with
    | nil => intro h; simp at h
    | cons p rest => intro h; exact hc.1
  exact gen q.segs q.consecutive h

variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub) (q : WalkChain tr tt)
include hL

theorem WalkChain.main_prefix (i j : Nat) (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hij : i≤j) (hm : tr.cell tt q.segs[j].1 main=1) : tr.cell tt q.segs[i].1 main=1 := by
  rcases isBool hL (q.start_lt i hi) (x:=main) (by simp [walkBools]) with hz | ho
  · have hh := WalkChain.implicit_suffix hL q i j hi hj hij hz
    rw [hm] at hh
    grind
  · exact ho

theorem WalkChain.not_last_before_main (i : Nat) (hi : i+1<q.segs.length)
    (hm : tr.cell tt q.segs[i+1].1 main=1) : tr.cell tt q.segs[i].1 lastMain=0 := by
  rcases isBool hL (q.start_lt i (by omega)) (x:=lastMain) (by simp [walkBools]) with hz | ho
  · exact hz
  · have hh := ((WalkChain.indexed_order hL q i hi).2.1 ho).1
    rw [hm] at hh
    grind

theorem WalkChain.main_slot (i : Nat) (hi : i<q.segs.length)
    (hm : tr.cell tt q.segs[i].1 main=1) : tr.cell tt q.segs[i].1 slot=(i:Fp) := by
  induction i with
  | zero =>
    rw [q.first_start hi]
    have hh := (order_start hL).2.2.1
    simpa only [Lean.Grind.Semiring.natCast_zero] using hh
  | succ i ih =>
    have hprev := WalkChain.main_prefix hL q i (i+1) (by omega) hi (by omega) hm
    have hnot := WalkChain.not_last_before_main hL q i hi hm
    have hstep := ((WalkChain.indexed_order hL q i hi).1 hprev hnot).2.1
    rw [hstep,ih (by omega) hprev,natCast_add]
    simp only [Lean.Grind.Semiring.natCast_one]

theorem WalkChain.main_slot_nat (i : Nat) (hi : i<q.segs.length)
    (hm : tr.cell tt q.segs[i].1 main=1) : cv tr tt q.segs[i].1 slot=i := by
  have hh := WalkChain.main_slot hL q i hi hm
  have hb := WalkChain.index_lt_modulus hL q i hi
  simp only [cv,hh,toNat_natCast,Nat.mod_eq_of_lt hb]

theorem WalkChain.main_kind (i : Nat) (hidx : i<q.segs.length)
    (hm : tr.cell tt q.segs[i].1 main=1) :
    tr.cell tt q.segs[i].1 lo=(if i=0 ∨ i=2 then 0 else 1) ∧
    tr.cell tt q.segs[i].1 hi=(if i<2 then 0 else 1) := by
  induction i with
  | zero =>
    rw [q.first_start hidx]
    simpa using (order_start hL).2.2.2
  | succ i ih =>
    have hprev := WalkChain.main_prefix hL q i (i+1) (by omega) hidx (by omega) hm
    have hnot := WalkChain.not_last_before_main hL q i hidx hm
    have hstep := ((WalkChain.indexed_order hL q i hidx).1 hprev hnot).2.2
    obtain ⟨hlo,hhi⟩ := ih (by omega) hprev
    rw [hlo,hhi] at hstep
    by_cases h0 : i=0
    · subst i; simp only [Nat.reduceAdd,ite_true,ite_false] at hstep ⊢; constructor <;> grind
    · by_cases h1 : i=1
      · subst i; simp only [Nat.reduceAdd,ite_true,ite_false] at hstep ⊢; constructor <;> grind
      · by_cases h2 : i=2
        · subst i; simp only [Nat.reduceAdd,ite_true,ite_false] at hstep ⊢; constructor <;> grind
        · have hh : ¬i<2 := by omega
          have hn : ¬(i+1=0 ∨ i+1=2) := by omega
          have hn2 : ¬i+1<2 := by omega
          simp only [if_neg (show ¬(i=0 ∨ i=2) by omega),if_neg hh] at hstep
          simp only [if_neg hn,if_neg hn2]
          constructor <;> grind

end ZkFormal.NearV3.Qv.Extract
