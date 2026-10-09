import ZkFormal.NearV3.Qv.Extract.WalkMain

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (count)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub) (q : WalkChain tr tt)
include hL q

theorem WalkChain.last_main_shape (i : Nat) (hidx : i<q.segs.length)
    (hf : tr.cell tt q.segs[i].1 lastMain=1) :
    tr.cell tt q.segs[i].1 main=1 ∧ 2≤i := by
  have hr := q.start_lt i hidx
  have hm := con hL hr (e:=.mul (c lastMain) (Dsl.not (c main))) (by simp [constraints])
  have hh := con hL hr (e:=.mul (c lastMain) (Dsl.not (c hi))) (by simp [constraints])
  simp only [eval_mul,eval_c,eval_not,hf] at hm hh
  have hmain : tr.cell tt q.segs[i].1 main=1 := by grind
  have hk := (WalkChain.main_kind hL q i hidx hmain).2
  refine ⟨hmain,?_⟩
  by_cases hsmall : i<2
  · rw [if_pos hsmall] at hk
    rw [hk] at hh
    grind
  · omega

/-- The final main slot determines the group count as an ordinary natural,
including the zero-group case at the yielded request. -/
theorem WalkChain.last_main_count (i : Nat) (hidx : i<q.segs.length)
    (hf : tr.cell tt q.segs[i].1 lastMain=1) : cv tr tt q.segs[i].1 count=i-2 := by
  obtain ⟨hm,hge⟩ := WalkChain.last_main_shape hL q i hidx hf
  have hs := WalkChain.main_slot hL q i hidx hm
  have hk := (WalkChain.main_kind hL q i hidx hm).1
  have hh := gate_eq hL (q.start_lt i hidx) (g:=c lastMain) (a:=c count)
    (b:=.mul (c lo) (sub (c slot) (k 2))) (by simp [constraints]) hf
  simp only [eval_c,eval_mul,eval_sub,eval_k,hs,hk] at hh
  have hcast : tr.cell tt q.segs[i].1 count=((i-2:Nat):Fp) := by
    by_cases he : i=2
    · subst i
      simp only [Nat.sub_self,Lean.Grind.Semiring.natCast_zero] at *
      grind
    · have hn : ¬(i=0 ∨ i=2) := by omega
      rw [if_neg hn] at hh
      have hc : (i:Fp)=((i-2:Nat):Fp)+(2:Nat) := by
        rw [←natCast_add]
        congr 1
        omega
      rw [hc] at hh
      grind
  have hsmall : i-2<P := by have := WalkChain.index_lt_modulus hL q i hidx; omega
  simp only [cv,hcast,toNat_natCast,Nat.mod_eq_of_lt hsmall]

theorem WalkChain.main_count_constant (i : Nat) (hidx : i<q.segs.length)
    (hm : tr.cell tt q.segs[i].1 main=1) : tr.cell tt q.segs[i].1 count=tr.cell tt 0 count := by
  induction i with
  | zero => rw [q.first_start hidx]
  | succ i ih =>
    have hprev := WalkChain.main_prefix hL q i (i+1) (by omega) hidx (by omega) hm
    have hf := WalkChain.not_last_before_main hL q i hidx hm
    have hstep := ((WalkChain.indexed_order hL q i hidx).1 hprev hf).2.2.2.2
    exact hstep.trans (ih (by omega) hprev)

theorem WalkChain.last_main_exists : ∃ i, ∃ (hi : i<q.segs.length),
    tr.cell tt q.segs[i].1 lastMain=1 := by
  by_cases hex : ∃ i, ∃ (hi : i<q.segs.length), tr.cell tt q.segs[i].1 lastMain=1
  · exact hex
  · exfalso
    have hz : ∀ i (hi : i<q.segs.length), tr.cell tt q.segs[i].1 lastMain=0 := by
      intro i hi
      exact (isBool hL (q.start_lt i hi) (x:=lastMain) (by simp [walkBools])).resolve_right
        (fun he => hex ⟨i,hi,he⟩)
    have hall : ∀ i (hi : i<q.segs.length), tr.cell tt q.segs[i].1 main=1 := by
      intro i
      induction i with
      | zero => intro hi; rw [q.first_start hi]; exact (order_start hL).1
      | succ i ih =>
        intro hi
        exact ((WalkChain.indexed_order hL q i hi).1 (ih (by omega)) (hz i (by omega))).1
    have hpos : 0<q.segs.length := List.length_pos_iff.mpr q.nonempty
    let i := q.segs.length-1
    have hi : i<q.segs.length := by dsimp [i]; omega
    have hp : q.segs[i]∈q.segs := List.getElem_mem hi
    have hv := q.valid _ hp
    have hlen := hv.1
    have hfit : q.segs[i].1+q.segs[i].2≤tr.height tt :=
      Nat.le_trans (seg_le_end q.segs 0 q.consecutive _ hp).2 q.fits
    have he : segEnd 0 q.segs=q.segs[i].1+q.segs[i].2 :=
      segEnd_last q.segs 0 q.consecutive hpos
    have hm := walk_metadata hL hfit hv (x:=main) (by simp)
      (q.segs[i].1+q.segs[i].2-1) (by omega) (by omega)
    have hf := walk_metadata hL hfit hv (x:=lastMain) (by simp)
      (q.segs[i].1+q.segs[i].2-1) (by omega) (by omega)
    have hend := WalkChain.final_end hL q
    rw [he] at hend
    have hh := (order_termination hL (show q.segs[i].1+q.segs[i].2-1<tr.height tt by omega) hend).2
      (hm.trans (hall i hi))
    rw [hf,hz i hi] at hh
    grind

/-- The carried group count is bounded by actual accepted request rows. -/
theorem WalkChain.main_count_bound : cv tr tt 0 count<tr.height tt := by
  obtain ⟨i,hi,hf⟩ := WalkChain.last_main_exists hL q
  have hm := (WalkChain.last_main_shape hL q i hi hf).1
  have hc := WalkChain.last_main_count hL q i hi hf
  have he := WalkChain.main_count_constant hL q i hi hm
  have hb := q.length_le_height
  have hh : cv tr tt q.segs[i].1 count=cv tr tt 0 count := congrArg Fp.toNat he
  omega

end ZkFormal.NearV3.Qv.Extract
