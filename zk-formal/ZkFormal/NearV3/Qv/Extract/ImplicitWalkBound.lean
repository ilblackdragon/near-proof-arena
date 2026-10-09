import ZkFormal.NearV3.Qv.Extract.MainWalkIds

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (tau)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
include hL

/-- Every implicit request counter is bounded by the actual public terminal K.
No supplied implicit-row count or counter no-wrap assumption is used. -/
theorem implicit_distance_bound (last i : Nat) (hlast : last<q.segs.length)
    (hf : tr.cell tt q.segs[last].1 lastMain=1)
    (hi : i<q.segs.length) (hli : last<i) :
    i-last≤(kPublic.eval tr tt 0 pub).toNat := by
  have hn : last+1<q.segs.length := by omega
  obtain ⟨hm,ht⟩ := (WalkChain.indexed_order hL q last hn).2.1 hf
  have hpos : 0<q.segs.length := by omega
  have hj : q.segs.length-1<q.segs.length := by omega
  have hc := WalkChain.implicit_counter_nat hL q (last+1) (q.segs.length-1)
    hn hj (by omega) hm ht
  have hp := q.valid _ (List.getElem_mem hj)
  have hfit := Nat.le_trans (seg_le_end q.segs 0 q.consecutive _ (List.getElem_mem hj)).2 q.fits
  have he := segEnd_last q.segs 0 q.consecutive hpos
  have hrow : segEnd 0 q.segs-1<tr.height tt := by have := hp.1; omega
  have hterm := (order_termination hL hrow (q.final_end hL)).1
  have hmeta := walk_metadata hL hfit hp (x:=tau) (by simp)
    (segEnd 0 q.segs-1) (by have := hp.1; omega) (by have := hp.1; omega)
  have hpub : kPublic.eval tr tt (segEnd 0 q.segs-1) pub=kPublic.eval tr tt 0 pub := rfl
  rw [hmeta,hpub] at hterm
  have hcv := congrArg Fp.toNat hterm
  change cv tr tt q.segs[q.segs.length-1].1 tau=(kPublic.eval tr tt 0 pub).toNat at hcv
  rw [hc] at hcv
  omega

/-- Main/implicit identifiers occupy disjoint residue classes when the native
public transition count is below 64. -/
theorem main_implicit_id_ne (last i j : Nat) (hlast : last<q.segs.length)
    (hf : tr.cell tt q.segs[last].1 lastMain=1)
    (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hm : tr.cell tt q.segs[i].1 main=1) (hlj : last<j)
    (hK : (kPublic.eval tr tt 0 pub).toNat<64) :
    wid.eval tr tt (q.segs[i]'hi).1 pub≠wid.eval tr tt (q.segs[j]'hj).1 pub := by
  intro he
  obtain ⟨hei,hbi⟩ := main_walk_id hL q i hi hm
  obtain ⟨hej,hbj⟩ := implicit_walk_id hL q last j hlast hf hj hlj
  rw [hei,hej] at he
  have hn := ofNat_inj hbi hbj he
  have hd := implicit_distance_bound hL q last j hlast hf hj hlj
  omega

/-- All actual queue requests have distinct identifiers under the native
public transition-count bound. -/
theorem queue_walk_id_unique (i j : Nat) (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hK : (kPublic.eval tr tt 0 pub).toNat<64)
    (he : wid.eval tr tt (q.segs[i]'hi).1 pub=wid.eval tr tt (q.segs[j]'hj).1 pub) : i=j := by
  obtain ⟨last,hlast,hf⟩ := WalkChain.last_main_exists hL q
  have hm := (WalkChain.last_main_shape hL q last hlast hf).1
  by_cases hil : i≤last
  · have hmi := WalkChain.main_prefix hL q i last hi hlast hil hm
    by_cases hjl : j≤last
    · have hmj := WalkChain.main_prefix hL q j last hj hlast hjl hm
      exact main_walk_id_unique hL q i j hi hj hmi hmj he
    · exact False.elim (main_implicit_id_ne hL q last i j hlast hf hi hj hmi (by omega) hK he)
  · by_cases hjl : j≤last
    · have hmj := WalkChain.main_prefix hL q j last hj hlast hjl hm
      exact False.elim (main_implicit_id_ne hL q last j i hlast hf hj hi hmj (by omega) hK he.symm)
    · exact implicit_walk_id_unique hL q last i j hlast hf hi hj (by omega) (by omega) he

end ZkFormal.NearV3.Qv.Extract
