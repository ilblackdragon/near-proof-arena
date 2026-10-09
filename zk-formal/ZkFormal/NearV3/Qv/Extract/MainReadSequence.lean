import ZkFormal.NearV3.Qv.Extract.NativeReadModes
import ZkFormal.NearV3.Qv.Extract.WalkCount

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (count)

/-- Main reads are exactly a prefix of three fixed reads followed by the
carried number of group reads. No extra main requests may follow that prefix. -/
theorem main_read_prefix {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) :
    3+cv tr tt 0 count≤q.segs.length ∧
      ∀ i (hi : i<q.segs.length), tr.cell tt q.segs[i].1 main=1 ↔ i<3+cv tr tt 0 count := by
  obtain ⟨last,hlast,hflag⟩ := WalkChain.last_main_exists hL q
  obtain ⟨hm,hge⟩ := WalkChain.last_main_shape hL q last hlast hflag
  have hc := WalkChain.last_main_count hL q last hlast hflag
  have he := congrArg Fp.toNat (WalkChain.main_count_constant hL q last hlast hm)
  have hcut : 3+cv tr tt 0 count=last+1 := by change cv tr tt q.segs[last].1 count=cv tr tt 0 count at he; omega
  rw [hcut]
  refine ⟨by omega,?_⟩
  intro i hi
  constructor
  · intro hmain
    by_cases hb : i<last+1
    · exact hb
    · have hnext : last+1<q.segs.length := by omega
      have hn := WalkChain.main_prefix hL q (last+1) i hnext hi (by omega) hmain
      have hz := WalkChain.not_last_before_main hL q last hnext hn
      rw [hflag] at hz
      exact False.elim ((by decide : (1:Fp)≠0) hz)
  · intro hb
    exact WalkChain.main_prefix hL q i last hi hlast (by omega) hm

/-- All three fixed main reads exist, including when the buffer is empty. -/
theorem fixed_main_reads {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) :
    ∃ h : 2<q.segs.length,
      tr.cell tt q.segs[0].1 main=1 ∧ tr.cell tt q.segs[1].1 main=1 ∧ tr.cell tt q.segs[2].1 main=1 := by
  obtain ⟨hfit,hmain⟩ := main_read_prefix hL q
  refine ⟨by omega,?_,?_,?_⟩ <;> apply (hmain _ (by omega)).mpr <;> omega

/-- An authenticated native shard count gives the exact native main-read length. -/
theorem native_main_read_prefix {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (ss : List Nat) (hj : 1<q.segs.length) (hc : cv tr tt q.segs[1].1 count=ss.length) :
    3+ss.length≤q.segs.length ∧
      ∀ i (hi : i<q.segs.length), tr.cell tt q.segs[i].1 main=1 ↔ i<3+ss.length := by
  obtain ⟨hfit,hmain⟩ := main_read_prefix hL q
  have hm := (hmain 1 hj).mpr (by omega)
  have he := congrArg Fp.toNat (WalkChain.main_count_constant hL q 1 hj hm)
  change cv tr tt q.segs[1].1 count=cv tr tt 0 count at he
  rw [hc] at he
  simpa only [←he] using And.intro hfit hmain

end ZkFormal.NearV3.Qv.Extract
