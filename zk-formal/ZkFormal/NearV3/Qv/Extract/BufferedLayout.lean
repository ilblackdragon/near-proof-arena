import ZkFormal.NearV3.Qv.Extract.EntryRows

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hm : tr.cell tt s mBuffer=1)
include hL hfit hw hs hm

/-- The entire suffix beginning at a shard word is a nonempty sequence of 24-byte entries. -/
theorem buffered_tail_layout {r : Nat} (hr : s≤r) (hb : r<s+n)
    (hp : tr.cell tt r shard=1) (hz : tr.cell tt r (sel 0)=1) :
    ∃ k, 0<k ∧ r+24*k=s+n ∧
      ∀ j, j<k → tr.cell tt (r+24*j) shard=1 ∧ tr.cell tt (r+24*j) (sel 0)=1 := by
  have aux : ∀ d r, s+n-r=d → s≤r → r<s+n → tr.cell tt r shard=1 →
      tr.cell tt r (sel 0)=1 → ∃ k, 0<k ∧ r+24*k=s+n ∧
        ∀ j, j<k → tr.cell tt (r+24*j) shard=1 ∧ tr.cell tt (r+24*j) (sel 0)=1 := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro r hd hr hb hp hz
      have he := buffered_entry_exit hL hfit hw hs hm hr hb hp hz
      rcases he with he|he
      · refine ⟨1,by omega,by omega,?_⟩
        intro j hj
        have hj0 : j=0 := by omega
        simpa only [hj0,Nat.mul_zero,Nat.add_zero] using And.intro hp hz
      · obtain ⟨k,hk,hend,hrows⟩ := ih (s+n-(r+24)) (by omega) (r+24) rfl (by omega) he.1 he.2.1 he.2.2.1
        refine ⟨k+1,by omega,by omega,?_⟩
        intro j hj
        by_cases hzj : j=0
        · simpa only [hzj,Nat.mul_zero,Nat.add_zero] using And.intro hp hz
        · have hh := hrows (j-1) (by omega)
          have hi : r+24+24*(j-1)=r+24*j := by omega
          simpa only [hi] using hh
  exact aux (s+n-r) r rfl hr hb hp hz

/-- A buffered record has exactly a four-byte header followed by complete entries. -/
theorem buffered_record_layout :
    ∃ k, n=4+24*k ∧ ∀ j, j<k →
      tr.cell tt (s+4+24*j) shard=1 ∧ tr.cell tt (s+4+24*j) (sel 0)=1 := by
  rcases buffered_header_exit hL hfit hw hs hm with he|he
  · refine ⟨0,by omega,?_⟩
    intro j hj; omega
  · obtain ⟨k,hk,hlen,hrows⟩ := buffered_tail_layout hL hfit hw hs hm
      (r:=s+4) (by omega) (by omega) he.2.1 he.2.2
    exact ⟨k,by omega,hrows⟩

end ZkFormal.NearV3.Qv.Extract.Parser
