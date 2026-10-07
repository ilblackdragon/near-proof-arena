import ZkFormal.NearV3.Rcpt.Candidates.SourcePublic
import ZkFormal.Near.Link.Bus

namespace ZkFormal.NearV3.Rcpt.Candidates.SourcePublic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open NearSpecV3 (SrcList)

/-- Natural form of the candidate public source record. -/
def recordNat (sources : List SrcList) (j : Nat) : Msg :=
  [j, (Public.sourceDup sources j).toNat, (sourceRepeated sources j).toNat] ++
    (sources.getD j ⟨[],0,[]⟩).root.map UInt8.toNat

def records (sources : List SrcList) : List Msg :=
  (List.range sources.length).map (recordNat sources)

def viewRecord (B : SrcpB) (rep : Bool) : Msg := [B.j, B.dup.toNat, rep.toNat]++B.root

theorem recordNat_field (sources : List SrcList) {j : Nat} (hj : j<sources.length) :
    (recordNat sources j).toFp=Public.recordValues plan j ((payload sources).getD j []) := by
  rw [record sources hj]
  cases hd : Public.sourceDup sources j <;> cases hp : sourceRepeated sources j <;>
    simp only [recordNat, Msg.toFp, hd, hp, Bool.false_eq_true, ite_false, ite_true,
      List.map_append, List.map_cons, List.map_nil, List.map_map] <;> rfl

theorem recordNat_canon (sources : List SrcList) {j : Nat} (hj : j<P) :
    Link.Canon (recordNat sources j) := by
  intro x hx
  simp only [recordNat, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | hx
  · exact hj
  · cases Public.sourceDup sources j <;> decide +kernel
  · cases sourceRepeated sources j <;> decide +kernel
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.lt_trans (UInt8.toNat_lt _) (by decide)

theorem recordNat_decode {sources : List SrcList} {j : Nat} {B : SrcpB} {rep : Bool}
    (he : viewRecord B rep=recordNat sources j) :
    B.j=j ∧ B.dup=Public.sourceDup sources j ∧ rep=sourceRepeated sources j ∧
      toBytes B.root=(sources.getD j ⟨[],0,[]⟩).root := by
  simp only [viewRecord, recordNat, List.cons_append, List.nil_append, List.cons.injEq] at he
  have bitinj : ∀ a b : Bool, a.toNat=b.toNat → a=b := by
    intro a b; cases a <;> cases b <;> simp
  refine ⟨he.1, bitinj _ _ he.2.1, bitinj _ _ he.2.2.1, ?_⟩
  · rw [he.2.2.2]
    simp [toBytes, List.map_map, Function.comp_def, UInt8.ofNat_toNat]

/-- Exact public SRC counts authenticate the key index, both duplicate flags and
the source root of every extracted view. Canonicality excludes field aliases. -/
theorem bind_record {sources : List SrcList} (hlen : sources.length<P)
    {views : List Msg}
    (hbal : ∀ m, cnt views m=cnt (records sources) m)
    {B : SrcpB} {rep : Bool} (hm : viewRecord B rep∈views)
    (hcan : Link.Canon (viewRecord B rep)) :
    B.j<sources.length ∧ B.dup=Public.sourceDup sources B.j ∧ rep=sourceRepeated sources B.j ∧
      toBytes B.root=(sources.getD B.j ⟨[],0,[]⟩).root := by
  have hh := Link.cnt_pos_of_mem hm
  rw [hbal] at hh
  obtain ⟨m, hm, he⟩ := Link.cnt_pos.mp hh
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have heNat := Link.toFp_inj hcan (recordNat_canon sources (by omega : j<P)) he.symm
  have hv := recordNat_decode heNat
  exact ⟨by omega, by simpa only [hv.1] using hv.2.1,
    by simpa only [hv.1] using hv.2.2.1, by simpa only [hv.1] using hv.2.2.2⟩

/-- Equal field multiplicities also fix the number of source occurrences. -/
theorem bind_length {sources : List SrcList} {views : List Msg}
    (hbal : ∀ m, cnt views m=cnt (records sources) m) : views.length=sources.length := by
  have hp : (views.map Msg.toFp).Perm ((records sources).map Msg.toFp) := by
    apply List.perm_iff_count.mpr
    exact hbal
  simpa [records] using hp.length_eq

end ZkFormal.NearV3.Rcpt.Candidates.SourcePublic
