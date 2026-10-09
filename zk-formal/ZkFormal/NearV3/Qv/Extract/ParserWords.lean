import ZkFormal.NearV3.Qv.Extract.ParserModes
import ZkFormal.Near.Extract.RcptFacts

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

theorem phase_exclusive {x : Nat} (hx : x∈phases) (h1 : tr.cell tt r x=1) :
    tr.cell tt r act=1 ∧ ∀ y∈phases, y≠x → tr.cell tt r y=0 := by
  have hh := con hL hr hw (e:=sub (sum (phases.map c)) (c act)) (by simp [constraints])
  simp only [eval_sub,eval_c,RcptProof.eval_sum_map_c] at hh
  have he : RcptProof.fsum (tr.cell tt r) phases=tr.cell tt r act := by grind
  apply RcptProof.oneHot_of (tr.cell tt r) phases (by decide) (tr.cell tt r act)
    _ (isBool hL hr hw (x:=act) (by simp)) he hx h1
  intro y hy
  simp only [phases,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact isBool hL hr hw (by simp [modes])

theorem selector_exclusive (ha : tr.cell tt r act=1) (hm : tr.cell tt r mRaw=0)
    {i : Nat} (hi : i<8) (h1 : tr.cell tt r (sel i)=1) :
    ∀ j, j<8 → j≠i → tr.cell tt r (sel j)=0 := by
  have hh := con hL hr hw (e:=sub (sum (selectors.map c)) (sub (c act) (c mRaw))) (by simp [constraints])
  simp only [eval_sub,eval_c,RcptProof.eval_sum_map_c,ha,hm] at hh
  have he : RcptProof.fsum (tr.cell tt r) selectors=1 := by grind
  have hx : sel i∈selectors := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have h := RcptProof.oneHot_of (tr.cell tt r) selectors (by decide) 1
    (fun x hx => isBool hL hr hw (by simp [hx])) (Or.inr rfl) he hx h1
  intro j hj hji
  exact h.2 _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩) (by unfold sel; omega)

theorem selected_word_byte {i x : Nat} (hi : i<8) (hsel : tr.cell tt r (sel i)=1)
    (hx : x∈[header,firstIndex,nextIndex]) (hphase : tr.cell tt r x=1) :
    tr.cell tt r byte=tr.cell tt r (reg i) := by
  have hxp : x∈phases := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> simp [phases]
  have hp := phase_exclusive hL hr hw hxp hphase
  have hsh := hp.2 shard (by simp [phases]) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> decide)
  have hraw := hp.2 mRaw (by simp [phases]) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> decide)
  have hsum := con hL hr hw (e:=sub (sum (phases.map c)) (c act)) (by simp [constraints])
  simp [eval_sub,phases,eval_c,hsh,hraw,hp.1] at hsum
  have hh := con hL hr hw (e:=mul3 (c (sel i)) (sum [c header,c firstIndex,c nextIndex])
      (sub (c byte) (c (reg i)))) (by
    unfold constraints
    have hm := List.mem_map_of_mem (f:=fun i => mul3 (c (sel i)) (sum [c header,c firstIndex,c nextIndex])
      (sub (c byte) (c (reg i)))) (List.mem_range.mpr hi)
    simp only [List.mem_append,hm,true_or,or_true])
  simp [eval_mul3,eval_sub,eval_c,hsel] at hh
  grind

theorem register_carry (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hh : headerEnd.eval tr tt r pub=0) (he : entryEnd.eval tr tt r pub=0)
    (i : Nat) (hi : i<8) : tr.cell tt (r+1) (reg i)=tr.cell tt r (reg i) := by
  have hm := List.mem_map_of_mem (f:=fun i => mul3 (c cont) (Dsl.not (.add headerEnd entryEnd))
    (sub (n (reg i)) (c (reg i)))) (List.mem_range.mpr hi)
  have h := con hL hr hw (e:=mul3 (c cont) (Dsl.not (.add headerEnd entryEnd))
    (sub (n (reg i)) (c (reg i)))) (by unfold constraints; simp only [List.mem_append,hm,true_or,or_true])
  simp only [eval_mul3,eval_not,eval_add,eval_sub,eval_n,eval_c,hc,hh,he,Nat.mod_eq_of_lt hn] at h
  grind

end ZkFormal.NearV3.Qv.Extract.Parser
