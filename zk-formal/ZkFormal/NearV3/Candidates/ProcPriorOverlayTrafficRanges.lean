import ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficRows
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficRanges
open ZkFormal.Near

theorem split {α : Type} (a b : Nat) (f : Nat→List α) :
    (List.range (a+b)).flatMap f=(List.range a).flatMap f++
      (List.range b).flatMap (fun j=>f (a+j)) := by
  simp only [List.range_add,List.flatMap_append,List.flatMap_map]

theorem four {α : Type} (a b c n : Nat) (hab:a≤b) (hbc:b≤c) (hcn:c≤n)
    (f : Nat→Nat→List α) :
    (List.range n).flatMap (fun r=>if r<a then f 0 r else if r<b then f 1 (r-a)
      else if r<c then f 2 (r-b) else f 3 (r-c))=
      (List.range a).flatMap (f 0)++(List.range (b-a)).flatMap (f 1)++
      (List.range (c-b)).flatMap (f 2)++(List.range (n-c)).flatMap (f 3) := by
  have hn:n=a+((b-a)+((c-b)+(n-c))):=by omega
  conv => lhs; rw [hn,split,split,split]
  simp only [List.append_assoc]
  congr 1
  · apply flatMap_congr'
    intro r hr
    simp only [List.mem_range] at hr
    simp [hr]
  · congr 1
    · apply flatMap_congr'
      intro r hr
      simp only [List.mem_range] at hr
      simp only [show ¬a+r<a by omega,ite_false,show a+r<b by omega,ite_true,
        show a+r-a=r by omega]
    · congr 1
      · apply flatMap_congr'
        intro r hr
        simp only [List.mem_range] at hr
        simp only [show ¬a+(b-a+r)<a by omega,ite_false,
          show ¬a+(b-a+r)<b by omega,show a+(b-a+r)<c by omega,ite_true,
          show a+(b-a+r)-b=r by omega]
      · apply flatMap_congr'
        intro r hr
        simp only [List.mem_range] at hr
        simp only [show ¬a+(b-a+(c-b+r))<a by omega,ite_false,
          show ¬a+(b-a+(c-b+r))<b by omega,show ¬a+(b-a+(c-b+r))<c by omega,
          show a+(b-a+(c-b+r))-c=r by omega]

/-- A proved silent suffix may be omitted from a physical traffic inventory. -/
theorem truncate {α : Type} (used n : Nat) (hn:used≤n) (f : Nat→List α)
    (hz:∀r,used≤r→r<n→f r=[]) :
    (List.range n).flatMap f=(List.range used).flatMap f := by
  rw [show n=used+(n-used) by omega,split]
  have he:(List.range (n-used)).flatMap (fun j=>f (used+j))=[]:=by
    apply List.flatMap_eq_nil_iff.mpr
    intro j hj
    have :=List.mem_range.mp hj
    exact hz _ (by omega) (by omega)
  rw [he,List.append_nil]
end ZkFormal.NearV3.Candidates.ProcPriorOverlayTrafficRanges
