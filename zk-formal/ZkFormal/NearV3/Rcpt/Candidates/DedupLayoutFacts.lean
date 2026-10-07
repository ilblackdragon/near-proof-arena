import ZkFormal.NearV3.Rcpt.Candidates.DedupAdjacency
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableFacts

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open Render.SrcpGen

theorem mem_recs {bs : List SrcpB} {r : Nat × Kind} (h : r ∈ recs bs) :
    r.1 < bs.length ∧ r.2 ∈ kinds (bs.getD r.1 default) := by
  simp only [recs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, k, hk, he⟩ := h
  subst r
  exact ⟨hi, hk⟩

theorem descriptor_mem {bs : List SrcpB} {r : Nat} (hr : r < R bs) :
    (recs bs).getD r default ∈ recs bs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact List.getElem_mem _

theorem none_last (B : SrcpB) (k : Kind) (hk : k ∈ kinds B)
    (hn : nextKind B k = none) : k = lastKind B := by
  cases hd : B.dup
  · have hk' : k ∈ Render.SrcpGen.kinds B := by simpa [kinds, hd] using hk
    have hn' : Render.SrcpGen.nextKind B k = none := by simpa [nextKind, hd] using hn
    simpa [lastKind, hd] using Render.SrcpGen.none_last B k hk' hn'
  · have he : k = .root := by simpa [kinds, hd] using hk
    simpa [lastKind, hd] using he

theorem firstAt {bs : List SrcpB} {repeated : Nat → Bool} (h : TableFacts bs repeated) :
    (recs bs).getD 0 default = (0, Kind.root) := by
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  obtain ⟨n, hn⟩ : ∃ n, bs.length = n + 1 := ⟨bs.length - 1, by omega⟩
  have hd : bs[0].dup = false := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some] using h.first_dup
  simp [recs, hn, List.range_succ_eq_map, kinds, hd, Render.SrcpGen.kinds]

theorem R_ge_33 {bs : List SrcpB} {repeated : Nat → Bool} (h : TableFacts bs repeated) :
    33 ≤ R bs := by
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  have hb : bs.getD 0 default ∈ bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    exact List.getElem_mem hp
  have hm : bs.getD 0 default ∈ bs.filter (fun B => !B.dup) :=
    List.mem_filter.mpr ⟨hb, by rw [h.first_dup]; rfl⟩
  have hf : 0 < (bs.filter (fun B => !B.dup)).length := by
    cases hs : bs.filter (fun B => !B.dup) with
    | nil => simp [hs] at hm
    | cons a rest => simp
  rw [R_accounting]
  omega

theorem secondAt {bs : List SrcpB} {repeated : Nat → Bool} (h : TableFacts bs repeated) :
    (recs bs).getD 1 default = (0, Kind.leaf 0) := by
  have hr := R_ge_33 h
  have ha := adjAt (bs := bs) (r := 0) (by omega)
  rw [firstAt h] at ha
  rcases ha with ⟨hn, hi⟩ | ⟨hn, hi⟩
  · have he : ((recs bs).getD 1 default).2 = .leaf 0 := by
      simpa only [nextKind, h.first_dup, Bool.false_eq_true, ite_false,
        Render.SrcpGen.nextKind, Option.some.injEq] using hn.symm
    exact Prod.ext hi he
  · simp only [nextKind, h.first_dup, Bool.false_eq_true, ite_false,
      Render.SrcpGen.nextKind] at hn
    cases hn

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
