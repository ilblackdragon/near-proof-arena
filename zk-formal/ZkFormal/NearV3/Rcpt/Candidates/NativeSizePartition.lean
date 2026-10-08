import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionarySize
import ZkFormal.NearV3.Rcpt.Candidates.DedupRender

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpec NearSpecV3

private theorem cost_partition {α : Type} (xs : List α) (dup : α → Bool) (cost full : α → Nat)
    (hd : ∀ x∈xs,dup x=true → cost x=12)
    (hn : ∀ x∈xs,dup x=false → cost x=full x) :
    (xs.map cost).sum=((xs.filter fun x => !dup x).map full).sum+
      12*(xs.length-(xs.filter fun x => !dup x).length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy => hd y (by simp [hy])) (fun y hy => hn y (by simp [hy]))
    have hl := List.length_filter_le (fun y => !dup y) xs
    cases h : dup x with
    | false =>
      have he := hn x (by simp) h
      simp only [List.map_cons,List.sum_cons,List.filter_cons,h,Bool.not_false,
        ite_true,List.length_cons,he]
      omega
    | true =>
      have he := hd x (by simp) h
      simp only [List.map_cons,List.sum_cons,List.filter_cons,h,Bool.not_true,
        Bool.false_eq_true,ite_false,List.length_cons,he]
      omega

/-- Exact source SIZE partition: skipped occurrences are charged twelve bytes,
computed occurrences use the native entry charge at the same public index. -/
theorem source_size_partition (sources : List SrcList) (bs : List SrcpB)
    (own : Nat) (rs : RcptV3Vs)
    (hlen : bs.length=sources.length)
    (hdup : ∀ i (hi : i<bs.length),(bs.getD i default).dup=Public.sourceDup sources i)
    (hskip : ∀ i (hi : i<bs.length),(bs.getD i default).dup=true → (bs.getD i default).L=12)
    (hcost : ∀ i,i<sources.length → Public.sourceDup sources i=false →
      entrySizeCharge (nativeEntryAt sources own rs bs i).entry=
        (bs.getD i default).L+33*(bs.getD i default).path.length) :
    DedupRender.size bs=((firstNativeEntries sources own rs bs).map entrySizeCharge).sum+
      12*(sources.length-(firstSourceIndices sources).length) := by
  have hh := cost_partition (List.range sources.length) (Public.sourceDup sources)
    (fun i => DedupRender.sizeStep (bs.getD i default))
    (fun i => entrySizeCharge (nativeEntryAt sources own rs bs i).entry)
    (by
      intro i hi hd
      have hb : i<bs.length := by have := List.mem_range.mp hi; omega
      have he : (bs.getD i default).dup=true := (hdup i hb).trans hd
      simp only [DedupRender.sizeStep,he,ite_true,Nat.add_zero,hskip i hb he])
    (by
      intro i hi hd
      have hsi := List.mem_range.mp hi
      have hb : i<bs.length := by omega
      have he : (bs.getD i default).dup=false := (hdup i hb).trans hd
      simpa only [DedupRender.sizeStep,he,Bool.false_eq_true,ite_false] using (hcost i hsi hd).symm)
  have he : (List.range sources.length).map (fun i => DedupRender.sizeStep (bs.getD i default))=
      bs.map DedupRender.sizeStep := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem
      (show i<bs.length by simpa only [List.length_map] using h2)]
  rw [he] at hh
  simpa only [DedupRender.size,firstNativeEntries,firstNativeSources,firstSourceIndices,
    List.map_map,Function.comp_def,List.length_range] using hh

end ZkFormal.NearV3.Rcpt.Candidates
