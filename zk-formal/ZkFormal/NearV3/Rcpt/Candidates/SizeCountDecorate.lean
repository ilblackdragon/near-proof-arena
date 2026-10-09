import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount

private theorem decorate_empty {α β γ : Type} (xs : List α) (f : α → List β)
    (g : α → β → γ) (h : xs.flatMap f=[]) :
    xs.flatMap (fun a => (f a).map (g a))=[] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.append_eq_nil_iff] at h
    simp [h.1,ih h.2]

/-- Adding a row-dependent authenticated component to traffic preserves the
unique physical supplier. This does not assume counters agree on other rows. -/
theorem decorate_singleton {α β γ : Type} [DecidableEq α]
    (xs : List α) (f : α → List β) (g : α → β → γ) (a : α) (b : β)
    (ha : a∈xs) (hf : f a=[b]) (h : xs.flatMap f=[b]) :
    xs.flatMap (fun a => (f a).map (g a))=[g a b] := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
    by_cases hc : c=a
    · subst c
      simp only [List.flatMap_cons,hf,List.singleton_append,List.cons.injEq] at h
      have hz : xs.flatMap (fun a => (f a).map (g a))=[] := decorate_empty xs f g h.2
      simp [hf,hz]
    · have hat : a∈xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hc)
      have hm : b∈xs.flatMap f := List.mem_flatMap.mpr ⟨a,hat,by simp [hf]⟩
      have hlen := congrArg List.length h
      simp only [List.flatMap_cons,List.length_append,List.length_singleton] at hlen
      have hpos : 0<(xs.flatMap f).length := List.length_pos_iff.mpr (by
        intro hz; simp [hz] at hm)
      have hz : f c=[] := List.length_eq_zero_iff.mp (by omega)
      have ht : xs.flatMap f=[b] := by simpa [hz] using h
      simp [hz,ih hat ht]

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
