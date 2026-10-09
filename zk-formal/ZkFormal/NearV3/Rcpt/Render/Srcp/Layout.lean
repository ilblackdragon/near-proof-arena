import ZkFormal.NearV3.Rcpt.Render.Srcp.Windows

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Last descriptor of a source list, including its empty-path case. -/
def lastKind (B : SrcpB) : Kind :=
  if B.path.length = 0 then .leaf 31 else .path (B.path.length - 1) 63

/-- The complete internal successor function; `none` marks a list boundary. -/
def nextKind (B : SrcpB) : Kind → Option Kind
  | .root => some (.leaf 0)
  | .leaf p => if p + 1 < 32 then some (.leaf (p + 1))
      else if 0 < B.path.length then some (.path 0 0) else none
  | .path i o => if o + 1 < 64 then some (.path i (o + 1))
      else if i + 1 < B.path.length then some (.path (i + 1) 0) else none

theorem next_last (B : SrcpB) : nextKind B (lastKind B) = none := by
  by_cases hp : B.path.length = 0
  · simp [lastKind, nextKind, hp]
  · simp [lastKind, nextKind, hp, show ¬ B.path.length - 1 + 1 < B.path.length by omega]

theorem kinds_first (B : SrcpB) : (kinds B).head? = some .root := by
  simp [kinds]

theorem kinds_last (B : SrcpB) : (kinds B).getLast? = some (lastKind B) := by
  by_cases hp : B.path.length = 0
  · simp [kinds, hp, lastKind, List.range_succ, List.getLast?_append]
  · obtain ⟨n, hn⟩ : ∃ n, B.path.length = n + 1 := ⟨B.path.length - 1, by omega⟩
    simp only [kinds, hn, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.getLast?_append]
    simp [lastKind, hn]

theorem firstAt {bs : List SrcpB} (h : SrcpWf bs) :
    (recs bs).getD 0 default = (0, Kind.root) := by
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  obtain ⟨n, hn⟩ : ∃ n, bs.length = n + 1 := ⟨bs.length - 1, by omega⟩
  simp [recs, hn, List.range_succ_eq_map, kinds]

theorem recs_last {bs : List SrcpB} (h : SrcpWf bs) :
    (recs bs).getLast? =
      some (bs.length - 1, lastKind (bs.getD (bs.length - 1) default)) := by
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  obtain ⟨n, hn⟩ : ∃ n, bs.length = n + 1 := ⟨bs.length - 1, by omega⟩
  unfold recs
  rw [hn, List.range_succ, List.flatMap_append, List.getLast?_append]
  simp [List.getLast?_map, kinds_last]

theorem lastAt {bs : List SrcpB} (h : SrcpWf bs) :
    (recs bs).getD (R bs - 1) default =
      (bs.length - 1, lastKind (bs.getD (bs.length - 1) default)) := by
  have hh := recs_last h
  rw [List.getLast?_eq_getElem?] at hh
  rw [List.getD_eq_getElem?_getD]
  unfold R
  rw [hh]
  rfl

end ZkFormal.NearV3.Render.SrcpGen
