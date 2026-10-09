import ZkFormal.NearV3.Rcpt.Extract.Srcp.Defs

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra

/-- Number of SHA messages in the source-proof lane, one leaf plus each path node. -/
def sourceCount (bs : List SrcpB) : Nat :=
  (bs.map fun B => 1 + B.path.length).sum

theorem sourceCount_append (xs ys : List SrcpB) :
    sourceCount (xs ++ ys) = sourceCount xs + sourceCount ys := by
  simp [sourceCount, List.sum_append]

private theorem take_next {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using congrArg (List.cons a) (ih i (by simpa using hi))

theorem sourceCount_next (bs : List SrcpB) (i : Nat) (hi : i < bs.length) :
    sourceCount (bs.take (i + 1)) = sourceCount (bs.take i) + 1 + bs[i].path.length := by
  rw [take_next bs i hi, sourceCount_append]
  simp [sourceCount, Nat.add_assoc]

/-- The local successor constraints pin each leaf to the global prefix count. -/
theorem source_ql {bs : List SrcpB} (h : SrcpWf bs) (i : Nat) (hi : i < bs.length) :
    bs[i].ql = 1 + sourceCount (bs.take i) := by
  induction i with
  | zero => simpa [sourceCount] using h.q0 hi
  | succ i ih =>
    rw [h.qnext i hi, SrcpB.lastQ, ih (by omega), sourceCount_next bs i (by omega)]
    omega

/-- Each block owns a closed, nonoverlapping interval of source message indices. -/
theorem source_interval_before {bs : List SrcpB} (h : SrcpWf bs)
    (i j : Nat) (hi : i < bs.length) (hj : j < bs.length) (hij : i < j) :
    bs[i].lastQ < bs[j].ql := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [h.qnext j hj]
    by_cases he : i = j
    · subst i; omega
    · have hh := ih (by omega) (by omega)
      simp only [SrcpB.lastQ] at *
      omega

/-- Total source indices fit the existing source table row cap. -/
theorem sourceCount_le_rows (bs : List SrcpB) : sourceCount bs ≤ srcpRows bs := by
  induction bs with
  | nil => simp [sourceCount, srcpRows]
  | cons B bs ih =>
    simp only [sourceCount, srcpRows, List.map_cons, List.sum_cons] at *
    omega

theorem sourceCount_take_le (bs : List SrcpB) (i : Nat) :
    sourceCount (bs.take i) ≤ sourceCount bs := by
  have hh := sourceCount_append (bs.take i) (bs.drop i)
  rw [List.take_append_drop] at hh
  omega

/-- Last message index is bounded by the table's actual semantic row count. -/
theorem source_lastQ_le {bs : List SrcpB} (h : SrcpWf bs) (i : Nat) (hi : i < bs.length) :
    bs[i].lastQ ≤ sourceCount bs := by
  have hq := source_ql h i hi
  have hn := sourceCount_next bs i hi
  have ht := sourceCount_take_le bs (i + 1)
  simp only [SrcpB.lastQ]
  omega

/-- Canonical field encoding follows from the original row cap. -/
theorem source_msgId_lt {bs : List SrcpB} (h : SrcpWf bs) (i q : Nat) (hi : i < bs.length)
    (hq : q ≤ bs[i].lastQ) : msgId K_SRC q < P := by
  have h1 := source_lastQ_le h i hi
  have h2 := sourceCount_le_rows bs
  have h3 := h.rows
  simp only [SrcpV3.maxLog] at h3
  unfold msgId K_SRC P
  omega

end ZkFormal.NearV3
