import ZkFormal.Near.Render.Proof.ShaFit2
import ZkFormal.Near.Render.Proof.AcctFacts
import ZkFormal.Near.Render.Proof.MrkFacts

/-!
# ZkFormal.Near.Render.Proof.ShaFit3 — SHA rows of the node, acct and mrk messages

`MsgsB ms`: every message has bytes `< 256` and fewer than `2^25` of them.
Node messages (`node_msgsB`), acct messages (`acct_msgsB`, `acct_rows`:
`70` rows per touched slot) and mrk messages (`mrk_msgsB`, `mrk_rows`: at
most `35` rows per hashed node, `64·hashed ≤ |recs n|`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- Every message is bytes, fewer than `2^25`. -/
def MsgsB (ms : List Msg) : Prop := ∀ m ∈ ms, (∀ x ∈ m.bytes, x < 256) ∧ m.bytes.length < 2 ^ 25

theorem msgsB_append {a b : List Msg} (ha : MsgsB a) (hb : MsgsB b) : MsgsB (a ++ b) := by
  intro m hm
  rcases List.mem_append.1 hm with h | h
  · exact ha m h
  · exact hb m h

theorem msgsB_flatMap {α : Type} {l : List α} {f : α → List Msg} (h : ∀ x ∈ l, MsgsB (f x)) :
    MsgsB (l.flatMap f) := by
  intro m hm
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hm
  exact h x hx m hm

theorem le_sum_of_mem {α : Type} (f : α → Nat) : ∀ {l : List α} {x : α}, x ∈ l → f x ≤ (l.map f).sum
  | _ :: l, _, .head _ => by simp
  | y :: l, x, .tail _ h => by have := le_sum_of_mem f h; simp; omega

section
variable {c : Claim} {e : Ext}

/-! ## node -/

theorem nodeAt_mem {n : Nat} (hn : n < e.ns.length) : (mkInfo c e).nodeAt n ∈ e.ns := by
  simp [Info.nodeAt, mkInfo_ns, Array.getD_eq_getD_getElem?, hn]

theorem node_msgsB (hg : Good c e) : MsgsB (nodeMsgs (mkInfo c e)) := by
  apply msgsB_flatMap
  intro n hn
  have hn' : n < e.ns.length := by simpa [mkInfo_ns] using hn
  have hmem := nodeAt_mem (c := c) hn'
  have h1 : sz0 ((mkInfo c e).nodeAt n) < 2 ^ 25 := by
    have := le_sum_of_mem nodeSize hmem
    have := hg.size
    simp only [revealedOf, Params.maxWitnessBytes] at *
    rw [nodeSize_eq] at *; omega
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨(pre_ok c e n).2, Nat.lt_of_le_of_lt (pre_ok c e n).1 h1⟩
  · exact ⟨(post_ok c e n).2, Nat.lt_of_le_of_lt (post_ok c e n).1 h1⟩

/-! ## acct -/

theorem acct_msgsB (hg : Good c e) : MsgsB (acctMsgs (mkInfo c e)) := by
  apply msgsB_flatMap
  intro k hk m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · obtain ⟨h1, h2, -⟩ := acct_pre hg k hk
    exact ⟨h2, by simp only [h1]; decide⟩
  · refine ⟨?_, by simp only [acct_post hg k hk]; decide⟩
    rw [vpost_eq hk]; exact toNats_lt _

theorem acct_rows (hg : Good c e) (hs : Small e) : rowsL (acctMsgs (mkInfo c e)) ≤ 70 * 256 := by
  simp only [rowsL, acctMsgs, sum_map_flatMap]
  have hl : (mkInfo c e).touched.length ≤ 256 := by rw [touched_len]; exact hs.touched
  have := Nat.mul_le_mul_left 70 hl
  refine Nat.le_trans (sum_map_le_mul _ 70 _ ?_) this
  intro k hk
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, (acct_pre hg k hk).1, acct_post hg k hk]
  decide

end

/-! ## mrk -/

namespace MrkGen

theorem shaN_lt (b : List Nat) : ∀ x ∈ shaN b, x < 256 := toNats_lt _

theorem levels_bytes (I : Info) : ∀ j, ∀ m ∈ levels I j, ∀ x ∈ m.dig, x < 256
  | 0, m, hm => by
    simp only [levels, List.mem_map, List.mem_range] at hm
    obtain ⟨r, _, rfl⟩ := hm; exact shaN_lt _
  | j + 1, m, hm => by
    simp only [levels, List.mem_map, List.mem_range] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    split
    · exact shaN_lt _
    · rename_i h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact levels_bytes I j _ (List.getElem_mem _)

theorem getD_mem_or {α : Type} (l : List α) (k : Nat) (d : α) : l.getD k d ∈ l ∨ l.getD k d = d := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k l.length with h | h
  · rw [List.getElem?_eq_getElem h]; exact .inl (List.getElem_mem _)
  · rw [List.getElem?_eq_none h]; exact .inr rfl

theorem dig_ok (I : Info) (m : MNode) (h : (∃ j, m ∈ levels I j) ∨ m = default) :
    m.dig.length ≤ 32 ∧ ∀ x ∈ m.dig, x < 256 := by
  rcases h with ⟨j, hj⟩ | rfl
  · exact ⟨by rw [levels_dig I j _ hj]; exact Nat.le_refl _, levels_bytes I j _ hj⟩
  · exact ⟨by decide, by intro x hx; cases hx⟩

/-- Digest windows of the levels: at most 32 bytes. -/
theorem lv_dig (I : Info) (j k : Nat) :
    ((((List.range (I.nRcpt + 2)).map (levels I)).getD j []).getD k default : MNode).dig.length ≤ 32 ∧
    ∀ x ∈ ((((List.range (I.nRcpt + 2)).map (levels I)).getD j []).getD k default : MNode).dig, x < 256 := by
  apply dig_ok
  rcases getD_mem_or ((List.range (I.nRcpt + 2)).map (levels I)) j [] with h | h
  · obtain ⟨j', -, hj⟩ := List.mem_map.1 h
    rcases getD_mem_or (((List.range (I.nRcpt + 2)).map (levels I)).getD j []) k default with h' | h'
    · rw [← hj] at h' ⊢; exact .inl ⟨j', h'⟩
    · exact .inr h'
  · rw [h]; exact .inr rfl

end MrkGen

theorem filterMap_rows {α : Type} (F : α → Option Msg) (E : α → List Rec) :
    ∀ l : List α, (∀ x ∈ l, ∀ m, F x = some m → (E x).length = 64 ∧ m.bytes.length ≤ 64) →
      64 * rowsL (l.filterMap F) ≤ 35 * (l.flatMap E).length
  | [], _ => by simp [rowsL]
  | x :: l, h => by
    have ih := filterMap_rows F E l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filterMap_cons, List.flatMap_cons, List.length_append]
    cases hF : F x with
    | none => simp only; omega
    | some m =>
      obtain ⟨h1, h2⟩ := h x (List.mem_cons_self ..) m hF
      have := rowsOf_mono h2
      have h35 : rowsOf 64 = 35 := by decide
      simp only [rowsL, List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem filterMap_rows' {α : Type} (F : α → Option Msg) (E : α → List Rec) (l : List α)
    (h : ∀ x ∈ l, ∀ m, F x = some m → (E x).length = 64 ∧ m.bytes.length ≤ 64) :
    rowsL (l.filterMap F) ≤ 35 * (l.flatMap E).length / 64 := by
  have := filterMap_rows F E l h
  omega

open MrkGen in
theorem mrk_rows (I : Info) (hn : I.nRcpt ≤ 256) : rowsL (mrkMsgs I) ≤ 13600 := by
  have hr := recs_len I.nRcpt
  rw [recs_eq] at hr
  unfold mrkMsgs
  refine Nat.le_trans (filterMap_rows' _ expand (mrkShape I.nRcpt) ?_) ?_
  · intro x _ m hm
    obtain ⟨j, i, h⟩ := x
    cases h with
    | false => simp at hm
    | true =>
      simp only [ite_true, Option.some.injEq] at hm
      subst hm
      have a := lv_dig I (j - 1) (2 * i)
      have b := lv_dig I (j - 1) (2 * i + 1)
      refine ⟨by rw [expand_len]; rfl, by simp only [List.length_append]; omega⟩
  · have := Nat.mul_le_mul_left 35 hr
    have := Nat.mul_le_mul_left 97 hn
    omega

open MrkGen in
theorem mrk_msgsB (I : Info) : MsgsB (mrkMsgs I) := by
  intro m hm
  simp only [mrkMsgs, List.mem_filterMap] at hm
  obtain ⟨⟨j, i, h⟩, -, hm⟩ := hm
  cases h with
  | false => simp at hm
  | true =>
    simp only [ite_true, Option.some.injEq] at hm
    subst hm
    have a := lv_dig I (j - 1) (2 * i)
    have b := lv_dig I (j - 1) (2 * i + 1)
    refine ⟨fun y hy => ?_, by simp only [List.length_append]; omega⟩
    rcases List.mem_append.1 hy with hy | hy
    · exact a.2 y hy
    · exact b.2 y hy

end ZkFormal.Near.Render
