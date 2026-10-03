import ReexecNpai.Trie.Lemmas
import ReexecNpai.Canon

/-!
# Pure lemmas for the parse phase

* `decRec_cs`: one decoded record consumes a suffix and adds exactly one
  revealed node to the stack (`cntL`), hence `decRecs_cnt`;
* `rb_treeAt`: the revealed bytes of `treeAt j` are the sum of `entRev` over
  the entries of its subtree interval.
-/

namespace ReexecNpai
namespace ParseProof

open NearSpec NearSpec.TransferV1

/-! ## Decoder: suffixes and node counts -/

/-- Total number of revealed nodes on a stack. -/
def cntL : List PTrie → Nat
  | [] => 0
  | t :: s => cntT t + cntL s

theorem cntL_append : ∀ a b : List PTrie, cntL (a ++ b) = cntL a + cntL b
  | [], b => by simp [cntL]
  | x :: a, b => by simp only [List.cons_append, cntL, cntL_append a b]; omega

theorem cntL_reverse : ∀ a : List PTrie, cntL a.reverse = cntL a
  | [] => rfl
  | x :: a => by simp only [List.reverse_cons, cntL_append, cntL_reverse a, cntL]; omega

/-- `r` is a suffix of `bs`. -/
def Suf (r bs : Bytes) : Prop := ∃ k, r = bs.drop k

theorem Suf.trans {a b c : Bytes} (h1 : Suf a b) (h2 : Suf b c) : Suf a c := by
  obtain ⟨k1, rfl⟩ := h1; obtain ⟨k2, rfl⟩ := h2
  exact ⟨k2 + k1, by rw [List.drop_drop]⟩

theorem Suf.refl (a : Bytes) : Suf a a := ⟨0, by simp⟩

theorem takeN_suf {n : Nat} {bs h r : Bytes} (e : takeN n bs = some (h, r)) : Suf r bs := by
  obtain ⟨rfl, rfl⟩ := takeN_some e
  exact ⟨h.length, by simp⟩

theorem readLE_suf {w x : Nat} {bs r : Bytes} (e : readLE w bs = some (x, r)) : Suf r bs := by
  simp only [readLE, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e
  obtain ⟨h, t, e', -, rfl⟩ := e
  exact takeN_suf e'

theorem decVal_suf {hv : Bool} {bs r : Bytes} {vo : Option Bytes} (e : decVal hv bs = some (vo, r)) :
    Suf r bs := by
  cases hv with
  | false =>
    simp only [decVal, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e; exact Suf.refl _
  | true =>
    simp only [decVal, ite_true] at e
    cases hr : readBorshBytes bs with
    | none => simp [hr] at e
    | some p =>
      obtain ⟨v, r'⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨-, rfl⟩ := e
      obtain ⟨e1, -⟩ := readBorshBytes_some hr
      exact ⟨(borshBytes v).length, by rw [e1]; simp⟩

theorem popN_inv' : ∀ (k : Nat) (stk cs s0 : List PTrie), popN k stk = some (cs, s0) →
    stk = cs.reverse ++ s0
  | 0, stk, cs, s0, h => by
    simp only [popN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | k + 1, [], cs, s0, h => by simp [popN] at h
  | k + 1, x :: stk, cs, s0, h => by
    simp only [popN] at h
    cases hp : popN k stk with
    | none => simp [hp] at h
    | some p =>
      obtain ⟨cs', s0'⟩ := p
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [popN_inv' k stk _ _ hp]
      simp

theorem mkKids_cnt : ∀ (n bm ex : Nat) (hs : List Bytes) (cs : List PTrie) (kids : Kids),
    mkKids n bm ex hs cs = some kids → cntKids kids = cntL cs
  | 0, bm, ex, [], [], kids, h => by
    simp only [mkKids, Option.some.injEq] at h; subst h; simp [cntKids, cntL]
  | 0, bm, ex, _ :: _, _, kids, h => by simp [mkKids] at h
  | 0, bm, ex, [], _ :: _, kids, h => by simp [mkKids] at h
  | n + 1, bm, ex, hs, cs, kids, h => by
    simp only [mkKids] at h
    split at h
    · split at h
      · simp at h
      · rename_i x hs'
        split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · rename_i c cs'
              cases hk : mkKids n (bm / 2) (ex / 2) hs' cs' with
              | none => simp [hk] at h
              | some k' =>
                simp only [hk, Option.map_some, Option.some.injEq] at h
                subst h
                have ih := mkKids_cnt n _ _ hs' cs' k' hk
                simp only [cntKids, cntL, ih]
        · cases hk : mkKids n (bm / 2) (ex / 2) hs' cs with
          | none => simp [hk] at h
          | some k' =>
            simp only [hk, Option.map_some, Option.some.injEq] at h
            subst h
            have ih := mkKids_cnt n _ _ hs' cs k' hk
            simp only [cntKids, cntT, ih, Nat.zero_add]
    · split at h
      · simp at h
      · cases hk : mkKids n (bm / 2) (ex / 2) hs cs with
        | none => simp [hk] at h
        | some k' =>
          simp only [hk, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [cntKids, mkKids_cnt n _ _ hs cs k' hk]

theorem decLeaf_cs {hasVal : Bool} {stk stk' : List PTrie} {bs bs' : Bytes}
    (h : decLeaf hasVal stk bs = some (stk', bs')) : Suf bs' bs ∧ cntL stk' = cntL stk + 1 := by
  unfold decLeaf at h
  split at h; · simp at h
  rename_i vo bs1 h1
  split at h; · simp at h
  rename_i tag bs2 h2
  split at h; · simp at h
  split at h; · simp at h
  rename_i hl bs3 h3
  split at h; · simp at h
  rename_i hp bs4 h4
  split at h; · simp at h
  rename_i key h5
  split at h; · simp at h
  rename_i len bs5 h6
  split at h; · simp at h
  rename_i hh bs6 h7
  split at h; · simp at h
  rename_i mm bs7 h8
  cases hs : mkSlot vo len hh with
  | none => simp [hs] at h
  | some s =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(readLE_suf h8).trans ((takeN_suf h7).trans ((readLE_suf h6).trans ((takeN_suf h4).trans
      ((readLE_suf h3).trans ((readLE_suf h2).trans (decVal_suf h1)))))), ?_⟩
    simp only [cntL, cntT]; omega

theorem decExt_cs {stk stk' : List PTrie} {bs bs' : Bytes}
    (h : decExt stk bs = some (stk', bs')) : Suf bs' bs ∧ cntL stk' = cntL stk + 1 := by
  unfold decExt at h
  split at h; · simp at h
  rename_i e bs1 h1
  split at h; · simp at h
  split at h; · simp at h
  rename_i tag bs2 h2
  split at h; · simp at h
  split at h; · simp at h
  rename_i hl bs3 h3
  split at h; · simp at h
  rename_i hp bs4 h4
  split at h; · simp at h
  rename_i key h5
  split at h; · simp at h
  rename_i hh bs5 h6
  split at h; · simp at h
  rename_i mm bs6 h7
  have hsuf : Suf bs6 bs := (readLE_suf h7).trans ((takeN_suf h6).trans ((takeN_suf h4).trans
      ((readLE_suf h3).trans ((readLE_suf h2).trans (readLE_suf h1)))))
  split at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i c s0
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hsuf, by simp only [cntL, cntT]; omega⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hsuf, by simp only [cntL, cntT]; omega⟩

theorem decBranch_cs {kind : Nat} {stk stk' : List PTrie} {bs bs' : Bytes}
    (h : decBranch kind stk bs = some (stk', bs')) : Suf bs' bs ∧ cntL stk' = cntL stk + 1 := by
  unfold decBranch at h
  split at h; · simp at h
  rename_i vo bs1 h1
  split at h; · simp at h
  rename_i ex bs2 h2
  split at h; · simp at h
  rename_i tag bs3 h3
  have hs3 : Suf bs3 bs := (readLE_suf h3).trans ((readLE_suf h2).trans (decVal_suf h1))
  by_cases k4 : kind = 4
  · subst k4
    simp only [ite_true] at h
    have ht : tag = 1 := Classical.byContradiction fun ht => by simp [ht] at h
    simp only [ht, ne_eq, not_true_eq_false, ite_false] at h
    split at h; · simp at h
    rename_i bm bs5 h5
    split at h; · simp at h
    rename_i slots bs6 h6
    split at h; · simp at h
    rename_i mm bs7 h7
    split at h; · simp at h
    rename_i cs s0 h9
    cases hk : mkKids 16 bm ex (chunks32 (popc 16 bm) slots) cs with
    | none => simp [hk] at h
    | some kids =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(readLE_suf h7).trans ((takeN_suf h6).trans ((readLE_suf h5).trans hs3)), ?_⟩
      rw [popN_inv' _ _ _ _ h9]
      simp only [cntL, cntT, cntL_append, cntL_reverse, mkKids_cnt _ _ _ _ _ _ hk]
      omega
  · simp only [k4, ite_false] at h
    have ht : tag = 2 := Classical.byContradiction fun ht => by simp [ht] at h
    simp only [ht, ne_eq, not_true_eq_false, ite_false] at h
    cases hr : readU32 bs3 with
    | none => simp [hr] at h
    | some p =>
    obtain ⟨len, bs4⟩ := p
    cases ht32 : takeN 32 bs4 with
    | none => simp [hr, ht32] at h
    | some q =>
    obtain ⟨hh, bs5⟩ := q
    simp only [hr, ht32, Option.map_some] at h
    split at h; · simp at h
    rename_i bm bs6 h6
    split at h; · simp at h
    rename_i slots bs7 h7
    split at h; · simp at h
    rename_i mm bs8 h8
    cases hs : mkSlot vo len hh with
    | none => simp [hs] at h
    | some s =>
    simp only [hs, Option.map_some] at h
    split at h; · simp at h
    rename_i cs s0 h9
    cases hk : mkKids 16 bm ex (chunks32 (popc 16 bm) slots) cs with
    | none => simp [hk] at h
    | some kids =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(readLE_suf h8).trans ((takeN_suf h7).trans ((readLE_suf h6).trans ((takeN_suf ht32).trans
        ((readLE_suf hr).trans hs3)))), ?_⟩
      rw [popN_inv' _ _ _ _ h9]
      simp only [cntL, cntT, cntL_append, cntL_reverse, mkKids_cnt _ _ _ _ _ _ hk]
      omega

theorem decRec_cs {stk stk' : List PTrie} {bs bs' : Bytes} (h : decRec stk bs = some (stk', bs')) :
    Suf bs' bs ∧ cntL stk' = cntL stk + 1 := by
  cases bs with
  | nil => simp [decRec] at h
  | cons kd bs0 =>
    simp only [decRec] at h
    have hs : Suf bs0 (kd :: bs0) := ⟨1, rfl⟩
    split at h
    · obtain ⟨a, b⟩ := decLeaf_cs h; exact ⟨a.trans hs, b⟩
    · split at h
      · obtain ⟨a, b⟩ := decLeaf_cs h; exact ⟨a.trans hs, b⟩
      · split at h
        · obtain ⟨a, b⟩ := decExt_cs h; exact ⟨a.trans hs, b⟩
        · split at h
          · obtain ⟨a, b⟩ := decBranch_cs h; exact ⟨a.trans hs, b⟩
          · simp at h

theorem decRecs_cnt : ∀ (n : Nat) (stk : List PTrie) (bs : Bytes) (stk' : List PTrie) (bs' : Bytes),
    decRecs n stk bs = some (stk', bs') → cntL stk' = cntL stk + n
  | 0, stk, bs, stk', bs', h => by
    simp only [decRecs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, stk, bs, stk', bs', h => by
    simp only [decRecs] at h
    split at h
    · simp at h
    · rename_i s1 b1 h1
      have := (decRec_cs h1).2
      have := decRecs_cnt n s1 b1 stk' bs' h
      omega

theorem decRecs_add' : ∀ (a b : Nat) (stk : List PTrie) (bs : Bytes) (s : List PTrie) (r : Bytes),
    decRecs a stk bs = some (s, r) → decRecs (a + b) stk bs = decRecs b s r
  | 0, b, stk, bs, s, r, h => by
    simp only [decRecs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | a + 1, b, stk, bs, s, r, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [decRecs] at h ⊢
    split at h
    · simp at h
    · next stk' bs' _ => exact decRecs_add' a b stk' bs' s r h

end ParseProof
end ReexecNpai
