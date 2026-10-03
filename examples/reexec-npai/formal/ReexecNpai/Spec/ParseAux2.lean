import ReexecNpai.Spec.ParseAux1
import ReexecNpai.Spec.ParseInv

/-!
# Revealed bytes of the arena trees

`rb_treeAt`: in a well-formed arena, `(treeAt j).revealedBytes` is the sum of
`entRev` over the subtree interval `[lo j, j]` — every entry's `entRev` is
exactly its node's own share of `PTrie.revealedBytes`.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace ReexecNpai
namespace ParseProof

open NearSpec NearSpec.TransferV1

/-- `Σ_{i < n} f (a + i)`. -/
def ssum (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | a, n + 1 => f a + ssum f (a + 1) n

theorem ssum_add (f : Nat → Nat) : ∀ a n m, ssum f a (n + m) = ssum f a n + ssum f (a + n) m := by
  intro a n m
  induction n generalizing a with
  | zero => simp [ssum]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [ssum, ih (a + 1)]
    rw [show a + 1 + n = a + (n + 1) by omega]; omega

theorem ssum_succ_right (f : Nat → Nat) (a n : Nat) : ssum f a (n + 1) = ssum f a n + f (a + n) := by
  rw [ssum_add]; simp [ssum]

theorem ssum_shift (f : Nat → Nat) : ∀ a n, ssum f (a + 1) n = ssum (fun i => f (i + 1)) a n := by
  intro a n
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [ssum, ih (a + 1)]

theorem ssum_congr (f g : Nat → Nat) : ∀ a n, (∀ i, a ≤ i → i < a + n → f i = g i) →
    ssum f a n = ssum g a n := by
  intro a n h
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [ssum]
    rw [h a (Nat.le_refl _) (by omega), ih (a + 1) (fun i h1 h2 => h i (by omega) (by omega))]

theorem foldl_ssum (g : Ent → Nat) : ∀ (l : List Ent) (acc : Nat),
    (l.map g).foldl (· + ·) acc = acc + ssum (fun i => g (l.getD i default)) 0 l.length
  | [], acc => by simp [ssum]
  | x :: l, acc => by
    simp only [List.map_cons, List.foldl_cons, List.length_cons, ssum, foldl_ssum g l]
    rw [ssum_shift]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem revSum_eq (pb : Bytes) (A : List Ent) :
    revSum pb A = ssum (fun i => entRev pb (A.getD i default)) 0 A.length := by
  unfold revSum; rw [foldl_ssum]; simp

theorem pseg_length {pb : Bytes} {a n : Nat} (h1 : PF ≤ a) (h2 : a + n ≤ PF + pb.length) :
    (pseg pb a n).length = n := by
  simp [pseg]; omega

theorem u16_len (x : Nat) : (u16 x).length = 2 := leN_length 2 x
theorem u32_len (x : Nat) : (u32 x).length = 4 := leN_length 4 x
theorem u64_len (x : Nat) : (u64 x).length = 8 := leN_length 8 x

theorem nPres_cons (x : Option (Option Bytes)) (r : List (Option (Option Bytes))) :
    nPres (x :: r) = nPres r + (if x = none then 0 else 1) := by
  unfold nPres; rw [List.countP_cons]; cases x <;> simp

theorem slotBytes_length : ∀ (ks : List (Option (Option Bytes))) (chs : List Bytes),
    (∀ s ∈ ks, match s with | some (some h) => h.length = 32 | _ => True) →
    (∀ x ∈ chs, x.length = 32) → chs.length = nRev ks →
    (slotBytes ks chs).length = 32 * nPres ks
  | [], chs, _, _, _ => by simp [slotBytes, nPres]
  | none :: r, chs, h1, h2, h3 => by
    simp only [slotBytes, nPres_cons, ite_true]
    rw [slotBytes_length r chs (fun s hs => h1 s (by simp [hs])) h2 (by rw [h3, nRev_cons]; simp)]
    omega
  | some (some h) :: r, chs, h1, h2, h3 => by
    have hh : h.length = 32 := h1 (some (some h)) (by simp)
    simp only [slotBytes, nPres_cons, List.length_append, hh, reduceCtorEq, ite_false]
    rw [slotBytes_length r chs (fun s hs => h1 s (by simp [hs])) h2 (by rw [h3, nRev_cons]; simp)]
    omega
  | some none :: r, chs, h1, h2, h3 => by
    cases chs with
    | nil => rw [nRev_cons] at h3; simp at h3
    | cons c cs =>
      have hc : c.length = 32 := h2 c (by simp)
      simp only [slotBytes, nPres_cons, List.length_append, List.headD_cons, List.tail_cons, hc,
        reduceCtorEq, ite_false]
      rw [slotBytes_length r cs (fun s hs => h1 s (by simp [hs])) (fun x hx => h2 x (by simp [hx]))
        (by rw [nRev_cons] at h3; simp at h3; omega)]
      omega

theorem count_kidsOf (f : Nat → PTrie) : ∀ (ks : List (Option (Option Bytes))) (q : Nat),
    Kids.count (kidsOf f ks q) = nPres ks
  | [], _ => by simp [kidsOf, Kids.count, nPres]
  | none :: r, q => by simp [kidsOf, Kids.count, nPres_cons, count_kidsOf f r]
  | some (some h) :: r, q => by simp [kidsOf, Kids.count, nPres_cons, count_kidsOf f r]; omega
  | some none :: r, q => by simp [kidsOf, Kids.count, nPres_cons, count_kidsOf f r]; omega

theorem rb_kidsOf (f : Nat → PTrie) : ∀ (ks : List (Option (Option Bytes))) (q : Nat),
    Kids.revealedBytes (kidsOf f ks q) = ssum (fun i => (f i).revealedBytes) q (nRev ks)
  | [], _ => by simp [kidsOf, Kids.revealedBytes, ssum]
  | none :: r, q => by simp [kidsOf, Kids.revealedBytes, nRev_cons, rb_kidsOf f r]
  | some (some h) :: r, q => by
    simp [kidsOf, Kids.revealedBytes, nRev_cons, rb_kidsOf f r, PTrie.revealedBytes]
  | some none :: r, q => by
    simp [kidsOf, Kids.revealedBytes, nRev_cons, rb_kidsOf f r, ssum]

/-- Own share of one node plus its children's trees. -/
theorem rb_node {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    (hv : hasVal e.nf = true → (vals j).length = vlenAt pb e) :
    (treeAt A K vals j).revealedBytes = entRev pb e +
      ssum (fun q => (treeAt A K vals (childIdx K e.kid (nKids e.nf) q)).revealedBytes) 0 (nKids e.nf) := by
  have hl : j < A.length := by
    rcases Nat.lt_or_ge j A.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  obtain ⟨e', he', hnf, hPF, hrp, hpe, ⟨z, zs, hz, hzs, hzs32, hpi⟩, -, -, -, -, hch, -⟩ := hw.nodes j hl
  rw [hj] at he'; cases he'
  have hlen : e.preLen = (preImg e.nf (vlenAt pb e) z zs).length := by
    rw [← hpi, pseg_length (by omega) (by omega)]
  unfold entRev
  rw [hlen]
  cases hn : e.nf with
  | leaf k ref mm =>
    rw [treeAt_leaf hj hn]
    rw [hn] at hnf hzs
    cases ref with
    | none =>
      simp [hn, hasVal] at hv
      simp only [PTrie.revealedBytes, preImg, slotOfRef, hasVal, nKids, ssum, List.length_append,
        List.length_cons, List.length_nil, u32_len, u64_len, hz, hv, ite_true]
      omega
    | some p =>
      obtain ⟨len, h⟩ := p
      have hh : h.length = 32 := hnf.2.2.2.2
      simp only [PTrie.revealedBytes, preImg, slotOfRef, hasVal, nKids, ssum, List.length_append,
        List.length_cons, List.length_nil, u32_len, u64_len, hh, Bool.false_eq_true, ite_false]
  | ext k h mm =>
    rw [hn] at hnf hzs
    cases h with
    | some hh =>
      have hh32 : hh.length = 32 := hnf.2.2.2
      rw [treeAt_exth hj hn]
      simp [PTrie.revealedBytes, preImg, hasVal, nKids, ssum, u32_len, u64_len, hh32]
      omega
    | none =>
      rw [treeAt_ext hj hn]
      have := hch 0 (by simp [hn, nKids])
      simp only [hn, nKids, childIdx] at this
      obtain ⟨ec, -, hlt, -⟩ := this
      simp at hlt
      simp only [nKids, Option.isNone_none, ite_true] at hzs
      obtain ⟨x, rfl⟩ : ∃ x, zs = [x] := by
        match zs, hzs with
        | [x], _ => exact ⟨x, rfl⟩
      have hx : x.length = 32 := hzs32 x (by simp)
      simp [PTrie.revealedBytes, preImg, hasVal, nKids, ssum, u32_len, u64_len, hx, childIdx, hlt]
      omega
  | branch v ks mm =>
    rw [hn] at hnf hzs
    rw [treeAt_branch hj hn]
    rw [kidsOf_congr _ (fun q => treeAt A K vals (childIdx K e.kid (nRev ks) q)) ks 0 (by
      intro p _ hp
      obtain ⟨ec, -, hlt, -⟩ := hch p (by simpa [hn, nKids] using hp)
      simp only [hn, nKids] at hlt
      simp [hlt])]
    have hsl := slotBytes_length ks zs hnf.2.2.2 hzs32 (by simpa [nKids] using hzs)
    have hv' := hv
    simp only [hn, hasVal] at hv'
    rcases v with _ | _ | ⟨len, h⟩
    · simp [PTrie.revealedBytes, preImg, hasVal, nKids, u16_len, u64_len, hsl, rb_kidsOf, count_kidsOf]
      omega
    · simp [PTrie.revealedBytes, preImg, hasVal, nKids, u16_len, u32_len, u64_len, hsl, rb_kidsOf,
        count_kidsOf, slotOfRef, hv', hz]
      omega
    · have hh : h.length = 32 := hnf.2.2.1.2
      simp [PTrie.revealedBytes, preImg, hasVal, nKids, u16_len, u32_len, u64_len, hsl, rb_kidsOf,
        count_kidsOf, slotOfRef, hh]
      omega

theorem rb_treeAt {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} (hV : ∀ j e, A[j]? = some e → hasVal e.nf = true → (vals j).length = vlenAt pb e) :
    ∀ j e, A[j]? = some e →
      (treeAt A K vals j).revealedBytes = ssum (fun i => entRev pb (A.getD i default)) e.lo (j + 1 - e.lo) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro e hj
  obtain ⟨hlo, hlo0, hch, -⟩ := nodeWF_of hw hj
  rw [rb_node hw hj (hV j e hj)]
  have hF : entRev pb e = (fun i => entRev pb (A.getD i default)) j := by simp [List.getD_eq_getElem?_getD, hj]
  -- children sums
  have key : ∀ m, m ≤ nKids e.nf →
      e.lo ≤ (if m = 0 then e.lo else childIdx K e.kid (nKids e.nf) (m - 1) + 1) ∧
      ssum (fun q => (treeAt A K vals (childIdx K e.kid (nKids e.nf) q)).revealedBytes) 0 m =
        ssum (fun i => entRev pb (A.getD i default)) e.lo
          ((if m = 0 then e.lo else childIdx K e.kid (nKids e.nf) (m - 1) + 1) - e.lo) := by
    intro m
    induction m with
    | zero => intro _; simp [ssum]
    | succ m ihm =>
      intro hm
      obtain ⟨h0, h1⟩ := ihm (by omega)
      obtain ⟨ec, hc, hlt, hclo, -⟩ := hch m (by omega)
      have hcl := (nodeWF_of hw hc).1
      have ihc := ih _ hlt ec hc
      generalize hE : (if m = 0 then e.lo else childIdx K e.kid (nKids e.nf) (m - 1) + 1) = E at h0 h1 hclo
      subst hclo
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      refine ⟨by omega, ?_⟩
      rw [ssum_succ_right, h1, Nat.zero_add, ihc,
        show childIdx K e.kid (nKids e.nf) m + 1 - e.lo = (ec.lo - e.lo) + (childIdx K e.kid (nKids e.nf) m + 1 - ec.lo) by omega,
        ssum_add, show e.lo + (ec.lo - e.lo) = ec.lo by omega]
  by_cases hn0 : nKids e.nf = 0
  · have := hlo0 hn0
    rw [hn0]; simp [ssum, this, hF]
  · obtain ⟨-, h2⟩ := key (nKids e.nf) (Nat.le_refl _)
    obtain ⟨_, -, -, -, hlast⟩ := hch (nKids e.nf - 1) (by omega)
    have hl := hlast (by omega)
    simp only [if_neg hn0, hl] at h2
    have h3 := ssum_succ_right (fun i => entRev pb (A.getD i default)) e.lo (j - e.lo)
    rw [show e.lo + (j - e.lo) = j by omega, show j - e.lo + 1 = j + 1 - e.lo by omega] at h3
    simp only at h3 hF
    omega

end ParseProof
end ReexecNpai
