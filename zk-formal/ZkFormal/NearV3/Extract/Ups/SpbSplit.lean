import ZkFormal.NearV3.Extract.Ups.UpsParts

/-!
# ZkFormal.NearV3.Extract.Ups.SpbSplit — the split branch is the spec's (M7e, step 2)

`qSPB ci src cx x si v` (`SpbSpec`) is the branch that `splitLeaf` / `splitExt` build before `wrapExt`, in each
of the seven split cases, when the walk stopped inside the terminal record after matching `I` nibbles:

* the record's key `k` and the remaining lookup key `key'` agree on `I` nibbles (`k.take I = key'.take I`),
  so `commonPrefix k key' = k.take I` (`commonPrefix_eq`) — the walk's mismatch, or an end of key, is at `I`;
* `key'.drop I = [0,15].drop si` (`y = yOf si`, `ys = ysOf si`: the new leaf `qNLF si v`);
* `x = k[I]` the record's nibble, `cx` the moved node (`qMVL k s I` / `qMVE k c m I`, part 0).

`split_LSa … split_ESn1`: `splitLeaf k s key' v` / `splitExt k c m key' v` `= wrapExt (k.take I) (qSPB …)`,
and `wexKey_eq`: `k.take I = wexKey si I` (the wrapping extension's key) when `key' = [0,15].drop (si − I)`.
-/

namespace ZkFormal.NearV3.UpsRows

open NearSpec UpsSpec

/-- The common prefix of two keys that agree on `I` nibbles and differ (or one ends) at `I`. -/
theorem commonPrefix_eq : ∀ (a b : List Nat) (I : Nat), a.take I = b.take I → I ≤ a.length → I ≤ b.length →
    (a.length = I ∨ b.length = I ∨ a[I]? ≠ b[I]?) → commonPrefix a b = a.take I
  | [], _, _, _, _, _, _ => by simp [commonPrefix]
  | _ :: _, [], _, _, _, h2, _ => by simp at h2; subst h2; simp [commonPrefix]
  | x :: as, y :: bs, 0, _, _, _, h => by
    simp only [List.take_zero]
    simp only [List.length_cons, List.getElem?_cons_zero, ne_eq, Option.some.injEq] at h
    rcases h with h | h | h
    · omega
    · omega
    · simp [commonPrefix, h]
  | x :: as, y :: bs, I + 1, ht, h1, h2, h => by
    simp only [List.take_succ_cons, List.cons.injEq] at ht
    obtain ⟨rfl, ht⟩ := ht
    simp only [List.length_cons, List.getElem?_cons_succ] at h1 h2 h
    have ih := commonPrefix_eq as bs I ht (by omega) (by omega) (by
      rcases h with h | h | h
      · left; omega
      · right; left; omega
      · right; right; exact h)
    simp [commonPrefix, ih]

theorem key_drop (si : Nat) (hsi : si < 2) : key.drop si = yOf si :: ysOf si := by
  rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> rfl

theorem key_drop2 : key.drop 2 = [] := rfl

theorem drop_cons_of {k : List Nat} {I : Nat} (h : I < k.length) : k.drop I = k[I] :: k.drop (I + 1) := by
  rw [List.drop_eq_getElem_cons h]

section
variable (k : List Nat) (key' : List Nat) (v : Bytes) (I si : Nat)
  (hpre : k.take I = key'.take I) (hkey : key'.drop I = key.drop si)

include hpre hkey

theorem key'_len (hsi : si < 2) : I < key'.length := by
  have := congrArg List.length hkey
  rw [List.length_drop, key_drop si hsi] at this
  simp at this; omega

theorem key'_end (hsi : si = 2) : key'.length ≤ I := by
  have := congrArg List.length hkey
  rw [List.length_drop, hsi, key_drop2] at this
  simp at this; omega

/-- `LSa`: the leaf's key is a proper prefix of the lookup key. -/
theorem split_LSa (s : Slot) (m : Nat) (cx : PTrie) (x : Nat) (hk : k.length = I) (hsi : si < 2) :
    splitLeaf k s key' v = wrapExt (k.take I) (qSPB 4 (.leaf k s m) cx x si v) := by
  have hl := key'_len k key' I si hpre hkey hsi
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by omega) (Or.inl hk)
  have hd : k.drop I = [] := by simp [hk]
  unfold splitLeaf
  simp only [hcp, List.length_take, show min I k.length = I by omega, hd, hkey, key_drop si hsi]
  rfl

/-- `LSb`: the lookup key ends inside the leaf's key. -/
theorem split_LSb (s : Slot) (m : Nat) (hk : I < k.length) (hsi : si = 2) :
    splitLeaf k s key' v = wrapExt (k.take I) (qSPB 5 (.leaf k s m) (qMVL k s I) k[I] si v) := by
  have hl := key'_end k key' I si hpre hkey hsi
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by
    have := congrArg List.length hpre; simp at this; omega) (Or.inr (Or.inl (by
      have := congrArg List.length hpre; simp at this; omega)))
  unfold splitLeaf
  simp only [hcp, List.length_take, show min I k.length = I by omega, drop_cons_of hk, hkey, hsi, key_drop2]
  rfl

/-- `LSc`: the keys differ at `I`. -/
theorem split_LSc (s : Slot) (m : Nat) (hk : I < k.length) (hsi : si < 2) (hxy : k[I] ≠ yOf si) :
    splitLeaf k s key' v = wrapExt (k.take I) (qSPB 6 (.leaf k s m) (qMVL k s I) k[I] si v) := by
  have hl := key'_len k key' I si hpre hkey hsi
  have hyI : key'[I]? = some (yOf si) := by
    have := congrArg List.head? hkey
    rw [key_drop si hsi, List.head?_drop] at this; simpa using this
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by omega)
    (Or.inr (Or.inr (by rw [hyI, List.getElem?_eq_getElem hk]; simpa using hxy)))
  unfold splitLeaf
  simp only [hcp, List.length_take, show min I k.length = I by omega, drop_cons_of hk, hkey, key_drop si hsi]
  rfl

/-- `ESl0`: the lookup key ends inside the extension's key, which keeps nibbles after `x`. -/
theorem split_ESl0 (c : PTrie) (m : Nat) (hk : I + 1 < k.length) (hsi : si = 2) :
    splitExt k c m key' v = wrapExt (k.take I) (qSPB 7 (.ext k c m) (qMVE k c m I) k[I] si v) := by
  have hl := key'_end k key' I si hpre hkey hsi
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by
    have := congrArg List.length hpre; simp at this; omega) (Or.inr (Or.inl (by
      have := congrArg List.length hpre; simp at this; omega)))
  have hxs : k.drop (I + 1) = k[I + 1] :: k.drop (I + 2) := drop_cons_of hk
  unfold splitExt
  simp only [hcp, List.length_take, show min I k.length = I by omega, drop_cons_of (show I < k.length by omega),
    hkey, hsi, key_drop2, hxs]
  simp only [qSPB, qMVE, PTrie.memD, PTrie.mem?, Option.getD_some, ← hxs]

/-- `ESl1`: the lookup key ends one nibble before the extension's key does. -/
theorem split_ESl1 (c : PTrie) (m : Nat) (cx : PTrie) (hk : I + 1 = k.length) (hsi : si = 2) :
    splitExt k c m key' v = wrapExt (k.take I) (qSPB 8 (.ext k c m) cx k[I] si v) := by
  have hl := key'_end k key' I si hpre hkey hsi
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by
    have := congrArg List.length hpre; simp at this; omega) (Or.inr (Or.inl (by
      have := congrArg List.length hpre; simp at this; omega)))
  have hxs : k.drop (I + 1) = [] := by simp; omega
  unfold splitExt
  simp only [hcp, List.length_take, show min I k.length = I by omega, drop_cons_of (show I < k.length by omega),
    hkey, hsi, key_drop2, hxs]
  rfl

/-- `ESn0`: the keys differ at `I`; the extension keeps nibbles after `x`. -/
theorem split_ESn0 (c : PTrie) (m : Nat) (hk : I + 1 < k.length) (hsi : si < 2)
    (hxy : k[I] ≠ yOf si) :
    splitExt k c m key' v = wrapExt (k.take I) (qSPB 9 (.ext k c m) (qMVE k c m I) k[I] si v) := by
  have hl := key'_len k key' I si hpre hkey hsi
  have hyI : key'[I]? = some (yOf si) := by
    have := congrArg List.head? hkey
    rw [key_drop si hsi, List.head?_drop] at this; simpa using this
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by omega)
    (Or.inr (Or.inr (by rw [hyI, List.getElem?_eq_getElem (show I < k.length by omega)]; simpa using hxy)))
  have hxs : k.drop (I + 1) = k[I + 1] :: k.drop (I + 2) := drop_cons_of hk
  unfold splitExt
  simp only [hcp, List.length_take, show min I k.length = I by omega, drop_cons_of (show I < k.length by omega),
    hkey, key_drop si hsi, hxs]
  simp only [qSPB, qMVE, qNLF, PTrie.memD, PTrie.mem?, Option.getD_some, ← hxs]

/-- `ESn1`: the keys differ at the extension's last nibble. -/
theorem split_ESn1 (c : PTrie) (m : Nat) (cx : PTrie) (hk : I + 1 = k.length) (hsi : si < 2)
    (hxy : k[I] ≠ yOf si) :
    splitExt k c m key' v = wrapExt (k.take I) (qSPB 10 (.ext k c m) cx k[I] si v) := by
  have hl := key'_len k key' I si hpre hkey hsi
  have hyI : key'[I]? = some (yOf si) := by
    have := congrArg List.head? hkey
    rw [key_drop si hsi, List.head?_drop] at this; simpa using this
  have hcp := commonPrefix_eq k key' I hpre (by omega) (by omega)
    (Or.inr (Or.inr (by rw [hyI, List.getElem?_eq_getElem (show I < k.length by omega)]; simpa using hxy)))
  have hxs : k.drop (I + 1) = [] := by simp; omega
  unfold splitExt
  simp only [hcp, List.length_take, show min I k.length = I by omega, drop_cons_of (show I < k.length by omega),
    hkey, key_drop si hsi, hxs]
  rfl

end

/-- The wrapping extension's key is the common prefix. -/
theorem wexKey_eq (k : List Nat) (I si : Nat) (hpre : k.take I = (key.drop (si - I)).take I) :
    k.take I = wexKey si I := hpre

theorem key'_drop (I si : Nat) (h : I ≤ si) : (key.drop (si - I)).drop I = key.drop si := by
  rw [List.drop_drop]; congr 1; omega

end ZkFormal.NearV3.UpsRows
