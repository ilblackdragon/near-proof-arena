import WasmBase.Main.SegMemMembS
import WasmBase.Main.SegMP
import WasmBase.Main.SegSoundMP
import WasmBase.Main.SegMemFrameMP

/-!
# WasmBase.Main.SegMemRootMP — the memory-root conjunct for the multiproof AIR (E2E M4c, MEM item 5)

`Main/SegMemRoot.lean`'s items 1, 3, 4 for `wasmBaseSegAirMP` (only table 20 differs), via `mp_tree`:

* `batch_update_pd`: lane B's `Merkle.batch_update_sound` with the hash injective only on 48-byte
  digests (`Sha384Coll` otherwise).
* `toUpd`: the multiproof's partial tree `PTree` as lane B's update description `Upd`, digests in bytes
  (`bytesOf_shaNode`: the chip's node on any limbs is `nodeH` of the bytes the limbs stand for, so no
  canonicity of stubs is needed); `toUpd_agrees`, `toUpd_apply`: the touched leaves' positions.
* `mpm_chipO`/`mpm_chipN`: every multiproof row's parent is `shaNode` of its children (chip contract,
  bus-103 receives of table 20), discharging `mp_tree`'s compression hypothesis.
* `mp_core`: the tree's leaves are exactly the touched blocks' `blk`, with MEMB's `hoI`/`hoO` as leaf
  digests; old leaves are the in-state's; `memOut` is the root of the in-state's leaves with the touched
  ones replaced.
* **`seg_membIn_mp`**, **`seg_memRootOut_mp`**, **`seg_mem_sound_mp`**: as in `SegMemRoot`; the MEMB
  side is shared through `HoldsXS` (`Main/SegMemMembS.lean`, `membIn_of_leaves`, `memLeaves_out_of`).

Extra named premise: `Dn pub ≤ 30` (public; the multiproof's positions are field naturals, `mp_tree`;
the verifier fixes `D = 16`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
open NearSpecV3.Wasm hiding P
open NearSpecV3.E2E.Bnd (Sha384Coll sha384 sha384_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace MemRoot

open StateM5a.Merkle

/-! ## 1. The batched update with a partially injective hash -/

section generic
variable {α : Type} (H : α → α → α) (Pd : α → Prop)

/-- Every digest of a description satisfies `Pd`. -/
def UPd : Upd α → Prop
  | .keep h => Pd h
  | .leaf o n => Pd o ∧ Pd n
  | .node l r => UPd l ∧ UPd r

theorem upd_old_pd (hH : ∀ a b, Pd (H a b)) : ∀ u : Upd α, UPd Pd u → Pd (u.old H)
  | .keep _, h => h
  | .leaf _ _, h => h.1
  | .node _ _, _ => hH _ _

theorem root_pd (hH : ∀ a b, Pd (H a b)) : ∀ (D : Nat) (l : List α) (x : α), (∀ y ∈ l, Pd y) →
    root H D l = some x → Pd x
  | 0, l, x, hl, h => by
    match l, h with
    | [y], h => simp only [root, Option.some.injEq] at h; subst h; exact hl _ (by simp)
  | D + 1, l, x, _, h => root_pd hH D (up H l) x (up_pd H Pd hH l) h

/-- **`Merkle.batch_update_sound` for a hash injective on `Pd`-digests.** -/
theorem batch_update_pd (hH : ∀ a b, Pd (H a b))
    (hinj : ∀ a b c d, Pd a → Pd b → Pd c → Pd d → H a b = H c d → a = c ∧ b = d) :
    ∀ (D : Nat) (u : Upd α) (l : List α), u.Fits D → UPd Pd u → (∀ y ∈ l, Pd y) → l.length = 2 ^ D →
      root H D l = some (u.old H) → u.Agrees D l ∧ root H D (u.apply D l) = some (u.new H)
  | D, .keep h, l, _, _, _, _, hr => by
    refine ⟨by cases D <;> simp [Upd.Agrees], ?_⟩
    cases D <;> simpa [Upd.apply, Upd.old, Upd.new] using hr
  | 0, .leaf o n, l, _, _, _, hl, hr => by
    match l, hl with
    | [x], _ =>
      simp only [root, Upd.old, Option.some.injEq] at hr
      subst hr
      exact ⟨rfl, rfl⟩
  | D + 1, .node a b, l, hf, hu, hlP, hl, hr => by
    simp only [Upd.Fits] at hf
    obtain ⟨hua, hub⟩ := hu
    have e : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
    have h1 : (l.take (2 ^ D)).length = 2 ^ D := by simp [hl, e]
    have h2 : (l.drop (2 ^ D)).length = 2 ^ D := by simp [hl, e]
    have p1 : ∀ y ∈ l.take (2 ^ D), Pd y := fun y hy => hlP y (List.mem_of_mem_take hy)
    have p2 : ∀ y ∈ l.drop (2 ^ D), Pd y := fun y hy => hlP y (List.mem_of_mem_drop hy)
    rw [root_succ_split H D l hl] at hr
    cases hx : root H D (l.take (2 ^ D)) with
    | none => simp [hx] at hr
    | some x =>
      cases hy : root H D (l.drop (2 ^ D)) with
      | none => simp [hx, hy] at hr
      | some y =>
        simp only [hx, hy, Option.bind_some, Option.map_some, Option.some.injEq, Upd.old] at hr
        obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ (root_pd H Pd hH D _ x p1 hx) (root_pd H Pd hH D _ y p2 hy)
          (upd_old_pd H Pd hH a hua) (upd_old_pd H Pd hH b hub) hr
        obtain ⟨ha1, ha2⟩ := batch_update_pd hH hinj D a _ hf.1 hua p1 h1 hx
        obtain ⟨hb1, hb2⟩ := batch_update_pd hH hinj D b _ hf.2 hub p2 h2 hy
        refine ⟨⟨ha1, hb1⟩, ?_⟩
        have la := Upd.apply_length D a _ hf.1 h1
        have lb := Upd.apply_length D b _ hf.2 h2
        have hlen : (Upd.apply D a (l.take (2 ^ D)) ++ Upd.apply D b (l.drop (2 ^ D))).length =
            2 ^ (D + 1) := by simp [la, lb, e]
        simp only [Upd.apply]
        rw [root_succ_split H D _ hlen, List.take_left' la, List.drop_left' la, ha2, hb2]
        rfl
  | D + 1, .leaf _ _, _, hf, _, _, _, _ => by simp [Upd.Fits] at hf
  | 0, .node _ _, _, hf, _, _, _, _ => by simp [Upd.Fits] at hf

end generic

/-! ## 2. The multiproof's partial tree in bytes -/

theorem bytesOf_length (x : List F) : (bytesOf x).length = 48 := by
  simp [bytesOf, SegSha.wbytes_length, SegSha.decF]

theorem decF_length (x : List F) : (SegSha.decF x).length = 6 := by simp [SegSha.decF]

/-- **`shaNode` in bytes is lane B's `nodeH`**, on any limbs (the chip hashes the words' bytes). -/
theorem bytesOf_shaNode (a b : List F) :
    bytesOf (SegSha.shaNode a b) = StateM5a.StateView.nodeH (bytesOf a) (bytesOf b) := by
  have hco := SegSha.compressW_ok NearSpecV3.E2E.Bnd.IV384 (SegSha.decF a ++ SegSha.decF b ++ padW)
  have hl : ((SegSha.compressW NearSpecV3.E2E.Bnd.IV384 (SegSha.decF a ++ SegSha.decF b ++ padW)).take 6).length = 6 := by
    rw [List.length_take, hco.1]; rfl
  have hw : W64 ((SegSha.compressW NearSpecV3.E2E.Bnd.IV384 (SegSha.decF a ++ SegSha.decF b ++ padW)).take 6) :=
    fun w hw' => hco.2 w (List.mem_of_mem_take hw')
  rw [SegSha.shaNode, bytesOf, SegSha.decF_limbsF hl hw, ← SegSha.sha384_node _ _ (decF_length a) (decF_length b),
    SegSha.wbytes_append]
  rfl

/-- `shaNode` outputs are canonical. -/
theorem shaNode_canon (a b : List F) : Canon (SegSha.shaNode a b) (bytesOf (SegSha.shaNode a b)) := by
  have hco := SegSha.compressW_ok NearSpecV3.E2E.Bnd.IV384 (SegSha.decF a ++ SegSha.decF b ++ padW)
  exact canon_of (by rw [List.length_take, hco.1]; rfl) (fun w hw' => hco.2 w (List.mem_of_mem_take hw')) rfl

/-- A partial tree as lane B's update description, digests in bytes. -/
def toUpd (lo ln : Nat → List F) : PTree → Upd ArenaCore.Bytes
  | .leaf i => .leaf (bytesOf (lo i)) (bytesOf (ln i))
  | .stub d => .keep (bytesOf d)
  | .node l r => .node (toUpd lo ln l) (toUpd lo ln r)

theorem toUpd_old (lo ln : Nat → List F) : ∀ T : PTree,
    bytesOf (T.eval SegSha.shaNode lo) = (toUpd lo ln T).old StateM5a.StateView.nodeH
  | .leaf _ => rfl
  | .stub _ => rfl
  | .node l r => by
    simp only [PTree.eval, toUpd, Upd.old, bytesOf_shaNode, toUpd_old lo ln l, toUpd_old lo ln r]

theorem toUpd_new (lo ln : Nat → List F) : ∀ T : PTree,
    bytesOf (T.eval SegSha.shaNode ln) = (toUpd lo ln T).new StateM5a.StateView.nodeH
  | .leaf _ => rfl
  | .stub _ => rfl
  | .node l r => by
    simp only [PTree.eval, toUpd, Upd.new, bytesOf_shaNode, toUpd_new lo ln l, toUpd_new lo ln r]

theorem toUpd_pd (lo ln : Nat → List F) : ∀ T : PTree, UPd D48 (toUpd lo ln T)
  | .leaf _ => ⟨bytesOf_length _, bytesOf_length _⟩
  | .stub _ => bytesOf_length _
  | .node l r => ⟨toUpd_pd lo ln l, toUpd_pd lo ln r⟩

theorem toUpd_fits (lo ln : Nat → List F) : ∀ (k n : Nat) (T : PTree), T.At k n → (toUpd lo ln T).Fits k
  | _, _, .stub _, _ => by simp [toUpd, Upd.Fits]
  | 0, _, .leaf _, _ => by simp [toUpd, Upd.Fits]
  | k + 1, n, .node l r, h => ⟨toUpd_fits lo ln k (2 * n) l h.1, toUpd_fits lo ln k (2 * n + 1) r h.2⟩
  | 0, _, .node _ _, h => by simp [PTree.At] at h
  | _ + 1, _, .leaf _, h => by simp [PTree.At] at h

/-- The touched leaves' old digests are the list's entries at their positions. -/
theorem toUpd_agrees (lo ln : Nat → List F) : ∀ (k n : Nat) (T : PTree) (l : List ArenaCore.Bytes), T.At k n →
    (toUpd lo ln T).Agrees k l → ∀ i ∈ T.leaves, l[i - n * 2 ^ k]? = some (bytesOf (lo i))
  | _, _, .stub _, _, _, _, i, hi => by simp [PTree.leaves] at hi
  | 0, n, .leaf j, l, hA, hag, i, hi => by
    simp only [PTree.At] at hA
    simp only [PTree.leaves, List.mem_singleton] at hi
    subst hi; subst hA
    simp only [toUpd, Upd.Agrees] at hag
    subst hag; simp
  | k + 1, n, .node a b, l, hA, hag, i, hi => by
    obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨g1, g2⟩ := hag
    have e1 : n * 2 ^ (k + 1) = 2 * n * 2 ^ k := by rw [Nat.pow_succ]; grind
    rcases List.mem_append.mp hi with hi | hi
    · have hb := PTree.At_leaves k (2 * n) a hA1 i hi
      have := toUpd_agrees lo ln k (2 * n) a _ hA1 g1 i hi
      rw [List.getElem?_take, if_pos (by grind)] at this
      rw [e1]; exact this
    · have hb := PTree.At_leaves k (2 * n + 1) b hA2 i hi
      have := toUpd_agrees lo ln k (2 * n + 1) b _ hA2 g2 i hi
      rw [List.getElem?_drop] at this
      have e3 : 2 ^ k + (i - (2 * n + 1) * 2 ^ k) = i - 2 * n * 2 ^ k := by
        have q1 : (2 * n + 1) * 2 ^ k = 2 * (n * 2 ^ k) + 2 ^ k := by grind
        have q2 : 2 * n * 2 ^ k = 2 * (n * 2 ^ k) := by grind
        have hb1 := hb.1
        rw [q1] at hb1 ⊢; rw [q2]
        generalize n * 2 ^ k = c at hb1 ⊢
        generalize 2 ^ k = e at hb1 ⊢
        omega
      rw [e3] at this; rw [e1]; exact this
  | 0, _, .node _ _, _, h, _, _, _ => by simp [PTree.At] at h
  | _ + 1, _, .leaf _, _, h, _, _, _ => by simp [PTree.At] at h

/-- The list with the touched leaves replaced by their new digests. -/
theorem toUpd_apply (lo ln : Nat → List F) : ∀ (k n : Nat) (T : PTree) (l : List ArenaCore.Bytes), T.At k n →
    l.length = 2 ^ k → ∀ j, j < 2 ^ k →
      ((toUpd lo ln T).apply k l)[j]? =
        if n * 2 ^ k + j ∈ T.leaves then some (bytesOf (ln (n * 2 ^ k + j))) else l[j]?
  | k, n, .stub d, l, _, _, j, _ => by
    cases k <;> simp [toUpd, Upd.apply, PTree.leaves]
  | 0, n, .leaf i, l, hA, hl, j, hj => by
    simp only [PTree.At] at hA
    subst hA
    have : j = 0 := by simp at hj; omega
    subst this
    simp [toUpd, Upd.apply, PTree.leaves]
  | k + 1, n, .node a b, l, hA, hl, j, hj => by
    obtain ⟨hA1, hA2⟩ := hA
    have e : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have h1 : (l.take (2 ^ k)).length = 2 ^ k := by simp [hl, e]
    have h2 : (l.drop (2 ^ k)).length = 2 ^ k := by simp [hl, e]
    have la := Upd.apply_length k (toUpd lo ln a) _ (toUpd_fits lo ln k _ a hA1) h1
    have e1 : n * 2 ^ (k + 1) = 2 * n * 2 ^ k := by rw [Nat.pow_succ]; grind
    have e2 : (2 * n + 1) * 2 ^ k = 2 * n * 2 ^ k + 2 ^ k := by grind
    simp only [toUpd, Upd.apply, PTree.leaves, List.mem_append]
    by_cases hjk : j < 2 ^ k
    · rw [List.getElem?_append_left (by rw [la]; exact hjk), toUpd_apply lo ln k (2 * n) a _ hA1 h1 j hjk,
        List.getElem?_take, if_pos hjk, e1]
      have hnb : 2 * n * 2 ^ k + j ∉ b.leaves := fun hm => by
        have := PTree.At_leaves k (2 * n + 1) b hA2 _ hm; omega
      by_cases hm : 2 * n * 2 ^ k + j ∈ a.leaves
      · rw [if_pos hm, if_pos (Or.inl hm)]
      · rw [if_neg hm, if_neg (fun h => h.elim hm hnb)]
    · rw [List.getElem?_append_right (by rw [la]; omega), la,
        toUpd_apply lo ln k (2 * n + 1) b _ hA2 h2 (j - 2 ^ k) (by omega), List.getElem?_drop,
        show 2 ^ k + (j - 2 ^ k) = j by omega, e1, e2, show 2 * n * 2 ^ k + 2 ^ k + (j - 2 ^ k) = 2 * n * 2 ^ k + j by omega]
      have hna : 2 * n * 2 ^ k + j ∉ a.leaves := fun hm => by
        have := PTree.At_leaves k (2 * n) a hA1 _ hm; omega
      by_cases hm : 2 * n * 2 ^ k + j ∈ b.leaves
      · rw [if_pos hm, if_pos (Or.inr hm)]
      · rw [if_neg hm, if_neg (fun h => h.elim hna hm)]
  | 0, _, .node _ _, _, h, _, _, _ => by simp [PTree.At] at h
  | _ + 1, _, .leaf _, _, h, _, _, _ => by simp [PTree.At] at h

/-! ## 3. The multiproof's node compression is `shaNode` -/

/-- The 32 words of a multiproof MPATH compression: children at columns `l`, `rr`, parent `po`,
extra `xo`. -/
def mpmW (tr : Trace) (r l rr po xo k : Nat) : List F :=
  if k < 8 then SegSha.wF (Seg.IV384.getD k 0)
  else if k < 14 then (List.range 3).map fun j => mc tr r (l + 3 * (k - 8) + j)
  else if k < 20 then (List.range 3).map fun j => mc tr r (rr + 3 * (k - 14) + j)
  else if k < 24 then SegSha.wF (padW.getD (k - 20) 0)
  else if k < 30 then (List.range 3).map fun j => mc tr r (po + 3 * (k - 24) + j)
  else (List.range 3).map fun j => mc tr r (xo + 3 * (k - 30) + j)

theorem mpm_wsO_eval (tr : Trace) (pub : List F) (r : Nat) :
    ∀ k, k < 32 → ((MpathMP.ivW ++ MpathMP.nodeBlock "oL" "oR" ++ wordsAt MpathMP.c "po" 6 ++
      wordsAt MpathMP.c "xo" 2).getD k zeroW).map (·.eval (tr.row pub 20 r)) = mpmW tr r 13 49 85 121 k
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl | 15, _ => rfl | 16, _ => rfl | 17, _ => rfl | 18, _ => rfl | 19, _ => rfl | 20, _ => rfl
  | 21, _ => rfl | 22, _ => rfl | 23, _ => rfl | 24, _ => rfl | 25, _ => rfl | 26, _ => rfl | 27, _ => rfl
  | 28, _ => rfl | 29, _ => rfl | 30, _ => rfl | 31, _ => rfl
  | _ + 32, h => absurd h (by omega)

theorem mpm_wsN_eval (tr : Trace) (pub : List F) (r : Nat) :
    ∀ k, k < 32 → ((MpathMP.ivW ++ MpathMP.nodeBlock "nL" "nR" ++ wordsAt MpathMP.c "pn" 6 ++
      wordsAt MpathMP.c "xn" 2).getD k zeroW).map (·.eval (tr.row pub 20 r)) = mpmW tr r 31 67 103 127 k
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl | 15, _ => rfl | 16, _ => rfl | 17, _ => rfl | 18, _ => rfl | 19, _ => rfl | 20, _ => rfl
  | 21, _ => rfl | 22, _ => rfl | 23, _ => rfl | 24, _ => rfl | 25, _ => rfl | 26, _ => rfl | 27, _ => rfl
  | 28, _ => rfl | 29, _ => rfl | 30, _ => rfl | 31, _ => rfl
  | _ + 32, h => absurd h (by omega)

/-- One compression of a multiproof row, from its chip messages: the parent is `shaNode` of the
children. -/
theorem mpm_path_sha {tr : Trace} {chip : List IfMsg} (hcon : Sha512IfContract SegSha.compressW chip)
    (hlt : ∀ x ∈ chip, x.cid < P) {r l rr po xo : Nat} {cid : F}
    (hrecv : ∀ m, m < 16 → cid :: ((m : Nat) : F) :: (mpmW tr r l rr po xo (2 * m) ++ mpmW tr r l rr po xo (2 * m + 1))
      ∈ chip.map SegSha.ifF) :
    mdig tr r po = SegSha.shaNode (mdig tr r l) (mdig tr r rr) := by
  have hW3 : ∀ k, k < 32 → (mpmW tr r l rr po xo k).length = 3 := by
    intro k _; unfold mpmW
    by_cases h1 : k < 8 <;> by_cases h2 : k < 14 <;> by_cases h3 : k < 20 <;> by_cases h4 : k < 24 <;>
      by_cases h5 : k < 30 <;> simp [h1, h2, h3, h4, h5, SegSha.wF_length]
  obtain ⟨dl, dr, dout, l1, l2, l3, w1, w2, w3, e1, e2, e3, e4, -⟩ :=
    SegSha.consumer_node_sha384 hcon hlt hW3
      (fun k hk => by simp [mpmW, hk]; rfl)
      (fun k hk => by simp [mpmW, show ¬ 20 + k < 8 by omega, show ¬ 20 + k < 14 by omega,
        show ¬ 20 + k < 20 by omega, show 20 + k < 24 by omega])
      hrecv
  have fl : ∀ (base off : Nat) (d : List Nat), d.length = 6 →
      (∀ k, k < 6 → mpmW tr r l rr po xo (off + k) = (List.range 3).map (fun j => mc tr r (base + 3 * k + j))) →
      (∀ k, k < 6 → mpmW tr r l rr po xo (off + k) = SegSha.wF (d.getD k 0)) → mdig tr r base = SegSha.limbsF d := by
    intro base off d hd hform he
    have hf := SegSha.flat_triples d (fun i => mc tr r (base + i)) (fun k hk => by
      rw [hd] at hk
      rw [← he k hk, hform k hk]
      apply List.map_congr_left; intro j _; simp only [Nat.add_assoc])
    rw [hd] at hf; exact hf
  have eL := fl l 8 dl l1 (fun k hk => by
    simp only [mpmW, show ¬ 8 + k < 8 by omega, show 8 + k < 14 by omega, ite_false, ite_true,
      show 8 + k - 8 = k by omega]) e1
  have eR := fl rr 14 dr l2 (fun k hk => by
    simp only [mpmW, show ¬ 14 + k < 8 by omega, show ¬ 14 + k < 14 by omega, show 14 + k < 20 by omega,
      ite_false, ite_true, show 14 + k - 14 = k by omega]) e2
  have eP := fl po 24 dout l3 (fun k hk => by
    simp only [mpmW, show ¬ 24 + k < 8 by omega, show ¬ 24 + k < 14 by omega, show ¬ 24 + k < 20 by omega,
      show ¬ 24 + k < 24 by omega, show 24 + k < 30 by omega, ite_false, ite_true, show 24 + k - 24 = k by omega]) e3
  rw [eL, eR, eP, SegSha.shaNode_limbs l1 l2 w1 w2, e4]

section mpchip
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

/-- A bus-103 receive with count 1 of the multiproof MPATH is a chip message. -/
theorem mpm_recv_chip {compress : List Nat → List Nat → List Nat} {chip : List IfMsg}
    (hC : SegSha.ChipIf compress (wasmBaseSegAirMP nloc ngl) pub tr chip)
    {r : Nat} (hr : r < tr.height 20) {i : Inter} (hi : i ∈ MpathMP.table.inters) (hb : i.bus = extBus)
    (hc : (i.count.eval (tr.row pub 20 r)).toNat = 1) : i.msg.map (·.eval (tr.row pub 20 r)) ∈ chip.map SegSha.ifF := by
  have ht' : 20 < (wasmBaseSegAirMP nloc ngl).tables.length := segMP_lt nloc ngl 20 (by decide)
  have hi' : i ∈ ((wasmBaseSegAirMP nloc ngl).tables[20]'ht').inters := by rw [segMP_t20']; exact hi
  have ho := occ_of_inter ht' hr hi' hc
  have hbits := SegSha.segMP_if_bits H
  have hs : i.send = false := (hbits _ ho hb).1
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltX H extBus false (i.msg.map (·.eval (tr.row pub 20 r)))
    (fun o ho hb _ => (hbits o ho hb).2)
  have hbal := hC.balance (i.msg.map (·.eval (tr.row pub 20 r)))
  rw [SegSha.segMP_if_send_zero H, Nat.add_zero, Nat.mod_eq_of_lt hlt] at hbal
  refine List.count_pos_iff.mp ?_
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, Nat.zero_mod] at hbal
  simp only at hge
  omega

theorem mpm_comp_chip {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip)
    {r : Nat} (hr : r < tr.height 20) {cidE cnt : Expr} {ws : List W3}
    (hsub : ∀ i ∈ comp cidE ws cnt, i ∈ MpathMP.table.inters) (hcnt : (cnt.eval (tr.row pub 20 r)).toNat = 1) :
    ∀ m, m < 16 → (cidE.eval (tr.row pub 20 r) :: ((m : Nat) : F) ::
      ((ws.getD (2 * m) zeroW).map (·.eval (tr.row pub 20 r)) ++ (ws.getD (2 * m + 1) zeroW).map (·.eval (tr.row pub 20 r))))
        ∈ chip.map SegSha.ifF := by
  intro m hm
  have hi := hsub _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)
  have := mpm_recv_chip H hC hr hi rfl hcnt
  simpa [comp, List.map_append] using this

/-- **The multiproof's old parent is `shaNode` of its old children** (active row). -/
theorem mpm_chipO {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip)
    {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) :
    mdig tr r 85 = SegSha.shaNode (mdig tr r 13) (mdig tr r 49) := by
  have hin := mpm_comp_chip H hC hr (cidE := MpathMP.c "cidO")
    (ws := MpathMP.ivW ++ MpathMP.nodeBlock "oL" "oR" ++ wordsAt MpathMP.c "po" 6 ++ wordsAt MpathMP.c "xo" 2)
    (cnt := MpathMP.c "act")
    (fun i hi => by simp only [MpathMP.table, MpathMP.inters, List.mem_append]; left; right; exact hi)
    (by show (mc tr r 0).toNat = 1; rw [ha]; rfl)
  refine mpm_path_sha hC.contract hC.cidLt (xo := 121) (cid := (MpathMP.c "cidO").eval (tr.row pub 20 r)) (fun m hm => ?_)
  have := hin m hm
  rwa [mpm_wsO_eval tr pub r (2 * m) (by omega), mpm_wsO_eval tr pub r (2 * m + 1) (by omega)] at this

/-- **The multiproof's new parent is `shaNode` of its new children** (active, writable row). -/
theorem mpm_chipN {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip)
    {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) (hro : mc tr r 2 = 0) :
    mdig tr r 103 = SegSha.shaNode (mdig tr r 31) (mdig tr r 67) := by
  have hin := mpm_comp_chip H hC hr (cidE := MpathMP.c "cidN")
    (ws := MpathMP.ivW ++ MpathMP.nodeBlock "nL" "nR" ++ wordsAt MpathMP.c "pn" 6 ++ wordsAt MpathMP.c "xn" 2)
    (cnt := MpathMP.c "act" * (1 - MpathMP.c "ro"))
    (fun i hi => by simp only [MpathMP.table, MpathMP.inters, List.mem_append]; right; exact hi)
    (by show (mc tr r 0 * (1 - mc tr r 2)).toNat = 1; rw [ha, hro]; rfl)
  refine mpm_path_sha hC.contract hC.cidLt (xo := 127) (cid := (MpathMP.c "cidN").eval (tr.row pub 20 r)) (fun m hm => ?_)
  have := hin m hm
  rwa [mpm_wsN_eval tr pub r (2 * m) (by omega), mpm_wsN_eval tr pub r (2 * m + 1) (by omega)] at this

end mpchip

/-! ## 4. The MEMB side, from `HoldsXS` (both AIRs) -/

section tails
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

theorem memb_ro_bitS {r : Nat} (hr : r < tr.height 19) : mbN tr r 11 = 0 ∨ mbN tr r 11 = 1 := by
  have h := memb_CS H hr (Chips.bool (Memb.c "ro")) (by simp [Memb.constraints])
  rw [Chips.bool, Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.2.2, Expr.eval_ofNat'] at h
  exact bool_nat (rowNat_lt tr 19 r 11) h

/-- **In-side tail**: if every touched block's in-leaf `hoI` is the in-state's leaf at its `blk`,
MEMB's productions are the in-state's bytes. -/
theorem membIn_of_leaves {chip : List IfMsg} (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip)
    {s0 : St} (hG : MemGeom pub s0) (hn : ¬ Sha384Coll)
    (hleaf : ∀ b, 9 * b + 8 < tr.height 19 → mbN tr (9 * b + 8) 0 = 1 →
      (WasmView.memLeaves s0)[mbN tr (9 * b + 8) 10]? = some (bytesOf (bdig tr (9 * b + 8) 486))) :
    MembIn tr pub s0 := by
  intro x hx
  obtain ⟨b, k, i, hk, hi, hr8, ha8, rfl⟩ := memb_prod_formS H hx
  have hlt := (memb_blk_ltS H hr8 ha8).2.1
  rw [hG.2] at hlt
  have A := hleaf b hr8 ha8
  rw [memLeaves_get, if_pos hlt, leaf_in_bytesS H hC hr8 ha8] at A
  have hEq := sha384_inj hn (Option.some.inj A)
  have hj : 128 * k + i < 1024 := by omega
  have B := congrArg (·[128 * k + i]?) hEq
  rw [blkBytes_get _ _ hj, membBytes_get _ _ _ hj, show (128 * k + i) / 128 = k by omega,
    show (128 * k + i) % 128 = i by omega, mb_ix_bi i hi] at B
  have hrk : 9 * b + k < tr.height 19 := by omega
  have hak : mbN tr (9 * b + k) 0 = 1 := (memb_posS H _ hr8 ha8).1 _ (by omega)
  have hbi := memb_bi_lt'S H hrk hak (by omega) hi
  have hrd : (readByte s0 (1024 * mbN tr (9 * b + 8) 10 + (128 * k + i))).toNat = mbN tr (9 * b + k) (14 + i) := by
    rw [Option.some.inj B]; exact uint8_toNat_ofNat hbi
  rw [← Nat.add_assoc] at hrd
  refine ⟨?_, ?_⟩
  · show 1024 * mbN tr (9 * b + 8) 10 + 128 * k + i < memBytes s0
    simp only [memBytes, pageSize, WasmView.nblkOf] at hlt ⊢
    omega
  · simp only [encB, hrd]

/-- **Out-side tail**: a leaf list carrying every touched block's out-leaf `hoO` at its `blk` and the
in-state's leaf elsewhere is the out-state's leaf list (frame `hpg`/`hfr`, out-boundary `hout`). -/
theorem memLeaves_out_of {chip : List IfMsg} (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip)
    {s0 sN : St} (hG : MemGeom pub s0) (hpg : sN.pages.size = s0.pages.size)
    (hfr : ∀ a, (∀ x ∈ (part Memb.table tr pub 19 busStk true).map decMsg, x.slot ≠ a) →
      readByte sN a = readByte s0 a)
    (hout : ∀ a v tp, (⟨3, a, 0, v, 0, 0, 0, tp⟩ : Msg) ∈ (part Memb.table tr pub 19 busStk false).map decMsg →
      (readByte sN a).toNat = v)
    {Lf : List ArenaCore.Bytes} (hlen : Lf.length = 2 ^ WasmView.memDepth s0)
    (ht : ∀ b, 9 * b + 8 < tr.height 19 → mbN tr (9 * b + 8) 0 = 1 →
      Lf[mbN tr (9 * b + 8) 10]? = some (bytesOf (bdig tr (9 * b + 8) 534)))
    (hu : ∀ i, (∀ b, 9 * b + 8 < tr.height 19 → mbN tr (9 * b + 8) 0 = 1 → mbN tr (9 * b + 8) 10 ≠ i) →
      Lf[i]? = (WasmView.memLeaves s0)[i]?) :
    Lf = WasmView.memLeaves sN := by
  obtain ⟨hnb, hdp⟩ := nblk_depth_eq hpg
  have cc : ∀ r i, bc tr r i = ((mbN tr r i : Nat) : F) := fun r i => cell_cast tr 19 r i
  apply List.ext_getElem?; intro i
  rw [memLeaves_get sN i, hnb, hdp]
  by_cases hex : ∃ b, 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 ∧ mbN tr (9 * b + 8) 10 = i
  · obtain ⟨b, hr8, ha8, rfl⟩ := hex
    have hlt := (memb_blk_ltS H hr8 ha8).2.1
    rw [hG.2] at hlt
    rw [ht b hr8 ha8, if_pos hlt]
    have hbo : ∀ q, q < 8 → ∀ i', i' < 128 →
        mbN tr (9 * b + q) (142 + i') = (readByte sN (1024 * mbN tr (9 * b + 8) 10 + 128 * q + i')).toNat := by
      intro q hq i' hi'
      obtain ⟨tp, hm⟩ := memb_cons_memS H hr8 ha8 hq hi'
      exact (hout _ _ _ hm).symm
    have hbytes : SegSha.membBytes tr b "bo" = WasmView.blkBytes sN (mbN tr (9 * b + 8) 10) := by
      apply List.ext_getElem?; intro j
      by_cases hj : j < 1024
      · rw [membBytes_get _ _ _ hj, blkBytes_get _ _ hj, SegSha.mb_ix_bo _ (Nat.mod_lt _ (by decide)),
          hbo (j / 128) (by omega) (j % 128) (Nat.mod_lt _ (by decide)), UInt8.ofNat_toNat]
        congr 2; omega
      · rw [List.getElem?_eq_none (by rw [membBytes_length]; omega),
          List.getElem?_eq_none (by rw [blkBytes_length]; omega)]
    congr 1
    rw [← hbytes]
    rcases memb_ro_bitS H hr8 with hro | hro
    · obtain ⟨d, hl, hw, e, eb⟩ := SegSha.memb_leaf_outS H hC hr8 ha8 hro (fun q hq i' hi' => by
        rw [hbo q hq i' hi']; exact UInt8.toNat_lt _)
      exact (show Canon (bdig tr (9 * b + 8) 534) _ from ⟨d, hl, hw, e, eb⟩).bytes
    · rw [memb_ro_leafS H hr8 ha8 (by rw [cc, hro]; rfl), leaf_in_bytesS H hC hr8 ha8, memb_ro_bytesS H hr8 ha8 hro]
  · rw [hu i (fun b hr8 ha8 he => hex ⟨b, hr8, ha8, he⟩), memLeaves_get s0 i]
    by_cases hlt : i < WasmView.nblkOf s0
    · rw [if_pos hlt, if_pos hlt]
      congr 2
      apply List.ext_getElem?; intro j
      by_cases hj : j < 1024
      · rw [blkBytes_get _ _ hj, blkBytes_get _ _ hj]
        congr 1
        refine (hfr _ fun x hx he => ?_).symm
        obtain ⟨b, k, i', hk, hi', hr8, ha8, rfl⟩ := memb_prod_formS H hx
        simp only at he
        exact hex ⟨b, hr8, ha8, by omega⟩
      · rw [List.getElem?_eq_none (by rw [blkBytes_length]; omega),
          List.getElem?_eq_none (by rw [blkBytes_length]; omega)]
    · rw [if_neg hlt, if_neg hlt]

end tails

/-! ## 5. The multiproof tree against the spec memory tree -/

theorem leafOld_len (tr : Trace) (pub : List F) (i : Nat) :
    (leafOld tr pub i).length = 18 ∨ (leafOld tr pub i).length = 0 := by
  unfold leafOld; split
  · split <;> simp [mdig_len]
  · simp

theorem leafNew_len (tr : Trace) (pub : List F) (i : Nat) :
    (leafNew tr pub i).length = 18 ∨ (leafNew tr pub i).length = 0 := by
  unfold leafNew; split
  · split <;> simp [mdig_len]
  · simp

section mpcore
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

/-- Every bus-15 send of the multiproof AIR is a MEMB padding row's leaf message. -/
theorem mp_leaf_send_form {o : Occ} (ho : o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub) (hb : o.1 = 15)
    (hs : o.2.1 = true) :
    ∃ r, r < tr.height 19 ∧
      o = (15, true, [bc tr r 10, bc tr r 11] ++ bdig tr r 486 ++ bdig tr r 534, (bc tr r 9).toNat) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  by_cases h20 : t = 20
  · subst h20
    rw [segMP_t20'] at hi
    have hm : i ∈ MpathMP.table.inters.filter (fun i => i.bus = 15) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [mpm_f15] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl <;> simp at hs
  by_cases h19 : t = 19
  · subst h19
    rw [segMP_t19'] at hi
    have hm : i ∈ Memb.table.inters.filter (fun i => i.bus = 15) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [memb_leaf] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    subst hm
    refine ⟨r, hr, ?_⟩
    obtain ⟨-, ib, iro⟩ := mb_ix
    simp only [List.map_append, List.map_cons, List.map_nil, Memb.c, Memb.p, ib, iro, mb_ix_p 8 (by decide)]
    rw [bdig_eval tr pub r 486 "hoI" (fun l hl => (mb_ix_ho l hl).1),
      bdig_eval tr pub r 534 "hoO" (fun l hl => (mb_ix_ho l hl).2)]
    rfl
  by_cases h0 : t = 0
  · subst h0
    rw [segMP_t0'] at hi
    have := List.all_eq_true.mp segb_bus i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact absurd hb this.1
  · exact absurd hb (segMP_bus_other nloc ngl t ht h0 h19 h20 i hi).1

/-- A leaf message `[i, ρ] ++ old ++ new` that is MEMB's padding row `9b + 8`'s. -/
theorem leaf_of_memb {i r : Nat} {ρ : F} (hi : i < 2 ^ 30) (hr : r < tr.height 19)
    (hm : [((i : Nat) : F), ρ] ++ leafOld tr pub i ++ leafNew tr pub i =
      [bc tr r 10, bc tr r 11] ++ bdig tr r 486 ++ bdig tr r 534) (hbl : mbN tr r 10 < 65536) :
    mbN tr r 10 = i ∧ leafOld tr pub i = bdig tr r 486 ∧ leafNew tr pub i = bdig tr r 534 := by
  have hl := congrArg List.length hm
  simp only [List.length_append, List.length_cons, List.length_nil, bdig, List.length_map,
    List.length_range] at hl
  have h18 : (leafOld tr pub i).length = 18 := by
    rcases leafOld_len tr pub i with h | h <;> rcases leafNew_len tr pub i with h' | h' <;> omega
  obtain ⟨a, -, l1, l2⟩ := msg_split h18 (by simp [bdig]) hm
  rw [show bc tr r 10 = ((mbN tr r 10 : Nat) : F) from cell_cast tr 19 r 10] at a
  exact ⟨(cast_inj_small hi (by omega) a).symm, l1, l2⟩

/-- **The multiproof against the spec tree.**  Without a SHA-384 collision: the multiproof's partial
tree `T` (`mp_tree` with the chip's `shaNode`) has exactly the touched blocks' `blk` as leaves, with
MEMB's `hoI`/`hoO` as old/new leaf digests; every leaf's old digest is the in-state's leaf there
(`batch_update_pd`); and `memOut` is (canonically) the root of the in-state's leaves with the touched
ones replaced by their new digests. -/
theorem mp_core {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip)
    (hD30 : Dn pub ≤ 30) {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0) (hn : ¬ Sha384Coll) :
    ∃ T : PTree, T.At (WasmView.memDepth s0) 0 ∧
      (∀ i ∈ T.leaves, ∃ b, 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 ∧ mbN tr (9 * b + 8) 10 = i ∧
        leafOld tr pub i = bdig tr (9 * b + 8) 486 ∧ leafNew tr pub i = bdig tr (9 * b + 8) 534) ∧
      (∀ b, 9 * b + 8 < tr.height 19 → mbN tr (9 * b + 8) 0 = 1 → mbN tr (9 * b + 8) 10 ∈ T.leaves) ∧
      (∀ i ∈ T.leaves, (WasmView.memLeaves s0)[i]? = some (bytesOf (leafOld tr pub i))) ∧
      ∃ mf, Canon (pubDig pub pubMemOut) mf ∧
        root StateM5a.StateView.nodeH (WasmView.memDepth s0)
          ((toUpd (leafOld tr pub) (leafNew tr pub) T).apply (WasmView.memDepth s0) (WasmView.memLeaves s0)) = some mf := by
  have hP := P_val
  have HS := H.toSMP
  have hDn : Dn pub = WasmView.memDepth s0 := hG.1
  obtain ⟨T, hAt, eIn, eOut, hL1, hL2⟩ := mp_tree H hD30 SegSha.shaNode (fun r hr ha => mpm_chipO H hC hr ha)
    (fun r hr ha hro => mpm_chipN H hC hr ha hro)
  rw [hDn] at hAt hD30
  have hlt30 : ∀ i ∈ T.leaves, i < 2 ^ 30 := by
    intro i hi
    have := (PTree.At_leaves _ 0 T hAt i hi).2
    have : 2 ^ WasmView.memDepth s0 ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD30
    omega
  -- the leaves are MEMB's blocks
  have L1 : ∀ i ∈ T.leaves, ∃ b, 9 * b + 8 < tr.height 19 ∧ mbN tr (9 * b + 8) 0 = 1 ∧ mbN tr (9 * b + 8) 10 = i ∧
      leafOld tr pub i = bdig tr (9 * b + 8) 486 ∧ leafNew tr pub i = bdig tr (9 * b + 8) 534 := by
    intro i hi
    obtain ⟨o, ho, hb, hs, hc, ρ, hm⟩ := hL1 i hi
    obtain ⟨r, hr, rfl⟩ := mp_leaf_send_form H ho hb hs
    simp only at hc hm
    have hp8 : mbN tr r 9 = 1 := by
      rcases memb_p_bitS HS hr (i := 8) (by decide) with h | h
      · rw [show 1 + 8 = 9 from rfl] at h; rw [h] at hc; exact absurd rfl hc
      · rw [show 1 + 8 = 9 from rfl, show bc tr r 9 = ((mbN tr r 9 : Nat) : F) from cell_cast tr 19 r 9] at h
        exact natEq (R := 1) h (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    obtain ⟨ha, hm9⟩ := memb_pad_of_p8S HS hr hp8
    have e : r = 9 * (r / 9) + 8 := by omega
    rw [e] at hr ha hm
    obtain ⟨a, b, c⟩ := leaf_of_memb H (hlt30 i hi) hr hm.symm (memb_blk_ltS HS hr ha).1
    exact ⟨r / 9, hr, ha, a, b, c⟩
  have L2 : ∀ b, 9 * b + 8 < tr.height 19 → mbN tr (9 * b + 8) 0 = 1 → mbN tr (9 * b + 8) 10 ∈ T.leaves := by
    intro b hr8 ha8
    have ht : 19 < (wasmBaseSegAirMP nloc ngl).tables.length := segMP_lt nloc ngl 19 (by decide)
    have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
      have := (memb_posS HS _ hr8 ha8).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
    have hi : (⟨busLeaf, true, Memb.p 8, [Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++
        (names "hoO" 18).map Memb.c⟩ : Inter) ∈ ((wasmBaseSegAirMP nloc ngl).tables[19]'ht).inters := by
      rw [segMP_t19']
      have : (⟨busLeaf, true, Memb.p 8, [Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++
          (names "hoO" 18).map Memb.c⟩ : Inter) ∈ Memb.table.inters.filter (fun i => i.bus = 15) := by
        rw [memb_leaf]; exact List.mem_cons_self
      exact (List.mem_filter.mp this).1
    have hc : ((Memb.p 8).eval (tr.row pub 19 (9 * b + 8))).toNat = 1 := by
      rw [memb_p_eval tr pub _ (by decide), hp8]; rfl
    have hocc := occ_of_inter ht hr8 hi hc
    obtain ⟨i, hi', ρ, hm⟩ := hL2 _ hocc rfl rfl rfl
    have hmsg : ([Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++ (names "hoO" 18).map Memb.c).map
        (·.eval (tr.row pub 19 (9 * b + 8))) =
        [bc tr (9 * b + 8) 10, bc tr (9 * b + 8) 11] ++ bdig tr (9 * b + 8) 486 ++ bdig tr (9 * b + 8) 534 := by
      obtain ⟨-, ib, iro⟩ := mb_ix
      simp only [List.map_append, List.map_cons, List.map_nil, Memb.c, ib, iro]
      rw [bdig_eval tr pub _ 486 "hoI" (fun l hl => (mb_ix_ho l hl).1),
        bdig_eval tr pub _ 534 "hoO" (fun l hl => (mb_ix_ho l hl).2)]
      rfl
    simp only at hm
    rw [hmsg] at hm
    obtain ⟨a, -, -⟩ := leaf_of_memb H (hlt30 i hi') hr8 hm.symm (memb_blk_ltS HS hr8 ha8).1
    rw [a]; exact hi'
  -- the batched update
  have hold : (toUpd (leafOld tr pub) (leafNew tr pub) T).old StateM5a.StateView.nodeH = WasmView.memRootOf s0 := by
    rw [← toUpd_old, eIn, Canon.bytes (b := WasmView.memRootOf s0) hR]
  obtain ⟨hag, hap⟩ := batch_update_pd StateM5a.StateView.nodeH D48 nodeH_d48 (nodeH_inj hn) _ _ _
    (toUpd_fits _ _ _ 0 T hAt) (toUpd_pd _ _ T) (WasmView.memLeaves_mem s0) (WasmView.memLeaves_length s0)
    (by rw [root_memLeaves, hold])
  have hnew : (toUpd (leafOld tr pub) (leafNew tr pub) T).new StateM5a.StateView.nodeH =
      bytesOf (pubDig pub pubMemOut) := by rw [← toUpd_new, eOut]
  have hcan : Canon (pubDig pub pubMemOut) (bytesOf (pubDig pub pubMemOut)) := by
    cases T with
    | leaf j =>
      exfalso
      have h1 := memDepth_pos s0
      obtain ⟨d, hd⟩ : ∃ d, WasmView.memDepth s0 = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
      rw [hd] at hAt; simp [PTree.At] at hAt
    | stub d =>
      simp only [PTree.eval] at eIn eOut
      rw [← eOut, eIn]; rw [Canon.bytes (b := WasmView.memRootOf s0) hR]; exact hR
    | node l r =>
      rw [← eOut]; exact shaNode_canon _ _
  refine ⟨T, hAt, L1, L2, fun i hi => ?_, _, hcan, by rw [hap, hnew]⟩
  have := toUpd_agrees (leafOld tr pub) (leafNew tr pub) _ 0 T _ hAt hag i hi
  simpa using this

end mpcore

/-! ## 6. Items 1, 3, 4 for the multiproof AIR -/

section mpmain
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

/-- **Item 1 for the multiproof AIR**: the in-root binds MEMB's in-side bytes (`Dn pub ≤ 30`: the
public depth fits the multiproof's position arithmetic; the verifier fixes `D = 16`). -/
theorem seg_membIn_mp {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip)
    (hD30 : Dn pub ≤ 30) {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0) :
    MembIn tr pub s0 ∨ Sha384Coll := by
  by_cases hn : Sha384Coll
  · exact .inr hn
  have HS := H.toSMP
  obtain ⟨T, -, L1, L2, LA, -⟩ := mp_core H hC hD30 hG hR hn
  refine .inl (membIn_of_leaves HS (SegSha.ChipIf.toSMP H hC) hG hn fun b hr8 ha8 => ?_)
  have hi := L2 b hr8 ha8
  obtain ⟨b', hr8', ha8', e, eo, -⟩ := L1 _ hi
  have hbb : b' = b := Classical.byContradiction fun hne =>
    memb_blk_distinct_of_holdsS HS hne hr8' hr8 ha8' ha8 e
  subst hbb
  rw [LA _ hi, eo]

/-- **Item 3 for the multiproof AIR**: the out-root is the out-state's memory root. -/
theorem seg_memRootOut_mp {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hD30 : Dn pub ≤ 30)
    {s0 sN : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0) (hpg : sN.pages.size = s0.pages.size)
    (hfr : ∀ a, (∀ x ∈ (part Memb.table tr pub 19 busStk true).map decMsg, x.slot ≠ a) →
      readByte sN a = readByte s0 a)
    (hout : ∀ a v tp, (⟨3, a, 0, v, 0, 0, 0, tp⟩ : Msg) ∈ (part Memb.table tr pub 19 busStk false).map decMsg →
      (readByte sN a).toNat = v) :
    (MemRootOut pub sN ∧ MemGeom pub sN) ∨ Sha384Coll := by
  by_cases hn : Sha384Coll
  · exact .inr hn
  have HS := H.toSMP
  obtain ⟨hnb, hdp⟩ := nblk_depth_eq hpg
  have hGN : MemGeom pub sN := ⟨by rw [hdp]; exact hG.1, by rw [hnb]; exact hG.2⟩
  obtain ⟨T, hAt, L1, L2, -, mf, hcan, hrt⟩ := mp_core H hC hD30 hG hR hn
  have hfits := toUpd_fits (leafOld tr pub) (leafNew tr pub) _ 0 T hAt
  have hlen := Upd.apply_length _ _ _ hfits (WasmView.memLeaves_length s0)
  have hap := toUpd_apply (leafOld tr pub) (leafNew tr pub) _ 0 T _ hAt (WasmView.memLeaves_length s0)
  have hT := memLeaves_out_of HS (SegSha.ChipIf.toSMP H hC) hG hpg hfr hout hlen
    (fun b hr8 ha8 => by
      have hi := L2 b hr8 ha8
      obtain ⟨b', hr8', ha8', e, -, en⟩ := L1 _ hi
      have hbb : b' = b := Classical.byContradiction fun hne =>
        memb_blk_distinct_of_holdsS HS hne hr8' hr8 ha8' ha8 e
      subst hbb
      have hlt := (PTree.At_leaves _ 0 T hAt _ hi).2
      rw [hap _ (by omega)]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [if_pos hi, en])
    (fun i hno => by
      by_cases hi : i < 2 ^ WasmView.memDepth s0
      · rw [hap i hi]
        simp only [Nat.zero_mul, Nat.zero_add]
        rw [if_neg fun hm => by
          obtain ⟨b, hr8, ha8, e, -⟩ := L1 i hm
          exact hno b hr8 ha8 e]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [WasmView.memLeaves_length]; omega)])
  have hroot := root_memLeaves sN
  rw [← hT, hdp, hrt] at hroot
  exact .inl ⟨by rw [MemRootOut, ← Option.some.inj hroot]; exact hcan, hGN⟩

end mpmain

/-- **`seg_mem_sound_mp`**: `seg_mem_sound` for the multiproof AIR. -/
theorem seg_mem_sound_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hD30 : Dn pub ≤ 30)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hpr : HostPagesRely X.toCtx tr pub) (hcu : CutiNoMem tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0)
    (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub) (initS tr pub)) :
    (MembIn tr pub s0 ∨ Sha384Coll) ∧
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      ∀ {tN SN : Nat} {mN : List F}, Bnd X.toCtx sg sN tN SN mN (finS tr pub) →
      (MemRootOut pub sN ∧ MemGeom pub sN) ∨ Sha384Coll := by
  refine ⟨seg_membIn_mp H hC hD30 hG hR, fun sN hseg tN SN mN hN => ?_⟩
  obtain ⟨hpg, hfr⟩ := seg_mem_frame_mp X H hcode hfunc hb hg hkeep hhold hpr hst0 hlen htin hfeeN hstepgas hg64
    hinit h0 sN hseg
  exact seg_memRootOut_mp H hC hD30 hG hR hpg (fun a ha => hfr a (initS_free hcu ha)) (membOut_of_bnd hN)

end MemRoot

#print axioms MemRoot.batch_update_pd
#print axioms MemRoot.mpm_chipO
#print axioms MemRoot.mp_core
#print axioms MemRoot.seg_membIn_mp
#print axioms MemRoot.seg_memRootOut_mp
#print axioms MemRoot.seg_mem_sound_mp

end WasmBase
