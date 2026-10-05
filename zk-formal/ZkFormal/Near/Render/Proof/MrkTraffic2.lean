import ZkFormal.Near.Render.Proof.MrkTraffic
import ZkFormal.Near.Render.Proof.BusRids

/-!
# ZkFormal.Near.Render.Proof.MrkTraffic2 — per-node traffic of the mrk table
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkTraffic
open SortLocal (ofNat0 ofNat1)
open MrkGen

/-- The view node of shape node `x`. -/
def gNode (lv : List (List MNode)) (x : Nat × Nat × Bool) : MrkNode :=
  let (j, i, h) := x
  if h then .hashed (ch lv j (2 * i)).id (ch lv j (2 * i)).len (ch lv j (2 * i)).dig
    (ch lv j (2 * i + 1)).id (ch lv j (2 * i + 1)).len (ch lv j (2 * i + 1)).dig
  else .promoted (ch lv j (2 * i)).id (ch lv j (2 * i)).len

theorem toFp_digMsg (m : MNode) (hm : m.dig.length = 32) :
    Msg.toFp (digMsg m.id m.len m.dig) = digRow m 0 := by
  simp only [Msg.toFp, digMsg, digRow, List.map_append, List.map_cons, List.map_nil, Nat.zero_add]
  congr 1
  apply List.ext_getElem (by simp [hm])
  intro x h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < m.dig.length by simpa [hm] using h2)]

section node
variable (n : Nat) (lv : List (List MNode)) (j i : Nat)

theorem rowM_other (r : Rec) (b : Nat) (s : Bool) (h0 : b ≠ B_BYTES) (h1 : b ≠ B_DIGEST) (h9 : b ≠ B_MPOS) :
    rowM n lv r b s = [] := by
  simp [rowM, h0, h1, h9]

theorem rowM_otherS (r : Rec) (b : Nat) (h0 : b ≠ B_BYTES) (h9 : b ≠ B_MPOS) : rowM n lv r b true = [] := by
  simp [rowM, h0, h9]

theorem rowM_otherR (r : Rec) (b : Nat) (h1 : b ≠ B_DIGEST) (h9 : b ≠ B_MPOS) : rowM n lv r b false = [] := by
  simp [rowM, h1, h9]

theorem node_bytes (hL : (ch lv j (2 * i)).dig.length = 32) (hR : (ch lv j (2 * i + 1)).dig.length = 32) :
    (expand (j, i, true)).flatMap (fun r => rowM n lv r B_BYTES true) =
      (emitAt (msgId K_MRK (qBase n j + i)) 0 ((ch lv j (2 * i)).dig ++ (ch lv j (2 * i + 1)).dig)).map Msg.toFp := by
  simp only [expand, if_true, List.flatMap_map, emitAt, List.length_append, hL, hR, Nat.reduceAdd, List.map_map]
  rw [flatMap_single (g := fun p => [Fp.ofNat (K_MRK + 16 * (qBase n j + i)), Fp.ofNat (32 * (p / 32) + p % 32),
      Fp.ofNat ((chp lv j i p).dig.getD (p % 32 + 0) 0)])]
  · apply List.map_congr_left; intro p hp
    have hp' := List.mem_range.1 hp
    simp only [Function.comp_apply, Msg.toFp, List.map_cons, List.map_nil, msgId, Nat.zero_add, chp]
    congr 2
    · congr 1; omega
    · congr 2
      simp only [List.getD_eq_getElem?_getD, Nat.add_zero]
      by_cases h32 : p < 32
      · rw [if_pos (by omega), List.getElem?_append_left (by omega), Nat.mod_eq_of_lt h32]
      · rw [if_neg (by omega), List.getElem?_append_right (by omega), hL]
        congr 2; omega
  · intro p _
    simp [rowM, B_BYTES, B_DIGEST, B_MPOS]

theorem node_bytesP : (expand (j, i, false)).flatMap (fun r => rowM n lv r B_BYTES true) = [] := by
  simp [expand, rowM, B_BYTES, B_MPOS]

theorem node_mposS (h : Bool) :
    (expand (j, i, h)).flatMap (fun r => rowM n lv r B_MPOS true) =
      [Msg.toFp (if h then [j, i, msgId K_MRK (qBase n j + i), 64] else [j, i, (ch lv j (2 * i)).id, (ch lv j (2 * i)).len])] := by
  cases h with
  | true =>
    simp only [expand, if_true, List.flatMap_map]
    rw [flat64' _ (fun p _ hp => by simp [rowM, B_BYTES, B_DIGEST, B_MPOS, hp])]
    simp [rowM, B_BYTES, B_DIGEST, B_MPOS, Msg.toFp, msgId]
  | false => simp [expand, rowM, B_BYTES, B_DIGEST, B_MPOS, Msg.toFp]

theorem node_digest (h : Bool) (hL : (ch lv j (2 * i)).dig.length = 32) (hR : h = true → (ch lv j (2 * i + 1)).dig.length = 32) :
    (expand (j, i, h)).flatMap (fun r => rowM n lv r B_DIGEST false) =
      (if h then [digMsg (ch lv j (2 * i)).id (ch lv j (2 * i)).len (ch lv j (2 * i)).dig,
        digMsg (ch lv j (2 * i + 1)).id (ch lv j (2 * i + 1)).len (ch lv j (2 * i + 1)).dig] else []).map Msg.toFp := by
  cases h with
  | true =>
    simp only [expand, if_true, List.flatMap_map]
    rw [flat64 _ (fun p _ hp => by simp [rowM, B_BYTES, B_DIGEST, B_MPOS, hp])]
    simp only [List.map_cons, List.map_nil, toFp_digMsg _ hL, toFp_digMsg _ (hR rfl)]
    simp [rowM, B_BYTES, B_DIGEST, B_MPOS, chp]
  | false => simp [expand, rowM, B_BYTES, B_DIGEST, B_MPOS]

theorem node_mposR (h : Bool) :
    (expand (j, i, h)).flatMap (fun r => rowM n lv r B_MPOS false) =
      (if h then [[j - 1, 2 * i, (ch lv j (2 * i)).id, (ch lv j (2 * i)).len],
        [j - 1, 2 * i + 1, (ch lv j (2 * i + 1)).id, (ch lv j (2 * i + 1)).len]]
      else [[j - 1, 2 * i, (ch lv j (2 * i)).id, (ch lv j (2 * i)).len]]).map Msg.toFp := by
  cases h with
  | true =>
    simp only [expand, if_true, List.flatMap_map]
    rw [flat64 _ (fun p _ hp => by simp [rowM, B_BYTES, B_DIGEST, B_MPOS, hp])]
    simp [rowM, B_BYTES, B_DIGEST, B_MPOS, chp, Msg.toFp]
  | false => simp [expand, rowM, B_BYTES, B_DIGEST, B_MPOS, Msg.toFp]

end node

end MrkTraffic

end ZkFormal.Near.Render
