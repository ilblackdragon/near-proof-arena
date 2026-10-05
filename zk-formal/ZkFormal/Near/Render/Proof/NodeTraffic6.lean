import ZkFormal.Near.Render.Proof.NodeTraffic5

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic6 — node traffic: EDGE, gated edges by field
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeTr
open NodeCells NodeGen NodeInfo

def _root_.ZkFormal.Near.Render.NodeGen.F.isTag : F → Bool
  | .tag => true
  | _ => false

/-- Gated edges of field `f`, index `idx` of node `n`. -/
def geF (I : Info) (n : Nat) (f : F) (idx : Nat) : List Edge :=
  ge I ⟨n, if f.isTag then 0 else 1, f, idx, (NodeLay.fbytes (I.nodeAt n) false f).getD idx 0, 0⟩

theorem ge_congr (I : Info) (n p p' : Nat) (f : F) (idx b pb pb' : Nat) (h : p = 0 ↔ p' = 0) :
    ge I ⟨n, p, f, idx, b, pb⟩ = ge I ⟨n, p', f, idx, b, pb'⟩ := by
  simp only [ge, edgeAOf, edgeBOf, h]

theorem fields_tag (I : Info) (n : Nat) (nr : NodeRec) :
    ∃ rest, fieldsOf I n nr = .tag :: rest ∧ ∀ f ∈ rest, f.isTag = false := by
  have hb : ∀ f ∈ branchWins I nr.kids, f.isTag = false := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf; rfl
  cases nr with
  | leaf k v m => exact ⟨_, rfl, by simp [F.isTag]⟩
  | ext k kid m => exact ⟨_, rfl, by simp [F.isTag]⟩
  | branch v kids m =>
    cases v with
    | none =>
      refine ⟨[F.bm] ++ branchWins I kids ++ [F.mem], rfl, fun f hf => ?_⟩
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton, List.nil_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | hf | rfl
      · rfl
      · exact hb f (by simpa [NodeRec.kids] using hf)
      · rfl
    | some sv =>
      refine ⟨[F.vlen, F.vh (valWin I n sv), F.bm] ++ branchWins I kids ++ [F.mem], rfl, fun f hf => ?_⟩
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton, List.nil_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | hf | rfl
      · rfl
      · rfl
      · rfl
      · exact hb f (by simpa [NodeRec.kids] using hf)
      · rfl

theorem lay_tag (I : Info) (n p : Nat) (hp : p < (NodeLay.layN I n).length) :
    (((NodeLay.layN I n).getD p default).1.isTag = true ↔ p = 0) := by
  obtain ⟨rest, hr, hrt⟩ := fields_tag I n (I.nodeAt n)
  have hl : NodeLay.layN I n = (F.tag, 0) :: layout rest (hplenOf (I.nodeAt n)) := by
    simp only [NodeLay.layN, hr, layout, List.flatMap_cons, F.len]; rfl
  rw [hl] at hp ⊢
  cases p with
  | zero => simp [F.isTag]
  | succ p =>
    simp only [List.getD_cons_succ, Nat.succ_ne_zero, iff_false]
    have hm : (layout rest (hplenOf (I.nodeAt n))).getD p default ∈ layout rest (hplenOf (I.nodeAt n)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hp)]; exact List.getElem_mem _
    rw [hrt _ (mem_layout hm).1]; simp

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hs : Small e)
include hg hs

theorem ge_rows {n : Nat} (hn : n < e.ns.length) :
    (nodeRecs (mkInfo c.1 e) n).flatMap (ge (mkInfo c.1 e)) =
      (fieldsOf (mkInfo c.1 e) n ((mkInfo c.1 e).nodeAt n)).flatMap fun f =>
        (List.range (f.len (hplenOf ((mkInfo c.1 e).nodeAt n)))).flatMap (geF (mkInfo c.1 e) n f) := by
  rw [NodeLay.nodeRecs_bytes hg hs.keys hn, List.flatMap_map]
  rw [flatMap_congr' (g := fun p => (fun fi => geF (mkInfo c.1 e) n fi.1 fi.2)
    ((NodeLay.layN (mkInfo c.1 e) n).getD p default)) (fun p hp => by
      simp only [geF]
      apply ge_congr
      have := lay_tag (mkInfo c.1 e) n p (List.mem_range.1 hp)
      split <;> simp_all)]
  rw [← flatMap_getD default (NodeLay.layN (mkInfo c.1 e) n) (fun fi => geF (mkInfo c.1 e) n fi.1 fi.2)]
  simp only [NodeLay.layN, layout, List.flatMap_assoc, List.flatMap_map]

end

/-! ## Gated edges of each field -/

section
variable (I : Info) (n : Nat)

/-- The edge of key nibble `i` (the last nibble of an extension goes to its child). -/
def nibE (i : Nat) : List Edge :=
  let nr := I.nodeAt n
  if isExtR nr = true ∧ i + 1 = nr.key.length then
    (if xrvOf nr then [[n, i, nr.key.getD i 0, xresOf I nr, 0]] else [])
  else [[n, i, nr.key.getD i 0, n, i + 1]]

theorem geF_tag : geF I n .tag 0 = if n = 0 then [[0, 0, SYM_START, I.res.getD n n, 0]] else [] := by
  by_cases h : n = 0 <;> simp [geF, ge, edgeAOf, edgeBOf, F.isTag, h, gated]

theorem geF_plain (f : F) (idx : Nat) (h : f = .hpl ∨ f = .vlen ∨ f = .bm ∨ f = .mem) : geF I n f idx = [] := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [geF, ge, edgeAOf, edgeBOf, F.isTag, gated]

theorem geF_vh (w : Win) (idx : Nat) : geF I n (.vh w) idx =
    if idx = 0 ∧ w.look = true then [[n, (typeOf (I.nodeAt n)).1 * (I.nodeAt n).key.length, SYM_END, n, 0]] else [] := by
  by_cases h : idx = 0 ∧ w.look = true <;> simp [geF, ge, edgeAOf, edgeBOf, F.isTag, gated, h]

theorem geF_ch (w : Win) (idx : Nat) : geF I n (.ch w) idx =
    if idx = 0 ∧ w.look = true ∧ isLE (I.nodeAt n) = false then [[n, 0, w.slot.getD 0, w.cres, 0]] else [] := by
  by_cases h : idx = 0 ∧ w.look = true ∧ isLE (I.nodeAt n) = false <;>
    simp [geF, ge, edgeAOf, edgeBOf, F.isTag, gated, h]

variable (hle : isLE (I.nodeAt n) = true) (hk : ∀ x ∈ (I.nodeAt n).key, x < 16)
include hle hk

theorem hp0 : (NodeLay.fbytes (I.nodeAt n) false .hpf).getD 0 0 % 16 = (I.nodeAt n).key.getD 0 0 ∨
    (I.nodeAt n).key.length % 2 = 0 := by
  simp only [NodeLay.fbytes, NodeLay.hpf_byte, NodeLay.hp_head _ _ hk]
  by_cases h : (I.nodeAt n).key.length % 2 = 1
  · left; simp only [h, if_true]
    have : (I.nodeAt n).key.getD 0 0 < 16 := by
      cases hkk : (I.nodeAt n).key with
      | nil => simp
      | cons x _ => simp [hkk] at hk ⊢; exact hk.1
    omega
  · right; omega

theorem geF_hpf : geF I n .hpf 0 = if (I.nodeAt n).key.length % 2 = 1 then nibE I n 0 else [] := by
  have hodd : oddOf (I.nodeAt n) = (I.nodeAt n).key.length % 2 := by simp [oddOf, hle]
  by_cases h : (I.nodeAt n).key.length % 2 = 1
  · have hb := hp0 I n hle hk
    rcases hb with hb | hb
    · simp only [geF, ge, edgeAOf, edgeBOf, F.isTag, hodd, h, if_true, hb]
      simp only [nibE, gated]
      cases hnr : I.nodeAt n with
      | leaf k v m => simp [xlast0Of, isExtR, xdeadOf, hnr]
      | ext k kid m =>
        rw [hnr] at h
        simp only [NodeRec.key] at h
        by_cases h1 : k.length = 1
        · have h2 : k.length < 2 := by omega
          cases kid <;> simp [xlast0Of, isExtR, xdeadOf, xrvOf, NodeRec.key, nokeyOf, b2n, hplenOf, isLE, h1]
        · have h2 : ¬ k.length < 2 := by omega
          have h3 : ¬ 1 = k.length := by omega
          simp [xlast0Of, isExtR, xdeadOf, xrvOf, NodeRec.key, nokeyOf, b2n, hplenOf, isLE, h1, h2, h3]
      | branch v kids m => rw [hnr] at hle; simp [isLE] at hle
    · omega
  · simp [geF, ge, edgeAOf, edgeBOf, F.isTag, hodd, h, gated]

theorem geF_key (m : Nat) (hm : m < (I.nodeAt n).key.length / 2) :
    geF I n .key m = nibE I n (2 * m + (I.nodeAt n).key.length % 2) ++
      nibE I n (2 * m + (I.nodeAt n).key.length % 2 + 1) := by
  have hodd : oddOf (I.nodeAt n) = (I.nodeAt n).key.length % 2 := by simp [oddOf, hle]
  have hpl : hplenOf (I.nodeAt n) = 1 + (I.nodeAt n).key.length / 2 := by simp [hplenOf, hle]
  have hb : (NodeLay.fbytes (I.nodeAt n) false .key).getD m 0 =
      16 * (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2) 0 +
        (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2 + 1) 0 := by
    simp only [NodeLay.fbytes, NodeLay.key_byte, NodeLay.hp_tail _ _ hk m hm]
  have hlt : (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2 + 1) 0 < 16 := by
    apply hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have h1 : (16 * (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2) 0 +
      (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2 + 1) 0) / 16 =
      (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2) 0 := by omega
  have h2 : (16 * (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2) 0 +
      (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2 + 1) 0) % 16 =
      (I.nodeAt n).key.getD (2 * m + (I.nodeAt n).key.length % 2 + 1) 0 := by omega
  have hA : ¬ (isExtR (I.nodeAt n) = true ∧ 2 * m + (I.nodeAt n).key.length % 2 + 1 = (I.nodeAt n).key.length) :=
    fun h => absurd h.2 (by omega)
  simp only [geF, ge, edgeAOf, edgeBOf, F.isTag, hodd, hb, h1, h2, F.len, hpl, nibE, gated]
  simp only [Bool.false_eq_true, if_false, Nat.one_ne_zero, false_and, hA]
  by_cases hl : m + 1 = 1 + (I.nodeAt n).key.length / 2 - 1 ∧ isExtR (I.nodeAt n) = true
  · have hB : isExtR (I.nodeAt n) = true ∧ 2 * m + (I.nodeAt n).key.length % 2 + 1 + 1 = (I.nodeAt n).key.length :=
      ⟨hl.2, by omega⟩
    rw [if_pos hl, if_pos hB]
    cases hx : xrvOf (I.nodeAt n) <;> simp [xdeadOf, hx, hl.2]
  · have hB : ¬ (isExtR (I.nodeAt n) = true ∧ 2 * m + (I.nodeAt n).key.length % 2 + 1 + 1 = (I.nodeAt n).key.length) :=
      fun h => hl ⟨by omega, h.1⟩
    rw [if_neg hl, if_neg hB]

end

end NodeTr

end ZkFormal.Near.Render
