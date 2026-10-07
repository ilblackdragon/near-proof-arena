import ZkFormal.NearV3.Render.Node.FieldFacts
import ZkFormal.Near.Render.Proof.NodeBytes

/-!
# ZkFormal.NearV3.Render.Node.ByteFacts — the bytes of the non-window fields
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- The value-length bytes of a record. -/
def lenBOf (v : NodeV3) : List Nat := ((slotOf v).map NSlot3.lenB).getD []

theorem le256_snoc : ∀ (a : List Nat) (c : Nat), le256 (a ++ [c]) = le256 a + 256 ^ a.length * c
  | [], c => by simp [le256]
  | x :: a, c => by
    simp only [List.cons_append, le256, le256_snoc a c, List.length_cons, Nat.pow_succ, Nat.mul_add, Nat.add_assoc]
    rw [Nat.mul_comm (256 ^ a.length) 256, Nat.mul_assoc]

theorem le256_take_succ (l : List Nat) (i : Nat) (h : i + 1 < l.length) :
    le256 (l.take (i + 2)) = le256 (l.take (i + 1)) + 256 ^ (i + 1) * l.getD (i + 1) 0 := by
  rw [show i + 2 = (i + 1) + 1 by omega, List.take_succ, List.getElem?_eq_getElem h, Option.toList_some,
    le256_snoc, List.length_take, Nat.min_eq_left (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem le256_take_one (l : List Nat) (h : l ≠ []) : le256 (l.take 1) = l.getD 0 0 := by
  cases l with
  | nil => exact absurd rfl h
  | cons x l => simp [le256]

theorem key_nib {v : NodeV3} (hw : v.wf) : ∀ x ∈ keyOf v, x < 16 := by
  cases v with
  | leaf k s m => exact hw.1
  | ext k kid m => exact hw.1
  | branch => simp [keyOf]

theorem hpN_lt' (k : List Nat) (b : Bool) (i : Nat) : (hpN k b).getD i 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (hpN k b)[i]? with
  | none => simp
  | some x => exact Link.hpN_lt k b x (List.mem_of_getElem? h)

section
variable {vs : List NodeS3} (ok : NodeOk vs) {n p : Nat} (hn : n < vs.length) (hp : p < (layN vs n).length)
include ok hn hp

theorem byte_facts :
    let v := (rec vs n).v
    let A := (layN vs n).getD p default
    let B := (v.ser false).getD p 0
    let PB := (v.ser true).getD p 0
    (A.1.state = 14 → B = (typeOf v).2.2.1 + 2 * (typeOf v).2.2.2 + 3 * (typeOf v).2.1) ∧
    (A.1.state = 15 → B = (u32Bytes (hplenOf v)).getD A.2 0) ∧ (A.1.state = 15 → B < 256) ∧
    (A.1.state = 16 → B / 16 = 2 * (typeOf v).1 + oddOf v) ∧ (A.1.state = 16 → oddOf v = 0 → B % 16 = 0) ∧
    (A.1.state = 16 ∨ A.1.state = 17 → B < 256) ∧
    (A.1.state = 18 → B = (lenBOf v).getD A.2 0) ∧
    (A.1.state = 20 → A.2 = 0 → B = bmvOf v % 256) ∧ (A.1.state = 20 → A.2 ≠ 0 → B = bmvOf v / 256) ∧
    (A.1.state ≠ 19 → A.1.state ≠ 21 → PB = B) := by
  intro v A B PB
  have hb := row_b ok hn hp false
  have hpb := row_b ok hn hp true
  have hm := fmem ok hn hp
  have hw := rwf ok hn
  have hnib := key_nib hw
  have hb' : B = (fbytes v false A.1).getD A.2 0 := hb
  have hpb' : PB = (fbytes v true A.1).getD A.2 0 := hpb
  have hm' : A.1 ∈ fieldsOf v ∧ A.2 < A.1.len (hplenOf v) := hm
  have hnib' : ∀ x ∈ keyOf v, x < 16 := hnib
  clear hb hpb hm hnib hw
  generalize A = fi at *
  generalize B = b' at *
  generalize PB = pb' at *
  generalize v = r at *
  obtain ⟨f, i⟩ := fi
  obtain ⟨hf, hi⟩ := hm'
  have hb := hb'
  have hpb := hpb'
  have hnib := hnib'
  clear hb' hpb' hnib'
  simp only at hf hi hb hpb ⊢
  have hb2 : ∀ f ∈ branchWins (kidsOf r), f.state = 21 := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl
  cases f with
  | tag =>
    simp only [F.len] at hi
    simp only [F.state, Node.sTAG, show i = 0 by omega, fbytes] at hb hpb ⊢
    refine ⟨fun _ => ?_, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb, hpb]⟩
    rw [hb]; cases r with
    | leaf => rfl
    | ext => rfl
    | branch sv => cases sv <;> rfl
  | hpl =>
    simp only [F.state, Node.sHPL, fbytes] at hb hpb ⊢
    have hh : (hpN (keyOf r) (isLeaf r)).length = hplenOf r := by
      cases r with
      | leaf k sv m => simp [hpN_len, hplenOf, isLE, keyOf, isLeaf]
      | ext k kid m => simp [hpN_len, hplenOf, isLE, keyOf, isLeaf]
      | branch sv => exact absurd (hb2 _ (by cases sv <;> simpa [fieldsOf, kidsOf] using hf)) (by decide)
    refine ⟨(fun h => absurd h (by decide)), fun _ => by simpa only [hh] using hb,
      fun _ => ?_, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb, hpb]⟩
    rw [hb, List.getD_eq_getElem?_getD]
    cases he : (u32Bytes (hpN (keyOf r) (isLeaf r)).length)[i]? with
    | none => simp
    | some x => exact u32Bytes_lt _ _ (List.mem_of_getElem? he)
  | hpf =>
    simp only [F.len] at hi
    simp only [F.state, Node.sHPF, show i = 0 by omega, fbytes, NodeLay.hpf_byte] at hb hpb ⊢
    have hh := NodeLay.hp_head (keyOf r) (isLeaf r) hnib
    have hk0 : (keyOf r).getD 0 0 < 16 := by
      cases h : keyOf r with
      | nil => simp
      | cons x l => exact hnib x (by simp [h])
    have hle : (typeOf r).1 = b2n (isLeaf r) ∧ oddOf r = (keyOf r).length % 2 := by
      cases r with
      | leaf => simp [typeOf, isLeaf, b2n, oddOf, isLE]
      | ext => simp [typeOf, isLeaf, b2n, oddOf, isLE]
      | branch sv => exact absurd (hb2 _ (by cases sv <;> simpa [fieldsOf, kidsOf] using hf)) (by simp [F.state, Node.sHPL, Node.sHPF])
    have hlt := hpN_lt' (keyOf r) (isLeaf r) 0
    refine ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ => ?_, fun _ h => ?_, fun _ => by rw [hb]; exact hlt, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb, hpb]⟩
    · rw [hb, hh, hle.1, hle.2]; have := b2n_le' (isLeaf r); split <;> omega
    · rw [hb, hh]; rw [hle.2] at h; simp only [h, Nat.zero_ne_one, ite_false, Nat.add_zero, if_neg (show ¬ (0 = 1) by decide)]; omega
  | key =>
    simp only [F.state, Node.sKEY, fbytes] at hb hpb ⊢
    refine ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ => ?_, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb, hpb]⟩
    rw [hb, NodeLay.key_byte]; exact hpN_lt' _ _ _
  | vlen =>
    simp only [F.state, Node.sVLEN, fbytes] at hb hpb ⊢
    exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ => hb, (fun h => absurd h (by decide)),
      (fun h => absurd h (by decide)), fun _ _ => by rw [hb, hpb]⟩
  | vh w => simp only [F.state, Node.sVH]
            exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
              fun h => absurd rfl h⟩
  | bm =>
    simp only [F.len] at hi
    simp only [F.state, Node.sBM, fbytes] at hb hpb ⊢
    refine ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ h => ?_, fun _ h => ?_,
      fun _ _ => by rw [hb, hpb]⟩
    · subst h; rw [hb]; rfl
    · rw [hb, show i = 1 by omega]; rfl
  | ch w => simp only [F.state, Node.sCH]
            exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
              fun _ h => absurd rfl h⟩
  | mem => simp only [F.state, Node.sMEM, fbytes] at hb hpb ⊢
           exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
             fun _ _ => by rw [hb, hpb]⟩

end

/-- The value length bytes: four of them, and, for a revealed value, `vlen` with top byte `0`. -/
theorem lenB_facts {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length)
    (hf : F.vlen ∈ fieldsOf (rec vs n).v) :
    (lenBOf (rec vs n).v).length = 4 ∧
    (tvOf (rec vs n).v = true → le256 (lenBOf (rec vs n).v) = vlenOf (rec vs n).v ∧
      (lenBOf (rec vs n).v).getD 3 0 = 0) := by
  have hw := rwf ok hn
  have hlb := ok.lenB _ (rec_mem hn)
  generalize rec vs n = s at hw hlb hf
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE, ucid, mU⟩ := s
  simp only at hw hlb hf ⊢
  cases v with
  | leaf k sl m =>
    obtain ⟨-, hs, -⟩ := hw
    cases sl with
    | ref l h => exact ⟨hs.1, fun h => by simp [tvOf, NodeV3.value] at h⟩
    | val l i vl pre po wr =>
      obtain ⟨h1, -, -, -, h3, h4⟩ := hs
      refine ⟨h1, fun _ => ⟨?_, h3⟩⟩
      simp only [lenBOf, slotOf, Option.map_some, Option.getD_some, NSlot3.lenB, vlenOf, NodeV3.value]
      exact h4 (hlb l i vl pre po wr (.inl ⟨k, m, rfl⟩))
  | ext => simp [fieldsOf] at hf
  | branch sv kids m =>
    obtain ⟨-, hs, -, -⟩ := hw
    cases sv with
    | none =>
      simp [fieldsOf] at hf
      obtain ⟨_, _, _, _, _, _, h⟩ := mem_branchWins hf; cases h
    | some sl =>
      have hs' := hs sl rfl
      cases sl with
      | ref l h => exact ⟨hs'.1, fun h => by simp [tvOf, NodeV3.value] at h⟩
      | val l i vl pre po wr =>
        obtain ⟨h1, -, -, -, h3, h4⟩ := hs'
        refine ⟨h1, fun _ => ⟨?_, h3⟩⟩
        simp only [lenBOf, slotOf, Option.map_some, Option.getD_some, NSlot3.lenB, vlenOf, NodeV3.value]
        exact h4 (hlb l i vl pre po wr (.inr ⟨kids, m, rfl⟩))

end NodeGen3

end ZkFormal.NearV3.Render
