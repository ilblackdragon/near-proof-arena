import ZkFormal.Near.Render.Proof.NodeFields

/-!
# ZkFormal.Near.Render.Proof.NodeBytes — `cBytes`: the bytes of the non-window fields
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-! ## Bit sums -/

theorem sum_map_two (g : Nat → Nat) : ∀ l : List Nat, (l.map fun i => 2 * g i).sum = 2 * (l.map g).sum
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_two g l]; omega

theorem bitsum (v : Nat) : ∀ k o : Nat,
    ((List.range k).map fun i => 2 ^ i * bitOf v (o + i)).sum = v / 2 ^ o % 2 ^ k
  | 0, o => by simp [Nat.mod_one]
  | k + 1, o => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have ih := bitsum v k (o + 1)
    have : ((List.range k).map ((fun i => 2 ^ i * bitOf v (o + i)) ∘ Nat.succ)) =
        (List.range k).map (fun i => 2 * (2 ^ i * bitOf v (o + 1 + i))) := by
      apply List.map_congr_left; intro i _
      simp only [Function.comp, Nat.pow_succ]
      rw [show o + (i + 1) = o + 1 + i by omega]; rw [Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
    rw [this, sum_map_two (fun i => 2 ^ i * bitOf v (o + 1 + i)), ih]
    simp only [bitOf, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.pow_succ]
    rw [← Nat.div_div_eq_div_mul]
    generalize v / 2 ^ o = w
    rw [Nat.mul_comm (2 ^ k) 2, Nat.mod_mul]

theorem nib4 (x : Nat) : (bitOf x 0 : Int) + (2 * bitOf x 1 + (4 * bitOf x 2 + 8 * bitOf x 3)) = (x % 16 : Nat) := by
  have := bitsum x 4 0
  simp [List.range_succ] at this
  omega

theorem lo8 (x : Nat) : (bitOf x 0 : Int) + (2 * bitOf x 1 + (4 * bitOf x 2 + (8 * bitOf x 3 + (16 * bitOf x 4 +
    (32 * bitOf x 5 + (64 * bitOf x 6 + 128 * bitOf x 7)))))) = (x % 256 : Nat) := by
  have := bitsum x 8 0
  simp [List.range_succ] at this
  omega

theorem hi8 (x : Nat) : (bitOf x 8 : Int) + (2 * bitOf x 9 + (4 * bitOf x 10 + (8 * bitOf x 11 + (16 * bitOf x 12 +
    (32 * bitOf x 13 + (64 * bitOf x 14 + 128 * bitOf x 15)))))) = (x / 256 % 256 : Nat) := by
  have := bitsum x 8 8
  simp [List.range_succ] at this
  omega

theorem b2n_le1 (b : Bool) : b2n b ≤ 1 := by unfold b2n; split <;> omega

theorem nib_iff (f : F) : (f.nib = true ↔ f.state = 16 ∨ f.state = 17) := by
  cases f <;> simp [F.nib, F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
    Node.sCH, Node.sMEM]

/-! ## The bytes of the non-window fields -/

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

theorem byte_facts {n p : Nat} (hn : n < e.ns.length) (hp : p < (NodeLay.layN (mkInfo c e) n).length) :
    let nr := (mkInfo c e).nodeAt n
    let A := (NodeLay.layN (mkInfo c e) n).getD p default
    let B := ((mkInfo c e).pre.getD n []).getD p 0
    let PB := ((mkInfo c e).post.getD n []).getD p 0
    (A.1.state = 14 → B = (typeOf nr).2.2.1 + 2 * (typeOf nr).2.2.2 + 3 * (typeOf nr).2.1) ∧
    (A.1.state = 15 → A.2 = 0 → B = hplenOf nr) ∧ (A.1.state = 15 → A.2 ≠ 0 → B = 0) ∧
    (A.1.state = 16 → B / 16 = 2 * (typeOf nr).1 + oddOf nr) ∧ (A.1.state = 16 → oddOf nr = 0 → B % 16 = 0) ∧
    (A.1.state = 18 → b2n nr.touched = 1 → A.2 = 0 → B = 72) ∧ (A.1.state = 18 → b2n nr.touched = 1 → A.2 ≠ 0 → B = 0) ∧
    (A.1.state = 20 → A.2 = 0 → B = bmvOf nr % 256) ∧ (A.1.state = 20 → A.2 ≠ 0 → B = bmvOf nr / 256) ∧
    (A.1.state ≠ 19 → A.1.state ≠ 21 → PB = B) := by
  intro nr A B PB
  have hb := row_b hg hs hn hp
  have hpb := row_pb hg hs hn hp
  have hm := fmem hg hs hn hp
  have hnib := nodeAt_nib hg hs hn
  dsimp only [mkR] at hb hpb hm
  change B = _ at hb
  change PB = _ at hpb
  change A.1 ∈ fieldsOf (mkInfo c e) n nr ∧ A.2 < A.1.len (hplenOf nr) at hm
  change ∀ x ∈ nr.key, x < 16 at hnib
  have hb' : B = (NodeLay.fbytes nr false A.1).getD A.2 0 := hb
  have hpb' : PB = (NodeLay.fbytes nr true A.1).getD A.2 0 := hpb
  clear hb hpb
  generalize A = fi at *
  generalize B = b at *
  generalize PB = pb at *
  obtain ⟨f, i⟩ := fi
  obtain ⟨hf, hi⟩ := hm
  simp only at hf hi hb' hpb' ⊢
  have hb2 : ∀ f ∈ branchWins (mkInfo c e) nr.kids, f.state = 21 := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf; rfl
  generalize nr = r at *
  cases f with
  | tag =>
    simp only [F.len] at hi
    simp only [F.state, Node.sTAG, show i = 0 by omega, NodeLay.fbytes] at hb' hpb' ⊢
    refine ⟨fun _ => ?_, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb', hpb']⟩
    rw [hb']; cases r with
    | leaf => rfl
    | ext => rfl
    | branch v => cases v <;> rfl
  | hpl =>
    simp only [F.state, Node.sHPL, NodeLay.fbytes] at hb' hpb' ⊢
    refine ⟨(fun h => absurd h (by decide)), fun _ h => ?_, fun _ h => ?_, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb', hpb']⟩
    · subst h; rw [hb']
      cases r with
      | leaf k v m => simp [u32r, NodeLay.hpN_len, hplenOf, isLE, NodeRec.key, NodeLay.leafB]
      | ext k kid m => simp [u32r, NodeLay.hpN_len, hplenOf, isLE, NodeRec.key, NodeLay.leafB]
      | branch v => exact absurd (hb2 _ (by cases v <;> simpa [fieldsOf, NodeRec.kids] using hf)) (by simp [F.state, Node.sHPL, Node.sHPF])
    · simp only [F.len] at hi
      rw [hb']; rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl <;> rfl
  | hpf =>
    simp only [F.len] at hi
    simp only [F.state, Node.sHPF, show i = 0 by omega, NodeLay.fbytes, NodeLay.hpf_byte] at hb' hpb' ⊢
    have hh := NodeLay.hp_head r.key (NodeLay.leafB r) hnib
    have hk0 : r.key.getD 0 0 < 16 := by
      cases h : r.key with
      | nil => simp
      | cons x l => exact hnib x (by simp [h])
    have hle : (typeOf r).1 = b2n (NodeLay.leafB r) ∧ oddOf r = r.key.length % 2 := by
      cases r with
      | leaf => simp [typeOf, NodeLay.leafB, b2n, oddOf, isLE]
      | ext => simp [typeOf, NodeLay.leafB, b2n, oddOf, isLE]
      | branch v => exact absurd (hb2 _ (by cases v <;> simpa [fieldsOf, NodeRec.kids] using hf)) (by simp [F.state, Node.sHPL, Node.sHPF])
    refine ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ => ?_, fun _ h => ?_, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      fun _ _ => by rw [hb', hpb']⟩
    · rw [hb', hh, hle.1, hle.2]; split <;> omega
    · rw [hb', hh]; rw [hle.2] at h; simp only [h, Nat.zero_ne_one, ite_false, Nat.add_zero, if_neg (show ¬ (0 = 1) by decide)]; omega
  | key => simp only [F.state, Node.sKEY, NodeLay.fbytes] at hb' hpb' ⊢
           exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
             fun _ _ => by rw [hb', hpb']⟩
  | vlen =>
    simp only [F.state, Node.sVLEN, NodeLay.fbytes] at hb' hpb' ⊢
    refine ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ ht' h => ?_, fun _ ht' h => ?_, (fun h => absurd h (by decide)),
      (fun h => absurd h (by decide)), fun _ _ => by rw [hb', hpb']⟩
    all_goals
      have ht : r.touched = true := by unfold b2n at ht'; split at ht' <;> simp_all
      have hs : NodeLay.slotR r = some .touched := by
        cases r with
        | leaf k v m => cases v <;> simp_all [NodeRec.touched, NodeLay.slotR]
        | ext => simp [NodeRec.touched] at ht
        | branch v kids m => cases v with
          | none => simp [NodeRec.touched] at ht
          | some sv => cases sv <;> simp_all [NodeRec.touched, NodeLay.slotR]
      rw [hb', hs]
    · subst h; rfl
    · simp only [F.len] at hi
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl <;> rfl
  | vh w => simp only [F.state, Node.sVH]
            exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
              fun h => absurd rfl h⟩
  | bm =>
    simp only [F.len] at hi
    simp only [F.state, Node.sBM, NodeLay.fbytes] at hb' hpb' ⊢
    have hbm : bitmapOf r.kids 0 = bmvOf r := by
      cases r with
      | leaf => simp [fieldsOf] at hf
      | ext => simp [fieldsOf] at hf
      | branch v => simp [bmvOf, isLE, NodeRec.kids]
    refine ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), fun _ h => ?_, fun _ h => ?_,
      fun _ _ => by rw [hb', hpb']⟩
    · subst h; rw [hb', hbm]; rfl
    · rw [hb', show i = 1 by omega, hbm]; rfl
  | ch w => simp only [F.state, Node.sCH]
            exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
              fun _ h => absurd rfl h⟩
  | mem => simp only [F.state, Node.sMEM, NodeLay.fbytes] at hb' hpb' ⊢
           exact ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
             fun _ _ => by rw [hb', hpb']⟩

set_option maxHeartbeats 4000000 in
theorem cBytes_node {q : Nat} (hqn : q < RN c e) : RowGoal c e Node.cBytes q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hw := nodeAt_wf hg hs hn
  have hbf := byte_facts hg hs hn hp
  simp only at hbf
  have hb8 := row_b8 hg hs hn hp
  dsimp only [mkR] at hb8
  have hodd : oddOf ((mkInfo c e).nodeAt n) = 0 ∨ oddOf ((mkInfo c e).nodeAt n) = 1 := by
    unfold oddOf; split <;> omega
  generalize hA : (NodeLay.layN (mkInfo c e) n).getD p default = A at *
  generalize hB : ((mkInfo c e).pre.getD n []).getD p 0 = B at *
  simp only [Node.cBytes, List.mem_cons, List.not_mem_nil, or_false] at hex
  generalize HN c e = H at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals node_rc []
  all_goals try simp only [hA, hB]
  · have h := hbf.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h1 := nib4 (B / 16); have h2 := nib4 (B % 16); have h3 := nib_iff A.1; cases hnbv : A.1.nib <;> simp only [hnbv, Bool.false_eq_true, ite_false, ite_true, true_iff, false_iff] at h3 ⊢ <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.1; have h1 := nib4 (B / 16); have h3 := nib_iff A.1; cases hnbv : A.1.nib <;> simp only [hnbv, Bool.false_eq_true, ite_false, ite_true, true_iff, false_iff] at h3 ⊢ <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.2.1; have h2 := nib4 (B % 16); have h3 := nib_iff A.1; rcases hodd with ho | ho <;> simp only [ho] <;> cases hnbv : A.1.nib <;> simp only [hnbv, Bool.false_eq_true, ite_false, ite_true, true_iff, false_iff] at h3 ⊢ <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.2.2.1; have ht := b2n_le1 ((mkInfo c e).nodeAt n).touched; generalize b2n ((mkInfo c e).nodeAt n).touched = tv at *; rcases (show tv = 0 ∨ tv = 1 by omega) with rfl | rfl <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.2.2.2.1; have ht := b2n_le1 ((mkInfo c e).nodeAt n).touched; generalize b2n ((mkInfo c e).nodeAt n).touched = tv at *; rcases (show tv = 0 ∨ tv = 1 by omega) with rfl | rfl <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.2.2.2.2.1; have h1 := lo8 (bmvOf ((mkInfo c e).nodeAt n)); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.2.2.2.2.2.1; have h1 := hi8 (bmvOf ((mkInfo c e).nodeAt n)); have h2 := (flag_facts _ hw).2.2.2.2.2; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
  · have h := hbf.2.2.2.2.2.2.2.2.2; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)

set_option maxHeartbeats 4000000 in
theorem cBytes_other {q : Nat} (hq : RN c e ≤ q) (hqH : q < HN c e) : RowGoal c e Node.cBytes q := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 163 → C x = (if q = RN c e then (sumCell (totalOf (mkInfo c e)) x : Int)
      else (padCell (totalOf (mkInfo c e)) x : Int)) := by
    intro x hx; rw [hC x hx]
    split
    · subst q; rw [X_sum]
    · rw [X_pad (by omega)]
  simp only [Node.cBytes, List.mem_cons, List.not_mem_nil, or_false] at hex
  generalize HN c e = H at *
  generalize totalOf (mkInfo c e) = T at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals split <;> simp [sumCell, padCell, Node.sumr, Node.sz]

theorem cBytes_ok : GroupOk c e Node.cBytes :=
  groupOk_of (fun _ h => cBytes_node hg hs h) (cBytes_other hg hs (Nat.le_refl _) (by have := RN_lt (c := c) (e := e); omega))
    (fun _ h1 h2 => cBytes_other hg hs (by omega) h2)

end

end NodeRow

end ZkFormal.Near.Render
