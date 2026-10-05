import ZkFormal.Near.Render.Proof.NodeViewFacts

/-!
# ZkFormal.Near.Render.Proof.NodeLayout — the bytes of a node, field by field

`fbytes`: the bytes of each field of `fieldsOf`; the view's serialization is
their concatenation (`ser_fields`), each has the field's length
(`fbytes_len`), so the generator's serialization is read off the layout
(`pre_layout`, `post_layout`).  Key bytes are packed nibbles (`hp_head`,
`hp_tail`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

set_option linter.unusedSimpArgs false

namespace NodeLay
open NodeGen NodeInfo

def tagOf : NodeRec → Nat
  | .leaf .. => 0
  | .ext .. => 3
  | .branch none .. => 1
  | .branch (some _) .. => 2

def leafB : NodeRec → Bool
  | .leaf .. => true
  | _ => false

def slotR : NodeRec → Option VSlot
  | .leaf _ v _ => some v
  | .branch v _ _ => v
  | _ => none

def memR : NodeRec → Nat
  | .leaf _ _ m => m
  | .ext _ _ m => m
  | .branch _ _ m => m

/-- The bytes of field `f` of record `nr` (pre: `post = false`). -/
def fbytes (nr : NodeRec) (post : Bool) : F → List Nat
  | .tag => [tagOf nr]
  | .hpl => u32r (hpN nr.key (leafB nr)).length
  | .hpf => (hpN nr.key (leafB nr)).take 1
  | .key => (hpN nr.key (leafB nr)).drop 1
  | .vlen => match slotR nr with
    | some (.ref len _) => leBytes 4 len
    | _ => u32r 72
  | .vh w => if post then w.post else w.pre
  | .bm => [bitmapOf nr.kids 0 % 256, bitmapOf nr.kids 0 / 256]
  | .ch w => if post then w.post else w.pre
  | .mem => leBytes 8 (memR nr)

section
variable (I : Info) (n : Nat)

theorem kidWin_bytes (k : Kid) (w : Nat) (l : Bool) (sl : Option Nat) (post : Bool) :
    (if post then (kidWin I k w l sl).post else (kidWin I k w l sl).pre) = (nkidOf I k).bytes post := by
  cases k <;> cases post <;> rfl

theorem branchWins_bytes (kids : List Kid) (post : Bool) (nr : NodeRec) :
    (branchWins I kids).flatMap (fbytes nr post) = (kids.map (nkidOf I)).flatMap (NKid.bytes post) := by
  unfold branchWins
  generalize hP : (kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none) = P
  have h1 : ((P.zip (List.range P.length)).map (fun x => F.ch (kidWin I x.1.1 x.2 (x.2 + 1 = P.length)
      (some x.1.2)))).flatMap (fbytes nr post) = P.flatMap fun x => (nkidOf I x.1).bytes post := by
    rw [List.flatMap_map]
    have : ∀ (Q : List (Kid × Nat)) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => fbytes nr post (F.ch (kidWin I x.1.1 x.2 (x.2 + 1 = P.length) (some x.1.2)))) =
          Q.flatMap fun x => (nkidOf I x.1).bytes post := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L =>
          simp only [List.zip_cons_cons, List.flatMap_cons]
          rw [ih L (by simpa using hL)]
          simp only [fbytes, kidWin_bytes]
    exact this P _ (by simp)
  have h2 : (kids.zip (List.range kids.length)).flatMap (fun x => (nkidOf I x.1).bytes post) =
      (kids.map (nkidOf I)).flatMap (NKid.bytes post) := by
    have : ∀ (Q : List Kid) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => (nkidOf I x.1).bytes post) = (Q.map (nkidOf I)).flatMap (NKid.bytes post) := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L => simp only [List.zip_cons_cons, List.flatMap_cons, List.map_cons]; rw [ih L (by simpa using hL)]
    exact this kids _ (by simp)
  have h3 : P.flatMap (fun x => (nkidOf I x.1).bytes post) =
      (kids.zip (List.range kids.length)).flatMap (fun x => (nkidOf I x.1).bytes post) := by
    rw [← hP]
    generalize kids.zip (List.range kids.length) = Q
    induction Q with
    | nil => rfl
    | cons q Q ih =>
      by_cases hq : q.1 = .none
      · simp only [List.filter_cons, hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false, List.flatMap_cons, ih]
        simp [nkidOf, NKid.bytes]
      · simp only [List.filter_cons, hq, ne_eq, not_false_eq_true, decide_true, if_true, List.flatMap_cons, ih]
  rw [h1, h3, h2]

theorem take_tail (l X : List Nat) : l.take 1 ++ (l.tail ++ X) = l ++ X := by
  cases l <;> simp

theorem take_tail' (l : List Nat) : l.take 1 ++ l.tail = l := by
  cases l <;> simp

/-- **The view's serialization is the concatenation of the field bytes.** -/
theorem ser_fields (nr : NodeRec) (post : Bool) :
    (nodeVOf I n nr).ser post = (fieldsOf I n nr).flatMap (fbytes nr post) := by
  cases nr with
  | leaf k v mem =>
    cases v with
    | ref len h =>
      simp only [nodeVOf, NodeV.ser, fieldsOf, List.flatMap_cons, List.flatMap_nil, fbytes, leafB, slotR,
        memR, nslotOf, NSlot.bytes, valWin, NodeRec.key, List.append_nil, List.append_assoc]
      cases post <;> simp [tagOf, take_tail]
    | touched =>
      simp only [nodeVOf, NodeV.ser, fieldsOf, List.flatMap_cons, List.flatMap_nil, fbytes, leafB, slotR,
        memR, nslotOf, NSlot.bytes, valWin, NodeRec.key, List.append_nil, List.append_assoc]
      cases post <;> simp [tagOf, take_tail]
  | ext k kid mem =>
    simp only [nodeVOf, NodeV.ser, fieldsOf, List.flatMap_cons, List.flatMap_nil, fbytes, leafB,
      memR, NodeRec.key, List.append_nil, List.append_assoc, kidWin_bytes]
    simp [tagOf, take_tail]
  | branch v kids mem =>
    have hbm : kidBitmap (kids.map (nkidOf I)) = bitmapOf kids 0 := by
      rw [Link.kidBitmap_eq, List.map_map]
      congr 1
      conv => rhs; rw [← List.map_id kids]
      apply List.map_congr_left; intro k _; cases k <;> simp [nkidOf, NKid.toRec, toBytes_toNats]
    cases v with
    | none =>
      simp only [nodeVOf, NodeV.ser, fieldsOf, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        fbytes, memR, NodeRec.kids, Option.map_none, List.append_nil, List.append_assoc, hbm,
        branchWins_bytes]
      rfl
    | some s =>
      cases s with
      | ref len h =>
        simp only [nodeVOf, NodeV.ser, fieldsOf, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
          fbytes, memR, slotR, NodeRec.kids, Option.map_some, nslotOf, NSlot.bytes, valWin, List.append_nil,
          List.append_assoc, hbm, branchWins_bytes]
        cases post <;> simp [tagOf]
      | touched =>
        simp only [nodeVOf, NodeV.ser, fieldsOf, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
          fbytes, memR, slotR, NodeRec.kids, Option.map_some, nslotOf, NSlot.bytes, valWin, List.append_nil,
          List.append_assoc, hbm, branchWins_bytes]
        cases post <;> simp [tagOf]

end

/-! ## Layout -/

theorem flatMap_layout {α : Type} [Inhabited α] (fs : List α) (g : α → List Nat) (len : α → Nat)
    (h : ∀ f ∈ fs, (g f).length = len f) :
    fs.flatMap g = (fs.flatMap fun f => (List.range (len f)).map (f, ·)).map fun fi => (g fi.1).getD fi.2 0 := by
  rw [List.map_flatMap]
  apply flatMap_congr'; intro f hf
  rw [List.map_map]
  apply List.ext_getElem (by simp [h f hf])
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-! ## Field lengths -/

theorem mem_branchWins {I : Info} {kids : List Kid} {f : F} (h : f ∈ branchWins I kids) :
    ∃ k w l j, k ∈ kids ∧ k ≠ .none ∧ f = .ch (kidWin I k w l (some j)) := by
  unfold branchWins at h
  rw [List.mem_map] at h
  obtain ⟨⟨⟨k, j⟩, w⟩, hm, rfl⟩ := h
  have hm1 := (List.of_mem_zip hm).1
  rw [List.mem_filter] at hm1
  exact ⟨k, w, _, j, (List.of_mem_zip hm1.1).1, by simpa using hm1.2, rfl⟩

theorem hpN_len (k : List Nat) (b : Bool) : (hpN k b).length = 1 + k.length / 2 := by
  unfold hpN; rw [List.length_map, hexPrefix_len]

theorem fbytes_len (I : Info) (n : Nat) {nr : NodeRec} (hw : nr.wf) (post : Bool) :
    ∀ f ∈ fieldsOf I n nr, (fbytes nr post f).length = f.len (hplenOf nr) := by
  have hkid : ∀ k w l sl, k.wf → k ≠ .none →
      (fbytes nr post (.ch (kidWin I k w l sl))).length = 32 := by
    intro k w l sl hk hne
    cases k with
    | none => exact absurd rfl hne
    | hash h => cases post <;> simpa [fbytes, kidWin, toNats_len, Kid.wf] using hk
    | node c => cases post <;> simp [fbytes, kidWin, Info.preDig, Info.postDig, shaN_len]
  have hval : ∀ v : VSlot, v.wf → (fbytes nr post (.vh (valWin I n v))).length = 32 := by
    intro v hv
    cases v with
    | ref len h => cases post <;> simpa [fbytes, valWin, toNats_len, VSlot.wf] using hv.2
    | touched => cases post <;> simp [fbytes, valWin, shaN_len]
  intro f hf
  cases nr with
  | leaf k v mem =>
    obtain ⟨-, -, hv, -⟩ := hw
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hval v hv
      | (cases v <;> simp [fbytes, F.len, hplenOf, isLE, leafB, slotR, u32r, leBytes_len, hpN_len, NodeRec.key])
  | ext k kid mem =>
    obtain ⟨-, -, hne, hk, -⟩ := hw
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hkid kid 0 true none hk hne
      | simp [fbytes, F.len, hplenOf, isLE, leafB, u32r, leBytes_len, hpN_len, NodeRec.key]
  | branch v kids mem =>
    obtain ⟨-, hv, hk, -⟩ := hw
    have hb : ∀ f ∈ branchWins I kids, (fbytes (.branch v kids mem) post f).length = f.len 0 := by
      intro f hf
      obtain ⟨k, w, l, j, hm, hne, rfl⟩ := mem_branchWins hf
      exact hkid k w l (some j) (hk k hm) hne
    cases v with
    | none =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hf
      rcases hf with rfl | rfl | hf | rfl
      · simp [fbytes, F.len]
      · simp [fbytes, F.len]
      · exact hb f (by simpa using hf)
      · simp [fbytes, F.len, leBytes_len]
    | some sl =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf | rfl
      · simp [fbytes, F.len]
      · cases sl <;> simp [fbytes, F.len, slotR, u32r, leBytes_len]
      · exact hval sl (hv sl rfl)
      · simp [fbytes, F.len]
      · exact hb f (by simpa using hf)
      · simp [fbytes, F.len, leBytes_len]

/-! ## The generator's bytes along the layout -/

/-- The layout of node `n`. -/
abbrev layN (I : Info) (n : Nat) : List (F × Nat) := layout (fieldsOf I n (I.nodeAt n)) (hplenOf (I.nodeAt n))

theorem ser_layout (I : Info) (n : Nat) (hw : (I.nodeAt n).wf) (post : Bool) :
    (nodeVOf I n (I.nodeAt n)).ser post = (layN I n).map fun fi => (fbytes (I.nodeAt n) post fi.1).getD fi.2 0 := by
  rw [ser_fields]
  exact flatMap_layout _ _ _ (fbytes_len I n hw post)

theorem nodeRecs_eq (I : Info) (n : Nat) : nodeRecs I n = (List.range (layN I n).length).map fun pos =>
    ⟨n, pos, ((layN I n).getD pos default).1, ((layN I n).getD pos default).2,
      (I.pre.getD n []).getD pos 0, (I.post.getD n []).getD pos 0⟩ := by
  simp only [nodeRecs, List.size_toArray, layN]
  apply List.map_congr_left; intro pos _
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hk : KeyBound e)
include hg hk

theorem pre_layout {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).pre.getD n [] =
      (layN (mkInfo c e) n).map fun fi => (fbytes ((mkInfo c e).nodeAt n) false fi.1).getD fi.2 0 := by
  rw [← view_pre hg hn (hk _ (List.getElem_mem hn)), ← info_nodeAt hn, ser_layout]
  rw [info_nodeAt hn]; exact hg.nodes_wf _ (List.getElem_mem hn)

theorem post_layout {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).post.getD n [] =
      (layN (mkInfo c e) n).map fun fi => (fbytes ((mkInfo c e).nodeAt n) true fi.1).getD fi.2 0 := by
  rw [← view_post hg hn (hk _ (List.getElem_mem hn)), ← info_nodeAt hn, ser_layout]
  rw [info_nodeAt hn]; exact hg.nodes_wf _ (List.getElem_mem hn)

/-- The rows of a node, with their bytes read off the fields. -/
theorem nodeRecs_bytes {n : Nat} (hn : n < e.ns.length) : nodeRecs (mkInfo c e) n =
    (List.range (layN (mkInfo c e) n).length).map fun pos =>
      let fi := (layN (mkInfo c e) n).getD pos default
      ⟨n, pos, fi.1, fi.2, (fbytes ((mkInfo c e).nodeAt n) false fi.1).getD fi.2 0,
        (fbytes ((mkInfo c e).nodeAt n) true fi.1).getD fi.2 0⟩ := by
  rw [nodeRecs_eq]
  apply List.map_congr_left; intro pos hpos
  have hpos' := List.mem_range.1 hpos
  rw [pre_layout hg hk hn, post_layout hg hk hn]
  simp [List.getD_eq_getElem?_getD, hpos']

end

/-! ## Hex-prefix bytes -/

theorem toNat_byte {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  rw [UInt8.toNat_ofNat']; omega

theorem packNibbles_getD : ∀ (l : List Nat), (∀ x ∈ l, x < 16) → ∀ m, 2 * m + 1 < l.length →
    (toNats (packNibbles l)).getD m 0 = 16 * l.getD (2 * m) 0 + l.getD (2 * m + 1) 0
  | [], _, m, h => by simp at h
  | [_], _, m, h => by simp at h
  | a :: b :: l, hl, m, h => by
    have ha := hl a (by simp); have hb := hl b (by simp)
    cases m with
    | zero =>
      simp only [packNibbles, toNats, List.map_cons, List.getD_cons_zero, Nat.mul_zero, Nat.zero_add,
        List.getD_cons_succ]
      rw [toNat_byte (by omega)]; omega
    | succ m =>
      simp only [packNibbles, toNats, List.map_cons, List.getD_cons_succ]
      have := packNibbles_getD l (fun x hx => hl x (by simp [hx])) m (by simp at h; omega)
      simp only [toNats] at this
      rw [this, show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ]

theorem hp_head (k : List Nat) (b : Bool) (hk : ∀ x ∈ k, x < 16) :
    (hpN k b).getD 0 0 = 16 * (2 * b2n b + k.length % 2) + (if k.length % 2 = 1 then k.getD 0 0 else 0) := by
  unfold hpN hexPrefix
  cases k with
  | nil => cases b <;> simp [b2n]
  | cons x rest =>
    have hx := hk x (by simp)
    by_cases h : (rest.length + 1) % 2 = 1
    · simp only [List.length_cons, h, List.map_cons, List.getD_cons_zero, if_true]
      rw [toNat_byte (by cases b <;> simp <;> omega)]
      cases b <;> simp [b2n] <;> omega
    · have h' : (rest.length + 1) % 2 = 0 := by omega
      simp only [List.length_cons, h', List.map_cons, List.getD_cons_zero]
      rw [toNat_byte (by cases b <;> simp)]
      cases b <;> simp [b2n]

theorem hp_tail (k : List Nat) (b : Bool) (hk : ∀ x ∈ k, x < 16) (m : Nat) (hm : m < k.length / 2) :
    (hpN k b).getD (m + 1) 0 =
      16 * k.getD (2 * m + k.length % 2) 0 + k.getD (2 * m + k.length % 2 + 1) 0 := by
  unfold hpN hexPrefix
  cases k with
  | nil => simp at hm
  | cons x rest =>
    by_cases h : (rest.length + 1) % 2 = 1
    · simp only [List.length_cons, h, List.map_cons, List.getD_cons_succ]
      have := packNibbles_getD rest (fun y hy => hk y (by simp [hy])) m (by simp at hm; omega)
      simp only [toNats] at this
      rw [this]
    · have h' : (rest.length + 1) % 2 = 0 := by omega
      simp only [List.length_cons, h', List.map_cons, List.getD_cons_succ, Nat.add_zero]
      have := packNibbles_getD (x :: rest) hk m (by simp at hm ⊢; omega)
      simp only [toNats] at this
      exact this

theorem hpf_byte (k : List Nat) (b : Bool) : ((hpN k b).take 1).getD 0 0 = (hpN k b).getD 0 0 := by
  cases h : hpN k b <;> simp

theorem key_byte (k : List Nat) (b : Bool) (m : Nat) : ((hpN k b).drop 1).getD m 0 = (hpN k b).getD (m + 1) 0 := by
  simp [List.getD_eq_getElem?_getD, Nat.add_comm]

end NodeLay

end ZkFormal.Near.Render
