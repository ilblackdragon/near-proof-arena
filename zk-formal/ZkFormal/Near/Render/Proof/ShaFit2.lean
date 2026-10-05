import ZkFormal.Near.Render.Proof.ShaFit1
import ZkFormal.Near.Render.Proof.ShaTab
import ZkFormal.Near.Spec.Small

/-!
# ZkFormal.Near.Render.Proof.ShaFit2 — SHA rows of the node messages

A message of `L` bytes takes `rowsOf L = 1 + 17·⌈(L+9)/64⌉` SHA rows
(`honestRows_length`), and `8·rowsOf S ≤ 5·S` once `S ≥ 43` (tight at
`S = 56`).  Under `NodeRec.wf` only dead branches serialize to fewer than 43
bytes, so the node messages (`NPRE`, `NPOST` of every node) take
`4·rows ≤ 5·revealedOf e.ns + 144·#dead` rows (`node_rows`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- SHA rows of a message of `L` bytes. -/
def rowsOf (L : Nat) : Nat := 1 + 17 * ((L + 9 + (119 - L % 64) % 64) / 64)

theorem rowsOf_mono {a b : Nat} (h : a ≤ b) : rowsOf a ≤ rowsOf b := by
  unfold rowsOf; omega

theorem rowsOf_bound (S : Nat) : 8 * rowsOf S ≤ 5 * S + (if S < 43 then 144 else 0) := by
  unfold rowsOf; split <;> omega

theorem rowsOf_le (L : Nat) : 64 * rowsOf L ≤ 17 * L + 64 * 35 := by
  unfold rowsOf; omega

theorem msgRows_length (M : Sha.Gen.Msg) : (Sha.Gen.msgRows M).length = rowsOf M.bytes.length := by
  rw [Sha.Complete.msgRows_eq, List.length_map, List.length_range]
  have := Sha.Complete.nb_eq M
  unfold rowsOf; omega

theorem honestRows_length (gm : List Sha.Gen.Msg) :
    (Sha.Gen.honestRows gm).length = (gm.map fun M => rowsOf M.bytes.length).sum := by
  induction gm with
  | nil => rfl
  | cons M gm ih =>
    simp only [Sha.Gen.honestRows, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih, msgRows_length]; simp

/-- SHA rows of a list of NEAR messages. -/
def rowsL (ms : List Msg) : Nat := (ms.map fun m => rowsOf m.bytes.length).sum

theorem rowsL_append (a b : List Msg) : rowsL (a ++ b) = rowsL a + rowsL b := by
  simp [rowsL]

theorem shaMsgs_rows (ms : List Msg) : (Sha.Gen.honestRows (shaMsgs ms)).length = rowsL ms := by
  rw [honestRows_length]; simp [shaMsgs, rowsL, Function.comp_def]

/-! ## Sums -/

theorem sum_map_le {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h x (List.mem_cons_self ..)
    have := sum_map_le (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem sum_map_flatMap {α β : Type} (g : β → Nat) (f : α → List β) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum
  | [] => rfl
  | x :: l => by simp [List.flatMap_cons, sum_map_flatMap g f l]

theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add f g l]; omega

theorem sum_map_mul {α : Type} (k : Nat) (f : α → Nat) :
    ∀ l : List α, (l.map fun x => k * f x).sum = k * (l.map f).sum
  | [] => by simp
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul k f l, Nat.mul_add]

theorem sum_map_le_mul {α : Type} (f : α → Nat) (B : Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ B) → (l.map f).sum ≤ B * l.length
  | [], _ => by simp
  | x :: l, h => by
    have := h x (List.mem_cons_self ..)
    have := sum_map_le_mul f B l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]; omega

theorem range_map_getD {α : Type} (l : List α) (d : α) (f : α → Nat) :
    ((List.range l.length).map fun n => f (l.toArray.getD n d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [Array.getD_eq_getD_getElem?, h1]

theorem count_ite {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.map fun x => if p x then 1 else 0).sum = (l.filter p).length
  | [] => rfl
  | x :: l => by
    have := count_ite p l
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    split <;> simp <;> omega

/-! ## Record sizes -/

theorem hexPrefix_pos (k : List Nat) (b : Bool) : 1 ≤ (hexPrefix k b).length := by
  unfold hexPrefix; split <;> split <;> simp

theorem kidBytes_ge (kid : Kid) (hw : kid.wf) (hn : kid ≠ .none) :
    32 ≤ (kidBytes (fun _ => zeros 32) kid).length := by
  cases kid with
  | none => exact absurd rfl hn
  | hash h => simp only [Kid.wf] at hw; simp [kidBytes, hw]
  | node c => simp [kidBytes, zeros_len]

theorem vref_ge (v : VSlot) (hw : v.wf) : 36 ≤ (vrefBytes (zeros 32) v).length := by
  cases v with
  | ref len h => simp only [VSlot.wf] at hw; simp [vrefBytes, hw.2, u32, leN_length]
  | touched => simp [vrefBytes, zeros_len, u32, leN_length]

theorem kids_ge : ∀ kids : List Kid, (∀ kid ∈ kids, kid.wf) → kids.all (· == .none) = false →
    32 ≤ ((kids.map (kidBytes fun _ => zeros 32)).map List.length).sum
  | [], _, h => by simp at h
  | k :: ks, hw, h => by
    simp only [List.map_cons, List.sum_cons]
    by_cases hk : k = .none
    · subst hk
      have := kids_ge ks (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (by simpa using h)
      omega
    · have := kidBytes_ge k (hw k (List.mem_cons_self ..)) hk; omega

/-- Under `wf`, only dead branches are shorter than `43` bytes. -/
theorem sz0_ge (nr : NodeRec) (hw : nr.wf) (hd : nr.dead = false) : 43 ≤ sz0 nr := by
  unfold sz0
  cases nr with
  | leaf k v mem =>
    have := hexPrefix_pos k true
    have := vref_ge v hw.2.2.1
    simp only [ser, List.length_append, List.length_singleton, u32, u64, leN_length]; omega
  | ext k kid mem =>
    have := hexPrefix_pos k false
    have := kidBytes_ge kid hw.2.2.2.1 hw.2.2.1
    simp only [ser, List.length_append, List.length_singleton, u32, u64, leN_length]; omega
  | branch v kids mem =>
    cases v with
    | none =>
      have := kids_ge kids hw.2.2.1 (by simpa [NodeRec.dead] using hd)
      simp only [ser, List.length_append, List.length_singleton, u16, u64, leN_length, concatAll_len]
      omega
    | some s =>
      have := vref_ge s (hw.2.1 s rfl)
      simp only [ser, List.length_append, List.length_singleton, u16, u64, leN_length, concatAll_len]
      omega

theorem nodeSize_eq (nr : NodeRec) : nodeSize nr = sz0 nr + (if nr.touched then 72 else 0) := rfl

/-- Two messages of at most `sz0 nr` bytes. -/
theorem node_pair (nr : NodeRec) (hw : nr.wf) :
    16 * rowsOf (sz0 nr) ≤ 10 * nodeSize nr + 288 * (if nr.dead then 1 else 0) := by
  have h := rowsOf_bound (sz0 nr)
  rw [nodeSize_eq]
  by_cases hd : nr.dead = true
  · simp only [hd, ite_true]; split at h <;> split <;> omega
  · have := sz0_ge nr hw (by simpa using hd)
    simp only [hd, Bool.false_eq_true, ite_false]
    have h' : 8 * rowsOf (sz0 nr) ≤ 5 * sz0 nr := by simpa [show ¬ sz0 nr < 43 by omega] using h
    split <;> omega

section
variable {c : Claim} {e : Ext}

theorem nodeMsgs_rows : rowsL (nodeMsgs (mkInfo c e)) =
    ((List.range (mkInfo c e).ns.size).map fun n =>
      rowsOf ((mkInfo c e).pre.getD n []).length + rowsOf ((mkInfo c e).post.getD n []).length).sum := by
  simp only [rowsL, nodeMsgs, sum_map_flatMap]
  simp

/-- **SHA rows of the node messages.** -/
theorem node_rows (hg : Good c e) :
    4 * rowsL (nodeMsgs (mkInfo c e)) ≤ 5 * revealedOf e.ns + 144 * (e.ns.filter NodeRec.dead).length := by
  rw [nodeMsgs_rows]
  have hN : (mkInfo c e).ns.size = e.ns.length := by simp [mkInfo_ns]
  rw [hN]
  have h1 : ((List.range e.ns.length).map fun n =>
      rowsOf ((mkInfo c e).pre.getD n []).length + rowsOf ((mkInfo c e).post.getD n []).length).sum ≤
      ((List.range e.ns.length).map fun n => 2 * rowsOf (sz0 (e.ns.toArray.getD n (.branch none [] 0)))).sum := by
    apply sum_map_le
    intro n _
    have a := rowsOf_mono (pre_ok c e hg n).1
    have b := rowsOf_mono (post_ok c e hg n).1
    simp only [Info.nodeAt, mkInfo_ns] at a b
    omega
  rw [range_map_getD e.ns _ (fun nr => 2 * rowsOf (sz0 nr))] at h1
  have h2 : (e.ns.map fun nr => 16 * rowsOf (sz0 nr)).sum ≤
      (e.ns.map fun nr => 10 * nodeSize nr + 288 * (if nr.dead then 1 else 0)).sum :=
    sum_map_le fun nr h => node_pair nr (hg.nodes_wf nr h)
  have e1 : (e.ns.map fun nr => 16 * rowsOf (sz0 nr)).sum = 16 * (e.ns.map fun nr => rowsOf (sz0 nr)).sum :=
    sum_map_mul _ _ _
  have e2 : (e.ns.map fun nr => 2 * rowsOf (sz0 nr)).sum = 2 * (e.ns.map fun nr => rowsOf (sz0 nr)).sum :=
    sum_map_mul _ _ _
  have e3 : (e.ns.map fun nr => 10 * nodeSize nr + 288 * (if nr.dead then 1 else 0)).sum =
      10 * (e.ns.map nodeSize).sum + 288 * (e.ns.filter NodeRec.dead).length := by
    rw [sum_map_add, sum_map_mul, sum_map_mul, count_ite]
  simp only [revealedOf]
  omega

end

end ZkFormal.Near.Render
