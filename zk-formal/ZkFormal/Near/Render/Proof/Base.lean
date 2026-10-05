import ZkFormal.Near.Render.Statements
import ZkFormal.Near.Extract.Eval
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Render.Proof.Base — the honest trace, cell by cell

`render c e` reads table `t ∈ 1…6` from the bundle's row arrays; heights
`clog2` of their sizes.  Tables built by `mkTab H W f` read `f r col`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem mkInfo_e {c : Claim} {e : Ext} : (mkInfo c e).e = e := rfl

/-- Rows `t − 1` of the six NEAR tables (`1 node … 6 sort`). -/
def partOf (B : Bundle) : Nat → Array Row
  | 1 => B.node | 2 => B.walk | 3 => B.rcpt | 4 => B.acct | 5 => B.mrk | 6 => B.sort
  | _ => #[]

theorem render_log (c : Claim) (e : Ext) {t : Nat} (h0 : t ≠ 0) (h7 : t < 7) :
    (render c e).log t = clog2 (partOf (bundle c e) t).size := by
  match t, h0, h7 with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ =>
    simp [render, renderParts, partOf]

theorem getD_map_ofNat (A : Array Row) (r col : Nat) :
    ((Option.map (fun x => Array.map Fp.ofNat x) A[r]?).getD #[])[col]?.getD 0 =
      Fp.ofNat ((A[r]?.getD #[])[col]?.getD 0) := by
  cases A[r]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
    cases row[col]? <;> rfl

theorem render_cell (c : Claim) (e : Ext) {t : Nat} (h0 : t ≠ 0) (h7 : t < 7) (r col : Nat) :
    (render c e).cell t r col = Fp.ofNat (((partOf (bundle c e) t).getD r #[]).getD col 0) := by
  match t, h0, h7 with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ =>
    simp [render, renderParts, partOf, getD_map_ofNat]

/-! ## `clog2`, `logOf` -/

theorem clog2_go_pow (k : Nat) : ∀ f a, a ≤ k → k < a + f → clog2.go (2 ^ k) f a = k := by
  intro f
  induction f with
  | zero => intro a h1 h2; omega
  | succ f ih =>
    intro a h1 h2
    simp only [clog2.go]
    by_cases h : a = k
    · subst h; simp
    · have : ¬ 2 ^ k ≤ 2 ^ a := by
        rw [Nat.not_le]; exact Nat.pow_lt_pow_right (by omega) (by omega)
      rw [if_neg this]; exact ih (a + 1) (by omega) (by omega)

theorem clog2_pow (k : Nat) : clog2 (2 ^ k) = k :=
  clog2_go_pow k _ 0 (Nat.zero_le _) (by simpa using Nat.lt_two_pow_self)

theorem clog2_go_le {m k : Nat} (hm : m ≤ 2 ^ k) : ∀ f a, a ≤ k → clog2.go m f a ≤ k := by
  intro f
  induction f with
  | zero => intro a h; simpa [clog2.go] using h
  | succ f ih =>
    intro a h
    simp only [clog2.go]
    split
    · exact h
    · rename_i hn
      by_cases ha : a = k
      · subst ha; exact absurd hm hn
      · exact ih (a + 1) (by omega)

theorem clog2_le {m k : Nat} (hm : m ≤ 2 ^ k) : clog2 m ≤ k := clog2_go_le hm _ 0 (Nat.zero_le _)

theorem logOf_le {m k : Nat} (hk : 1 ≤ k) (hm : m ≤ 2 ^ k) : logOf m ≤ k := by
  have := clog2_le hm; simp only [logOf]; omega

theorem one_le_logOf (m : Nat) : 1 ≤ logOf m := by simp only [logOf]; omega

theorem clog2_go_ge {m : Nat} : ∀ f a, m ≤ 2 ^ (a + f) → m ≤ 2 ^ clog2.go m f a := by
  intro f
  induction f with
  | zero => intro a h; simpa [clog2.go] using h
  | succ f ih =>
    intro a h
    simp only [clog2.go]
    split
    · assumption
    · exact ih (a + 1) (by rw [show a + 1 + f = a + (f + 1) by omega]; exact h)

theorem le_pow_logOf (m : Nat) : m ≤ 2 ^ logOf m := by
  have h1 : m ≤ 2 ^ clog2 m := clog2_go_ge m 0 (by simpa using Nat.le_of_lt Nat.lt_two_pow_self)
  have h2 : 2 ^ clog2 m ≤ 2 ^ logOf m := Nat.pow_le_pow_right (by omega) (by simp only [logOf]; omega)
  omega

/-! ## `mkTab` -/

theorem mkTab_size (H W : Nat) (f : Nat → Nat → Nat) : (mkTab H W f).size = H := by
  simp [mkTab]

theorem mkTab_get {H W : Nat} {f : Nat → Nat → Nat} {q col : Nat} (hq : q < H) (hc : col < W) :
    ((mkTab H W f).getD q #[]).getD col 0 = f q col := by
  simp [mkTab, hq, hc, Array.getD_eq_getD_getElem?]

/-- A table of `render` built by `mkTab (2^L) W f`. -/
theorem render_mkTab {c : Claim} {e : Ext} {t L W : Nat} {f : Nat → Nat → Nat} (h0 : t ≠ 0) (h7 : t < 7)
    (hp : partOf (bundle c e) t = mkTab (2 ^ L) W f) :
    (render c e).log t = L ∧ (render c e).height t = 2 ^ L ∧
    ∀ q col, q < 2 ^ L → col < W → (render c e).cell t q col = Fp.ofNat (f q col) := by
  have hl : (render c e).log t = L := by rw [render_log c e h0 h7, hp, mkTab_size, clog2_pow]
  refine ⟨hl, by simp [Trace.height, hl], fun q col hq hc => ?_⟩
  rw [render_cell c e h0 h7, hp, mkTab_get hq hc]

/-! ## Traffic as lists -/

theorem flatMap_single {α β : Type} {l : List α} {f : α → List β} {g : α → β}
    (h : ∀ q ∈ l, f q = [g q]) : l.flatMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, List.map_cons, h x (by simp), List.singleton_append]
    rw [ih (fun q hq => h q (by simp [hq]))]

theorem nodup_map_on {α β : Type} {l : List α} {f : α → β}
    (h : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (hl : l.Nodup) : (l.map f).Nodup := by
  unfold List.Nodup at hl ⊢
  rw [List.pairwise_map]
  exact hl.imp_of_mem fun ha hb hne heq => hne (h _ ha _ hb heq)

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem flatMap_nil' {α β : Type} {l : List α} {f : α → List β} (h : ∀ q ∈ l, f q = []) :
    l.flatMap f = [] := List.flatMap_eq_nil_iff.2 h

theorem range_split {n H : Nat} (h : n ≤ H) : List.range H = List.range n ++ (List.range (H - n)).map (n + ·) := by
  rw [← List.range_add, Nat.add_sub_cancel' h]

/-- Uniform chunks: `k` messages per element. -/
theorem flatMap_chunks {α β : Type} (k : Nat) (hk : 0 < k) (d : α) (h : α → Nat → β) :
    ∀ S : List α, S.flatMap (fun x => (List.range k).map (h x)) =
      (List.range (k * S.length)).map (fun q => h (S.getD (q / k) d) (q % k))
  | [] => by simp
  | x :: S => by
    rw [List.flatMap_cons, flatMap_chunks k hk d h S, List.length_cons, Nat.mul_succ, Nat.add_comm,
      List.range_add, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left; intro q hq
      have := List.mem_range.1 hq
      simp [Nat.div_eq_of_lt this, Nat.mod_eq_of_lt this]
    · apply List.map_congr_left; intro q _
      simp only [Function.comp_apply]
      rw [show (k + q) / k = q / k + 1 by rw [Nat.add_comm, Nat.add_div_right _ hk],
        show (k + q) % k = q % k by rw [Nat.add_comm, Nat.add_mod_right]]
      simp

theorem perm_flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, (f x).Perm (g x)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (fun y hy => h y (by simp [hy])))

theorem perm_flatMap_append {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (ih.append_left (g x)).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _

theorem range_flatMap_chunks {β : Type} (k : Nat) (f : Nat → List β) :
    ∀ n, (List.range (k * n)).flatMap f = (List.range n).flatMap fun t => (List.range k).flatMap fun i => f (k * t + i)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.mul_succ, List.range_add, List.flatMap_append, range_flatMap_chunks k f n, List.range_succ,
      List.flatMap_append, List.flatMap_map]
    simp

theorem flatMap_getD {α β : Type} (d : α) (l : List α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun t => f (l.getD t d) := by
  have : (List.range l.length).map (fun t => l.getD t d) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  conv => lhs; rw [← this]
  rw [List.flatMap_map]

/-- `TableTraffic` from the per-bus message lists of the rows (up to permutation). -/
theorem traffic_of {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp} {tf : Traffic}
    (hs : ∀ b, ((List.range (tr.height t)).flatMap fun r => rowTraffic is tr t r pub b true).Perm
      ((tf.sends b).map Msg.toFp))
    (hr : ∀ b, ((List.range (tr.height t)).flatMap fun r => rowTraffic is tr t r pub b false).Perm
      ((tf.recvs b).map Msg.toFp)) :
    TableTraffic is tr t pub tf := by
  intro b m
  rw [tableBusCount_eq, tableBusCount_eq]
  exact ⟨(hs b).count_eq m, (hr b).count_eq m⟩

/-- Multiplicity of a one-bit interaction. -/
theorem multNat_one {g : Expr} {msg : List Expr} {bus : Nat} {s : Bool} {tr : Trace Fp} {t r : Nat}
    {pub : List Fp} :
    Interaction.multNat ⟨bus, [g], msg, s⟩ tr t r pub = if g.eval tr t r pub = 1 then 1 else 0 := by
  simp [Interaction.multNat, Interaction.multNat.go]

end ZkFormal.Near.Render
