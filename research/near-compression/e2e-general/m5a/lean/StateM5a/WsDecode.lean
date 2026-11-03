import StateM5a.DecodeM5a
import StateM5a.Sha512If
import StateM5a.WsRaw

/-!
# StateM5a.WsDecode — reading the working-set buses off `Holds` (generic part)

The tools `WsDecode2` uses to turn `Holds` of the AIR into the record-level premises of
`WsBus` / `WsSeg`:

* **Bus membership** (`mem_busList`, `busList_inv`): a row's message with multiplicity bit `1` is
  on the bus list; every message on a bus list is some row's message.
* **`RNG`** (`rng_v`): the `RNG` table's rows are `v = r` (`isFirst`, `isTransition`, height
  `≤ 2^8`); with no extra table sending on `RNG`, every value a table looks up in `RNG` is `< 256`
  (`WsDecode3.rng_send_lt`, `WsDecode3.rng_rcv`).
* **`IF384`** (`comp_mem`): under `IF384` balance, the 16 receives of a consumer row's compression
  `Ws.comp g cid ws` (`g = 1`), decoded (`decIf`, limbs as naturals), are among the decoded chip
  sends — the membership premise of `Sha512If.comp_sound` / `comp_iv` / `comp_node`.
* **Digests** (`decDig`, `rowDig`, `rowDig_of`): 18 limb columns read as a `Sha512If.Dig` (6 words);
  when the columns are the chip's limbs of a digest `d` (`enc d`), the reading is `d`.
* **Selections** (`sel_dec`, `sel2_perm`): a table's messages on one interaction, decoded, are the
  decoded rows' record messages (`List.Perm.map`, no injectivity needed).
* **Table lists** (`busList_ws`): on `WM`, `PT`, `RCH` only `WSN`, `WSA`, `WSL`, `WSP` take part,
  with the interactions pinned by `rfl` filter lemmas against the exported tables.
-/

namespace StateM5a.WsDecode

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Bus membership -/

section Mem
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] {tr : Trace F} {pub : List F}

theorem mem_tableBusList {is : List Interaction} {i : Interaction} (hi : i ∈ is) {t r : Nat}
    (hr : r < tr.height t) (hm : 1 ≤ i.multNat tr t r pub) :
    i.msgVal tr t r pub ∈ tableBusList is tr t pub i.bus i.send := by
  refine List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, ?_⟩
  unfold rowBusList
  refine List.mem_flatMap.2 ⟨i, hi, ?_⟩
  simp only [and_self, ↓reduceIte]
  exact List.mem_replicate.2 ⟨by omega, rfl⟩

theorem mem_go : ∀ (Ts : List Table) (t0 k : Nat), k < Ts.length → ∀ {m : List F} {b : Nat} {s : Bool},
    m ∈ tableBusList (Ts[k]!).interactions tr (t0 + k) pub b s → m ∈ busList.go tr pub b s Ts t0
  | [], _, _, hk, _, _, _, _ => absurd hk (Nat.not_lt_zero _)
  | T :: Ts, t0, 0, _, m, b, s, h => by
    simp only [busList.go]; exact List.mem_append_left _ (by simpa using h)
  | T :: Ts, t0, k + 1, hk, m, b, s, h => by
    simp only [busList.go]
    apply List.mem_append_right
    exact mem_go Ts (t0 + 1) k (by simp at hk; omega)
      (by rw [show t0 + 1 + k = t0 + (k + 1) by omega]; simpa using h)

theorem mem_busList (A : Air) {t : Nat} (ht : t < A.tables.length) {i : Interaction}
    (hi : i ∈ (A.tables[t]!).interactions) {r : Nat} (hr : r < tr.height t)
    (hm : 1 ≤ i.multNat tr t r pub) : i.msgVal tr t r pub ∈ busList A tr pub i.bus i.send := by
  unfold busList
  exact mem_go A.tables 0 t ht (by simpa using mem_tableBusList hi hr hm)

theorem table_inv {is : List Interaction} {t : Nat} {b : Nat} {s : Bool} {m : List F}
    (h : m ∈ tableBusList is tr t pub b s) :
    ∃ r, r < tr.height t ∧ ∃ i ∈ is, i.bus = b ∧ i.send = s ∧ m = i.msgVal tr t r pub := by
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.1 h
  unfold rowBusList at hm
  obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 hm
  split at hm
  · rename_i hc
    exact ⟨r, List.mem_range.1 hr, i, hi, hc.1, hc.2, (List.mem_replicate.1 hm).2⟩
  · simp at hm

theorem go_inv : ∀ (Ts : List Table) (t0 : Nat) {m : List F} {b : Nat} {s : Bool},
    m ∈ busList.go tr pub b s Ts t0 → ∃ k, k < Ts.length ∧ m ∈ tableBusList (Ts[k]!).interactions tr (t0 + k) pub b s
  | [], _, _, _, _, h => by simp [busList.go] at h
  | T :: Ts, t0, m, b, s, h => by
    simp only [busList.go, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, by simp, by simpa using h⟩
    · obtain ⟨k, hk, h'⟩ := go_inv Ts (t0 + 1) h
      exact ⟨k + 1, by simp; omega, by rw [show t0 + (k + 1) = t0 + 1 + k by omega]; simpa using h'⟩

/-- **Every message on a bus is some row's message.** -/
theorem busList_inv (A : Air) {b : Nat} {s : Bool} {m : List F} (h : m ∈ busList A tr pub b s) :
    ∃ t, t < A.tables.length ∧ ∃ r, r < tr.height t ∧ ∃ i ∈ (A.tables[t]!).interactions,
      i.bus = b ∧ i.send = s ∧ m = i.msgVal tr t r pub := by
  unfold busList at h
  obtain ⟨k, hk, h'⟩ := go_inv A.tables 0 h
  obtain ⟨r, hr, i, hi, e1, e2, e3⟩ := table_inv h'
  exact ⟨k, hk, r, by simpa using hr, i, hi, e1, e2, by simpa using e3⟩

end Mem

/-- A one-bit interaction with bit `1` has multiplicity `1`. -/
theorem mult_one {bus : Nat} {g : Expr} {msg : List Expr} {send : Bool} {tr : Trace Fp} {t r : Nat}
    {pub : List Fp} (hg : g.eval tr t r pub = 1) :
    1 ≤ ({ bus, mult := [g], msg, send } : Interaction).multNat tr t r pub := by
  rw [multNat_one]; simp [hg]

/-! ## The AIR the prover runs -/

section Full
variable {D : Nat} {extra : List Table} {nb np : Nat}

theorem full_len : (fullAir D extra nb np).tables.length = 12 + extra.length := by
  simp [fullAir, m5aAir]; omega

theorem full_get (k : Nat) (hk : k < 12) :
    (fullAir D extra nb np).tables[k]! = (m5aAir D).tables[k]! := by
  simp only [fullAir]
  rw [getElem!_pos _ k (by simp [m5aAir]; omega), getElem!_pos _ k (by simp [m5aAir]; omega)]
  exact List.getElem_append_left (by simp [m5aAir]; omega)

theorem full_get_extra (k : Nat) (hk : 12 ≤ k) (hk' : k < 12 + extra.length) :
    (fullAir D extra nb np).tables[k]! ∈ extra := by
  simp only [fullAir]
  rw [getElem!_pos _ k (by simp [m5aAir]; omega)]
  rw [List.getElem_append_right (by simp [m5aAir]; omega)]
  exact List.getElem_mem _

theorem full_rng : (fullAir D extra nb np).tables[9]! = Rng.table := by rw [full_get 9 (by decide)]; rfl
theorem full_wsn : (fullAir D extra nb np).tables[6]! = Wsn.table D := by rw [full_get 6 (by decide)]; rfl
theorem full_wsa : (fullAir D extra nb np).tables[7]! = Wsa.table := by rw [full_get 7 (by decide)]; rfl
theorem full_wsl : (fullAir D extra nb np).tables[10]! = Wsl.table := by rw [full_get 10 (by decide)]; rfl
theorem full_wsp : (fullAir D extra nb np).tables[11]! = Wsp.table D := by rw [full_get 11 (by decide)]; rfl
theorem full_wsb : (fullAir D extra nb np).tables[5]! = Wsb.table D := by rw [full_get 5 (by decide)]; rfl

theorem holds_constr {pub : List Fp} {tr : Trace Fp} (hH : Holds (fullAir D extra nb np) pub tr)
    {t : Nat} (ht : t < 12) {T : Table} (hT : (fullAir D extra nb np).tables[t]! = T) :
    ∀ r, r < tr.height t → ∀ e ∈ T.constraints, e.eval tr t r pub = 0 := by
  intro r hr e he
  have h := hH.constr t (by rw [full_len]; omega) r hr e
  rw [← getElem!_pos _ t (by rw [full_len]; omega), hT] at h
  exact h he

theorem holds_log {pub : List Fp} {tr : Trace Fp} (hH : Holds (fullAir D extra nb np) pub tr)
    {t : Nat} (ht : t < 12) {T : Table} (hT : (fullAir D extra nb np).tables[t]! = T) :
    tr.log t ≤ T.maxLog := by
  have h := (hH.logBound t (by rw [full_len]; omega)).2
  rw [← getElem!_pos _ t (by rw [full_len]; omega), hT] at h
  exact h

end Full

/-! ## `RNG` -/

section Rng
variable {tr : Trace Fp} {pub : List Fp}

theorem rng_mem_first : Expr.isFirst * Rng.c "v" ∈ Rng.constraints := by unfold Rng.constraints; simp
theorem rng_mem_tr : Expr.isTransition * (Rng.T.n "v" - Rng.c "v" - 1) ∈ Rng.constraints := by
  unfold Rng.constraints; simp

/-- The `RNG` rows count `0, 1, 2, …`. -/
theorem rng_v (hc : ∀ r, r < tr.height 9 → ∀ e ∈ Rng.table.constraints, e.eval tr 9 r pub = 0)
    (hlog : tr.log 9 ≤ 8) : ∀ r, r < tr.height 9 → ev tr 9 r pub (Rng.c "v") = r
  | 0, hr => by
    have h := hold rfl (hc 0 hr) rng_mem_first
    have g : ev tr 9 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
    exact FieldWsb.wsb_gate g h
  | r + 1, hr => by
    have hH : tr.height 9 ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hlog
    have ih := rng_v hc hlog r (by omega)
    have h := hold rfl (hc r (by omega)) rng_mem_tr
    have g : ev tr 9 r pub .isTransition = 1 := by
      rw [FieldWsb.ev_isTransition]; split <;> omega
    have h' := eq_of_sub (FieldWsb.wsb_gate g h)
    rw [ev_sub, show Rng.T.n "v" = Expr.col (Rng.T.L.off "v" + 0) true from rfl,
      FieldWsb.ev_next r _ hr, ih] at h'
    change (ev tr 9 (r + 1) pub (Rng.c "v") + _) % P = ev tr 9 r pub 1 at h'
    rw [ev_one] at h'
    have := ev_lt (tr := tr) (t := 9) (r := r + 1) (pub := pub) (Rng.c "v")
    omega

end Rng

/-! ## Decoders -/

def tn (x : Fp) : Nat := x.toNat

/-- A 64-bit word from its three limbs. -/
def w3 (a b c : Nat) : Nat := (a + 2 ^ 21 * b + 2 ^ 42 * c) % 2 ^ 64

/-- 18 limbs as a digest (6 words). -/
def decDig (l : List Nat) : Dig :=
  ⟨(List.range 6).map fun k => w3 (l.getD (3 * k) 0) (l.getD (3 * k + 1) 0) (l.getD (3 * k + 2) 0),
    by simp, by
      intro w hw
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw
      exact Nat.mod_lt _ (by decide)⟩

theorem w3_wlimbs {x : Nat} (hx : x < 2 ^ 64) :
    w3 (x % 2 ^ 21) (x / 2 ^ 21 % 2 ^ 21) (x / 2 ^ 42) = x := by
  unfold w3
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Reading a digest**: if the triples of `l` are the chip limbs of `d`, `l` reads as `d`. -/
theorem decDig_of {l : List Nat} {d : Dig}
    (h : (List.range 6).map (fun k => [l.getD (3 * k) 0, l.getD (3 * k + 1) 0, l.getD (3 * k + 2) 0]) = enc d) :
    decDig l = d := by
  apply Subtype.ext
  obtain ⟨dl, hlen, hw⟩ := d
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 6
  · have hk' := congrArg (fun L => L[k]?) h
    simp only [enc, List.getElem?_map, List.getElem?_range hk, Option.map_some] at hk'
    rw [List.getElem?_eq_getElem (show k < dl.length by omega)] at hk'
    simp only [Option.map_some, Option.some.injEq, wlimbs, List.cons.injEq, and_true] at hk'
    show ((List.range 6).map fun k => w3 (l.getD (3 * k) 0) (l.getD (3 * k + 1) 0) (l.getD (3 * k + 2) 0))[k]? = dl[k]?
    rw [List.getElem?_map, List.getElem?_range hk, Option.map_some,
      List.getElem?_eq_getElem (show k < dl.length by omega), hk'.1, hk'.2.1, hk'.2.2,
      w3_wlimbs (hw _ (List.getElem_mem _))]
  · show ((List.range 6).map fun k => w3 (l.getD (3 * k) 0) (l.getD (3 * k + 1) 0) (l.getD (3 * k + 2) 0))[k]? = dl[k]?
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

section Rows
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

/-- A row's 18 digest limb columns as a digest. -/
def rowDig (f : Nat → Expr) : Dig := decDig ((List.range 18).map fun j => ev tr t r pub (f j))

/-- A limb triple's values. -/
def dec3 (x : W3) : List Nat := [ev tr t r pub x.1, ev tr t r pub x.2.1, ev tr t r pub x.2.2]

end Rows

theorem digW_dec3 {tr : Trace Fp} {t r : Nat} {pub : List Fp} (f : Nat → Expr) :
    (digW f).map (dec3 tr t r pub) = (List.range 6).map fun k =>
      [((List.range 18).map fun j => ev tr t r pub (f j)).getD (3 * k) 0,
       ((List.range 18).map fun j => ev tr t r pub (f j)).getD (3 * k + 1) 0,
       ((List.range 18).map fun j => ev tr t r pub (f j)).getD (3 * k + 2) 0] := by
  simp only [digW, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk := List.mem_range.1 hk
  simp only [Function.comp_def, dec3, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show 3 * k < 18 by omega), List.getElem?_range (show 3 * k + 1 < 18 by omega),
    List.getElem?_range (show 3 * k + 2 < 18 by omega), Option.map_some, Option.getD_some]

/-- **A row digest is the chip's digest**: if a row's digest triples are `enc d`, `rowDig = d`. -/
theorem rowDig_of {tr : Trace Fp} {t r : Nat} {pub : List Fp} {f : Nat → Expr} {d : Dig}
    (h : (digW f).map (dec3 tr t r pub) = enc d) : rowDig tr t r pub f = d := by
  rw [digW_dec3] at h
  exact decDig_of h

theorem rowDig_congr {tr : Trace Fp} {t r : Nat} {pub : List Fp} {f g : Nat → Expr}
    (h : ∀ j < 18, ev tr t r pub (f j) = ev tr t r pub (g j)) : rowDig tr t r pub f = rowDig tr t r pub g := by
  unfold rowDig
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

/-! ## `IF384` -/

/-- A field `IF384` message decoded. -/
def decIf (m : List Fp) : IfMsg :=
  ⟨tn (m.getD 0 0), tn (m.getD 1 0), [tn (m.getD 2 0), tn (m.getD 3 0), tn (m.getD 4 0)],
    [tn (m.getD 5 0), tn (m.getD 6 0), tn (m.getD 7 0)]⟩

theorem dec3_zero {tr : Trace Fp} {t r : Nat} {pub : List Fp} : dec3 tr t r pub zeroW = zeroL := by
  simp [dec3, zeroW, zeroL]

theorem getD_dec3 {tr : Trace Fp} {t r : Nat} {pub : List Fp} (ws : List W3) (k : Nat) :
    (ws.map (dec3 tr t r pub)).getD k zeroL = dec3 tr t r pub (ws.getD k zeroW) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[k]? <;> simp [dec3_zero]

/-- **A consumer's compression receives are chip messages.**  Under `IF384` balance, a row with
bit `g = 1` whose table has the interactions `Ws.comp g cid ws` receives, decoded, 16 messages that
are among the decoded `IF384` sends. -/
theorem comp_mem {tr : Trace Fp} {pub : List Fp} {A : Air}
    (hperm : (busList A tr pub B_IF384 true).Perm (busList A tr pub B_IF384 false))
    {t : Nat} (ht : t < A.tables.length) {g cid : Expr} {ws : List W3}
    (hsub : ∀ i ∈ comp g cid ws, i ∈ (A.tables[t]!).interactions) {r : Nat} (hr : r < tr.height t)
    (hg : g.eval tr t r pub = 1) :
    ∀ x ∈ compRecv (ev tr t r pub cid) (ws.map (dec3 tr t r pub)),
      x ∈ (busList A tr pub B_IF384 true).map decIf := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  have hm' := List.mem_range.1 hm
  rw [getD_dec3, getD_dec3]
  generalize hA : ws.getD (2 * m) zeroW = Aw
  generalize hB : ws.getD (2 * m + 1) zeroW = Bw
  obtain ⟨a0, a1, a2⟩ := Aw
  obtain ⟨b0, b1, b2⟩ := Bw
  let i : Interaction := rcv B_IF384 g [cid, K m, a0, a1, a2, b0, b1, b2]
  have hi : i ∈ comp g cid ws := by
    unfold comp
    refine List.mem_map.2 ⟨m, hm, ?_⟩
    simp only [hA, hB]
    rfl
  have h1 := mem_busList A ht (hsub i hi) hr (mult_one hg)
  have h2 := hperm.mem_iff.2 h1
  refine List.mem_map.2 ⟨_, h2, ?_⟩
  simp only [decIf, Interaction.msgVal, i, rcv, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, IfMsg.mk.injEq, dec3]
  refine ⟨rfl, ?_, rfl, rfl⟩
  show ((Expr.const m).eval tr t r pub).toNat = m
  exact (ev_const (tr := tr) (t := t) (r := r) (pub := pub) m).trans (Nat.mod_eq_of_lt (by omega))

/-! ## Selections -/

section Sel
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- **Decoding a selection**: the decoded messages of the rows with bit `e = 1` are the record
messages `f` of the decoded active rows (bit `g`) satisfying `p`. -/
theorem sel_dec {β γ : Type} (e g : Expr) (msg : List Expr) (row : Nat → β) (p : β → Bool)
    (dec : List Fp → γ) (f : β → γ) : ∀ (rs : List Nat),
    (∀ r ∈ rs, e.eval tr t r pub = 1 ↔ (g.eval tr t r pub = 1 ∧ p (row r) = true)) →
    (∀ r ∈ rs, g.eval tr t r pub = 1 → p (row r) = true → dec (vals tr t r pub msg) = f (row r)) →
    (selL tr t pub e msg rs).map dec =
      ((rs.filterMap fun r => if g.eval tr t r pub = 1 then some (row r) else none).filter p).map f
  | [], _, _ => rfl
  | r :: rs, h1, h2 => by
    have ih := sel_dec e g msg row p dec f rs (fun r' hr' => h1 r' (List.mem_cons_of_mem _ hr'))
      (fun r' hr' => h2 r' (List.mem_cons_of_mem _ hr'))
    have a1 := h1 r (List.mem_cons_self ..)
    have a2 := h2 r (List.mem_cons_self ..)
    simp only [selL, List.filterMap_cons] at ih ⊢
    by_cases he : e.eval tr t r pub = 1
    · obtain ⟨hg, hp⟩ := a1.1 he
      simp [he, hg, hp, ih, a2 hg hp]
    · by_cases hg : g.eval tr t r pub = 1
      · have hp : p (row r) = false := by
          cases hq : p (row r)
          · rfl
          · exact absurd (a1.2 ⟨hg, hq⟩) he
        simp [he, hg, hp, ih]
      · simp [he, hg, ih]

theorem flatMap_append_perm {β γ : Type} (A B : β → List γ) :
    ∀ rs : List β, (rs.flatMap fun r => A r ++ B r).Perm (rs.flatMap A ++ rs.flatMap B)
  | [] => List.Perm.refl _
  | r :: rs => by
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine ((flatMap_append_perm A B rs).append_left (B r)).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

/-- A two-interaction selection is a permutation of the two selections. -/
theorem sel2_perm (g₁ : Expr) (m₁ : List Expr) (g₂ : Expr) (m₂ : List Expr) :
    (sel2 tr t pub g₁ m₁ g₂ m₂).Perm
      (selL tr t pub g₁ m₁ (List.range (tr.height t)) ++ selL tr t pub g₂ m₂ (List.range (tr.height t))) := by
  unfold sel2
  refine (flatMap_append_perm _ _ _).trans ?_
  have e : ∀ (g : Expr) (m : List Expr) (rs : List Nat),
      (rs.flatMap fun r => if g.eval tr t r pub = 1 then [vals tr t r pub m] else []) = selL tr t pub g m rs := by
    intro g m rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.flatMap_cons, selL, List.filterMap_cons] at ih ⊢
      split <;> simp [ih]
  rw [e, e]

theorem tbl_one (is : List Interaction) (g : Expr) (msg : List Expr) (b : Nat) (s : Bool)
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = [{ bus := b, mult := [g], msg, send := s }]) :
    tableBusList is tr t pub b s = selL tr t pub g msg (List.range (tr.height t)) := by
  rw [tableBusList_one is g msg tr t pub b s h]; rfl

end Sel

/-! ## The working-set interactions, pinned -/

def wsnRS : List Expr := 0 :: Wsn.vec "o" 18
def wsnRR : List Expr := Wsn.c "nw" :: Wsn.vec "o" 18
def wsaWR : List Expr :=
  [Wsa.c "seg"] ++ Wsa.vec "kd" 16 ++ [Wsa.c "cp", Wsa.c "cl"] ++ Wsa.vec "cv" 16 ++ [Wsa.c "wr", Wsa.c "idp"]
def wsaWS : List Expr :=
  [Wsa.c "seg"] ++ Wsa.vec "kd" 16 ++ [Wsa.c "ncp", Wsa.c "ncl"] ++ Wsa.vec "ncv" 16 ++ [1, Wsa.c "t"]
def wslPT : List Expr := [Wsl.c "seg", 0, Wsl.c "i"] ++ Wsl.vec "dgO" 18 ++ Wsl.vec "dgN" 18
def wslWS : List Expr :=
  [Wsl.c "seg"] ++ Wsl.vec "kd" 16 ++ [Wsl.c "cp", Wsl.c "cl"] ++ Wsl.vec "cv" 16 ++ [Wsl.c "wr", 0]
def wslWR : List Expr :=
  [Wsl.c "seg"] ++ Wsl.vec "kd" 16 ++ [Wsl.c "ncp", Wsl.c "ncl"] ++ Wsl.vec "ncv" 16 ++ [Wsl.c "nwr", Wsl.c "idl"]
def wspL : List Expr := [Wsp.c "seg", Wsp.c "lvl", sm 2 (Wsp.c "idx")] ++ Wsp.vec "lo" 18 ++ Wsp.vec "ln" 18
def wspR : List Expr := [Wsp.c "seg", Wsp.c "lvl", sm 2 (Wsp.c "idx") + 1] ++ Wsp.vec "ro" 18 ++ Wsp.vec "rn" 18
def wspO : List Expr := [Wsp.c "seg", Wsp.c "lvl" + 1, Wsp.c "idx"] ++ Wsp.vec "oo" 18 ++ Wsp.vec "on" 18
def wspRR : List Expr := Wsp.c "seg" :: Wsp.vec "oo" 18
def wspRS : List Expr := (Wsp.c "seg" + 1) :: Wsp.vec "on" 18

def fl (is : List Interaction) (b : Nat) (s : Bool) : List Interaction :=
  is.filter fun i => decide (i.bus = b ∧ i.send = s)

theorem wsn_rs : fl Wsn.interactions B_RCH true = [snd B_RCH (Wsn.c "top" * (1 - Wsn.c "ph")) wsnRS] := by rfl
theorem wsn_rr : fl Wsn.interactions B_RCH false = [rcv B_RCH (Wsn.c "top" * Wsn.c "ph") wsnRR] := by rfl
theorem wsa_wr : fl Wsa.interactions B_WM false = [rcv B_WM (Wsa.c "act") wsaWR] := by rfl
theorem wsa_ws : fl Wsa.interactions B_WM true = [snd B_WM (Wsa.c "act") wsaWS] := by rfl
theorem wsl_pts : fl Wsl.interactions B_PT true = [snd B_PT (Wsl.c "act") wslPT] := by rfl
theorem wsl_ptr : fl Wsl.interactions B_PT false = [] := by rfl
theorem wsl_ws : fl Wsl.interactions B_WM true = [snd B_WM (Wsl.c "act") wslWS] := by rfl
theorem wsl_wr : fl Wsl.interactions B_WM false = [rcv B_WM (Wsl.c "act") wslWR] := by rfl
theorem wsp_ptr : fl Wsp.interactions B_PT false = [rcv B_PT (Wsp.c "tl") wspL, rcv B_PT (Wsp.c "tr") wspR] := by rfl
theorem wsp_pts : fl Wsp.interactions B_PT true = [snd B_PT (Wsp.c "act" - Wsp.c "top") wspO] := by rfl
theorem wsp_rr : fl Wsp.interactions B_RCH false = [rcv B_RCH (Wsp.c "top") wspRR] := by rfl
theorem wsp_rs : fl Wsp.interactions B_RCH true = [snd B_RCH (Wsp.c "top") wspRS] := by rfl
theorem wsn_wm (s : Bool) : fl Wsn.interactions B_WM s = [] := by cases s <;> rfl
theorem wsn_pt (s : Bool) : fl Wsn.interactions B_PT s = [] := by cases s <;> rfl
theorem wsa_pt (s : Bool) : fl Wsa.interactions B_PT s = [] := by cases s <;> rfl
theorem wsa_rch (s : Bool) : fl Wsa.interactions B_RCH s = [] := by cases s <;> rfl
theorem wsl_rch (s : Bool) : fl Wsl.interactions B_RCH s = [] := by cases s <;> rfl
theorem wsp_wm (s : Bool) : fl Wsp.interactions B_WM s = [] := by cases s <;> rfl

/-- The working-set buses. -/
def WsBusN (b : Nat) : Prop := b = B_WM ∨ b = B_PT ∨ b = B_RCH

theorem nb_ws (b : Nat) (hb : WsBusN b) :
    noBus shaTable.interactions b = true ∧ noBus Key.table.interactions b = true ∧
    noBus Br.table.interactions b = true ∧ noBus Sn.table.interactions b = true ∧
    noBus Kcmp.table.interactions b = true ∧ noBus Wsb.interactions b = true ∧
    noBus Snc.table.interactions b = true ∧ noBus Rng.table.interactions b = true := by
  rcases hb with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The working-set buses' lists**: only `WSN` (6), `WSA` (7), `WSL` (10), `WSP` (11). -/
theorem busList_ws {tr : Trace Fp} {pub : List Fp} (D : Nat) (extra : List Table) (nb np : Nat)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH)
    (b : Nat) (s : Bool) (hb : WsBusN b) :
    busList (fullAir D extra nb np) tr pub b s =
      tableBusList Wsn.interactions tr 6 pub b s ++ tableBusList Wsa.interactions tr 7 pub b s ++
        tableBusList Wsl.interactions tr 10 pub b s ++ tableBusList Wsp.interactions tr 11 pub b s := by
  have ext := busList_extend (m5aAir D) extra nb np tr pub b s (fun T hT i hi ⟨e, _⟩ => by
    obtain ⟨h1, h2, h3⟩ := hx T hT i hi
    rcases hb with rfl | rfl | rfl <;> simp_all)
  simp only [fullAir]
  rw [ext]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := nb_ws b hb
  simp only [busList, m5aAir, busList.go]
  rw [tbl_nil n1, tbl_nil n2, tbl_nil (is := Br.table.interactions) n3, tbl_nil (is := Sn.table.interactions) n4,
    tbl_nil n5, tbl_nil (is := (Wsb.table D).interactions) n6, tbl_nil n7, tbl_nil n8]
  simp only [Wsn.table, Wsa.table, Wsl.table, Wsp.table, List.nil_append, List.append_nil,
    List.append_assoc]

end StateM5a.WsDecode
