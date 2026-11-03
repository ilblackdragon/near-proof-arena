import StateM5a.IntakeKeys

/-!
# StateM5a.FinalOrder — the writing roots are in the spec's key order; `sortKV committed = cs`

* **`final_key`**: a real FINAL `WSB` row `2^D + i` has the same key bytes as the INTAKE row `i`
  (`WsEntries.ws_entries`: same `kd` limbs; `KeyDigest.wsb_kd`: `kd = pairs (sha256 key)`;
  `Sha256CR`).
* **`wr_sorted`**: the writing rows (`ph·wr = 1`, `Tape.wrRows`, the walk roots of the committed
  changes, in `TCH` order) are real FINAL rows `2^D + i` with `i` increasing, so their keys are
  strictly increasing (`IntakeKeys.wsb_sorted`).
* **`fc_sorted`**: hence a `cs` matching the writing rows (`Tape.FinalChanges`) is strictly sorted
  by `bytesLt` on keys.
* **`sortKV_of_perm`** (spec side, generic): `sortKV l = cs` for any `l ~ cs` with `cs` strictly
  sorted (insertion sort of distinct keys).
* **`air_final_sorted`**: `applyChanges (some T) (sortKV committed)` — the spec's `Ovl.finalize`
  order — succeeds with root `post`, for any `committed ~ cs`.

What remains for `FinalChanges` itself: that `committed`, the spec's committed overlay, is (as a
list) a permutation of the writing rows' changes `(keyBytes kid_k, value with (cp, cl, cv))`.
`ws_entries` gives each writing row's `(cp, cl, cv)` as the latest write of its key on the `WRITE`
tape (closing value of the last touching segment, `WsCost.lastVal`); the overlay ↔ tape link and
the value preimages (`cv = sha256 value`) are outside this AIR (M5b / the statement).
-/

namespace StateM5a.FinalOrder

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.KeyDecode
open StateM5a.Tape StateM5a.KcChain StateM5a.KeyDigest StateM5a.KeyOrder StateM5a.IntakeKeys
open NearSpec NearSpecV3.D2

set_option maxRecDepth 100000

/-! ## Insertion sort of distinct keys (spec side) -/

theorem bytesLt_total : ∀ a b : Bytes, a ≠ b → bytesLt a b = true ∨ bytesLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => .inl rfl
  | _ :: _, [], _ => .inr rfl
  | x :: xs, y :: ys, h => by
    simp only [bytesLt]
    by_cases a1 : x.toNat < y.toNat
    · simp [a1]
    by_cases a2 : y.toNat < x.toNat
    · simp [a1, a2]
    have e : x = y := UInt8.toNat_inj.1 (by omega)
    subst e
    simp only [a1, if_false]
    exact bytesLt_total xs ys (fun h' => h (by rw [h']))

abbrev KR (p q : Bytes × Option Bytes) : Prop := bytesLt p.1 q.1 = true

theorem insertSorted_perm (p : Bytes × Option Bytes) :
    ∀ l : List (Bytes × Option Bytes), (insertSorted p l).Perm (p :: l)
  | [] => .refl _
  | q :: qs => by
    simp only [insertSorted]
    split
    · exact .refl _
    · exact ((insertSorted_perm p qs).cons q).trans (.swap p q qs)

theorem insertSorted_sorted (p : Bytes × Option Bytes) :
    ∀ l : List (Bytes × Option Bytes), l.Pairwise KR → (∀ q ∈ l, q.1 ≠ p.1) →
      (insertSorted p l).Pairwise KR
  | [], _, _ => by simp [insertSorted]
  | q :: qs, hs, hd => by
    simp only [insertSorted]
    split
    · rename_i h
      refine List.Pairwise.cons (fun x hx => ?_) hs
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact bytesLt_trans _ _ _ h (List.rel_of_pairwise_cons hs hx)
    · rename_i h
      have hqp : KR q p := by
        rcases bytesLt_total p.1 q.1 (fun e => hd q (List.mem_cons_self ..) e.symm) with h' | h'
        · exact absurd h' h
        · exact h'
      refine List.Pairwise.cons (fun x hx => ?_)
        (insertSorted_sorted p qs (List.Pairwise.of_cons hs) (fun x hx => hd x (List.mem_cons_of_mem _ hx)))
      have := (insertSorted_perm p qs).mem_iff.1 hx
      rcases List.mem_cons.1 this with rfl | hx'
      · exact hqp
      · exact List.rel_of_pairwise_cons hs hx'

theorem foldl_sort : ∀ (l acc : List (Bytes × Option Bytes)), acc.Pairwise KR →
    (acc ++ l).Pairwise (fun p q => p.1 ≠ q.1) →
    (l.foldl (fun acc p => insertSorted p acc) acc).Pairwise KR ∧
      (l.foldl (fun acc p => insertSorted p acc) acc).Perm (acc ++ l)
  | [], acc, hs, _ => by simpa using hs
  | p :: ps, acc, hs, hd => by
    simp only [List.foldl_cons]
    have hpd : ∀ q ∈ acc, q.1 ≠ p.1 := fun q hq =>
      List.pairwise_append.1 hd |>.2.2 q hq p (List.mem_cons_self ..)
    have hs' := insertSorted_sorted p acc hs hpd
    have hd' : (insertSorted p acc ++ ps).Pairwise (fun p q => p.1 ≠ q.1) := by
      have hperm : (insertSorted p acc ++ ps).Perm (acc ++ p :: ps) :=
        ((insertSorted_perm p acc).append_right ps).trans (by simp [List.perm_middle.symm])
      refine (hperm.pairwise_iff ?_).2 hd
      intro a b h e; exact h e.symm
    obtain ⟨h1, h2⟩ := foldl_sort ps (insertSorted p acc) hs' hd'
    refine ⟨h1, h2.trans ?_⟩
    exact ((insertSorted_perm p acc).append_right ps).trans (by simp [List.perm_middle.symm])

theorem sorted_perm_eq : ∀ {a b : List (Bytes × Option Bytes)}, a.Pairwise KR → b.Pairwise KR →
    a.Perm b → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h.length_eq (by simp)
  | _ :: _, [], _, _, h => absurd h.length_eq (by simp)
  | x :: xs, y :: ys, ha, hb, h => by
    by_cases e : x = y
    · subst e
      rw [sorted_perm_eq (List.Pairwise.of_cons ha) (List.Pairwise.of_cons hb) (h.cons_inv)]
    · have hx : x ∈ ys := by
        have := h.mem_iff.1 (List.mem_cons_self ..)
        rcases List.mem_cons.1 this with h' | h'
        · exact absurd h' e
        · exact h'
      have hy : y ∈ xs := by
        have := h.mem_iff.2 (List.mem_cons_self ..)
        rcases List.mem_cons.1 this with h' | h'
        · exact absurd h'.symm e
        · exact h'
      have h1 := List.rel_of_pairwise_cons ha hy
      have h2 := List.rel_of_pairwise_cons hb hx
      have := bytesLt_trans _ _ _ h1 h2
      rw [bytesLt_irrefl] at this
      exact absurd this (by decide)

/-- **`sortKV` of any permutation of a strictly key-sorted list is that list.** -/
theorem sortKV_of_perm {cs l : List (Bytes × Option Bytes)} (hs : cs.Pairwise KR) (hp : l.Perm cs) :
    sortKV l = cs := by
  have hd : l.Pairwise (fun p q => p.1 ≠ q.1) := by
    refine (hp.pairwise_iff ?_).2 (hs.imp fun {a b} h e => ?_)
    · intro a b h e; exact h e.symm
    · have h' : bytesLt a.1 b.1 = true := h
      rw [e, bytesLt_irrefl] at h'; exact absurd h' (by decide)
  obtain ⟨h1, h2⟩ := foldl_sort l [] List.Pairwise.nil (by simpa using hd)
  exact sorted_perm_eq h1 hs (h2.trans (by simpa using hp))

/-! ## The writing rows' keys -/

section
open StateM5a.Sha512If StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsDecode4
open StateM5a.WsKey StateM5a.WsLeafF StateM5a.WsBus StateM5a.WsCost

variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
  {compress : List Nat → List Nat → List Nat}

/-- All the premises of the working-set and key decoding. -/
structure Prem (tr : Trace Fp) (pub : List Fp) (D : Nat) (extra : List Table) (nb np : Nat)
    (compress : List Nat → List Nat → List Nat) : Prop where
  hH : Holds (fullAir D extra nb np) pub tr
  hx : ∀ T ∈ extra, ∀ i ∈ T.interactions,
    i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE
  hcomp : CompressOK compress
  hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf)
  hD1 : 1 ≤ D
  hD : D ≤ 20
  hNCR : NodeCR compress
  hLCR : LeafCR compress
  hCR : Walk.Sha256CR
  hsil : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KLEN = false ∧
    sendsOn T.interactions B_ORD = false ∧ sendsOn T.interactions B_SHA_BYTES = false ∧
    sendsOn T.interactions B_SHA_DIGEST = false ∧ sendsOn T.interactions B_KC = false ∧
    sendsOn T.interactions B_KDIG = false

theorem Prem.dist (h : Prem tr pub D extra nb np compress) :
    IntakeKeysDistinct compress (wsLeaves tr pub D 0) (WsLen.wsLen pub) :=
  intakeKeysDistinct h.hH (by have := h.hD; omega) h.hCR h.hLCR
    (fun T hT i hi => ⟨(h.hx T hT i hi).1, (h.hx T hT i hi).2.1, (h.hx T hT i hi).2.2.1,
      (h.hx T hT i hi).2.2.2.1⟩) h.hcomp h.hC
    (fun T hT => (h.hsil T hT).1) (fun T hT => (h.hsil T hT).2.1) (fun T hT => (h.hsil T hT).2.2.1)
    (fun T hT => (h.hsil T hT).2.2.2.1) (fun T hT => (h.hsil T hT).2.2.2.2.1)
    (fun T hT => (h.hsil T hT).2.2.2.2.2.1) (fun T hT => (h.hsil T hT).2.2.2.2.2.2)

theorem Prem.kdr (h : Prem tr pub D extra nb np compress) : WsbKdRange tr pub :=
  wsbKdRange h.hH (fun T hT => (h.hsil T hT).2.2.2.1) (fun T hT => (h.hsil T hT).2.2.2.2.1)
    (fun T hT => (h.hsil T hT).2.2.2.2.2.1) (fun T hT => (h.hsil T hT).2.2.2.2.2.2)

/-- The `WSB` height is `2^(D+1)`. -/
theorem wsb_height (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30) : tr.height 5 = 2 ^ (D + 1) := by
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  have h0 : 0 < tr.height 5 := Nat.two_pow_pos _
  obtain ⟨he, hp⟩ := WsLen.wsb_last (D := D) hc
  have hi := eq_of_sub (FieldWsb.wsb_gate he (hold rfl (hc _ (by omega)) (m_e D)))
  rw [show K (2 ^ D - 1) = Expr.const (2 ^ D - 1) from rfl, ev_const] at hi
  have : 2 ^ D ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD
  have := Nat.one_le_two_pow (n := D)
  rw [Nat.mod_eq_of_lt (by omega)] at hi
  rcases FieldWsb.wsb_index hc hlog hD (tr.height 5 - 1) (by omega) with ⟨a, _⟩ | ⟨_, b⟩
  · omega
  · rw [Nat.pow_succ]; omega

/-- A phase-0 `WSB` row is one of the first `2^D`. -/
theorem ph0_lt (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30) :
    ∀ k r, r + k + 1 = tr.height 5 → r < tr.height 5 → ev tr 5 r pub (Wsb.c "ph") = 0 → r < 2 ^ D := by
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  have hH20 : tr.height 5 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  intro k
  induction k with
  | zero =>
    intro r hk hr hp
    have := (WsLen.wsb_last (D := D) hc).2
    rw [show tr.height 5 - 1 = r by omega, hp] at this
    exact absurd this (by decide)
  | succ k ih =>
    intro r hk hr hp
    have hr1 : r + 1 < tr.height 5 := by omega
    have hidx := FieldWsb.wsb_index hc hlog hD r hr
    have hiP : ev tr 5 r pub (Wsb.c "i") + 1 < 2013265921 := by
      rcases hidx with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    obtain ⟨-, -, sp⟩ := FieldWsb.wsb_step hc hr1 hiP
    rcases FieldRows2.ev_bool (hold rfl (hc r hr) (FieldWsb.m_bool "e" (by simp))) with he | he
    · rw [hp, he] at sp
      have := ih (r + 1) (by omega) hr1 sp; omega
    · have hi := eq_of_sub (FieldWsb.wsb_gate he (hold rfl (hc r hr) (m_e D)))
      rw [show K (2 ^ D - 1) = Expr.const (2 ^ D - 1) from rfl, ev_const] at hi
      have : 2 ^ D ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD
      have := Nat.one_le_two_pow (n := D)
      rw [Nat.mod_eq_of_lt (by omega)] at hi
      rcases hidx with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · rw [hp] at h; exact absurd h (by decide)

/-- **A real FINAL row has its INTAKE row's key.** -/
theorem final_key (h : Prem tr pub D extra nb np compress) {i : Nat} (hi : i < WsLen.wsLen pub) :
    wkey tr pub (2 ^ D + i) = wkey tr pub i := by
  have hH := h.hH
  have hD30 : D ≤ 30 := by have := h.hD; omega
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  have hWl := WsLen.wsb_wsLen_le hc hlog hD30
  have hht := wsb_height hH hD30
  have hkd := ((WsEntries.ws_entries hH h.hx h.hcomp h.hC h.hD1 h.hD h.hNCR h.hLCR
    h.dist h.kdr).2.1 i hi).2.1
  have hr1 : 2 ^ D + i < tr.height 5 := by rw [hht, Nat.pow_succ]; omega
  obtain ⟨hi5, -, -, ri⟩ := phase0 hH hD30 hi
  have hR1 : ev tr 5 (2 ^ D + i) pub (Wsb.c "real") = 1 := by
    rcases FieldWsb.wsb_index hc hlog hD30 _ hr1 with ⟨a, b⟩ | ⟨_, b⟩
    · have := ph0_lt hH hD30 (tr.height 5 - (2 ^ D + i) - 1) _ (by omega) hr1 a; omega
    · exact (WsLen.wsb_real_iff hc hlog hD30 hr1).2.2 (by omega)
  have s := h.hsil
  have k1 := wsb_kd hH (fun T hT => (s T hT).2.2.2.1) (fun T hT => (s T hT).2.2.2.2.1)
    (fun T hT => (s T hT).2.2.2.2.2.1) (fun T hT => (s T hT).2.2.2.2.2.2) hr1 hR1
  have k0 := wsb_kd hH (fun T hT => (s T hT).2.2.2.1) (fun T hT => (s T hT).2.2.2.2.1)
    (fun T hT => (s T hT).2.2.2.2.2.1) (fun T hT => (s T hT).2.2.2.2.2.2) hi5 ri
  have e : pairs (sha256 (wkey tr pub (2 ^ D + i))) = pairs (sha256 (wkey tr pub i)) := by
    unfold wkey; rw [← k1, ← k0]; exact hkd
  have hs := congrArg limbBytes e
  rw [limbBytes_pairs _ (by rw [sha256_length]), limbBytes_pairs _ (by rw [sha256_length])] at hs
  exact h.hCR _ _ hs

/-- A writing row is the real FINAL row `2^D + i`. -/
theorem wr_row (h : Prem tr pub D extra nb np compress) {r : Nat} (hr : r ∈ wrRows tr pub) :
    ∃ i, r = 2 ^ D + i ∧ i < WsLen.wsLen pub := by
  have hH := h.hH
  have hD30 : D ≤ 30 := by have := h.hD; omega
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  obtain ⟨hr5, hg⟩ := List.mem_filter.1 hr
  have hr5 := List.mem_range.1 hr5
  have hg : gw.eval tr 5 r pub = 1 := of_decide_eq_true hg
  have hp := FieldRows2.ev_bool (hold rfl (hc r hr5) (m_bool_ph D))
  have hw := FieldRows2.ev_bool (hold rfl (hc r hr5) (m_bool_wr D))
  have hgv := eval_one_ev hg
  have e : ev tr 5 r pub gw = ev tr 5 r pub (Wsb.c "ph") * ev tr 5 r pub (Wsb.c "wr") % 2013265921 := ev_hmul _ _
  have hph : ev tr 5 r pub (Wsb.c "ph") = 1 := by
    rcases hp with hp | hp
    · rw [e, hp] at hgv; simp at hgv
    · exact hp
  have hwr : ev tr 5 r pub (Wsb.c "wr") = 1 := by
    rcases hw with hw | hw
    · rw [e, hw] at hgv; simp at hgv
    · exact hw
  have hreal : ev tr 5 r pub (Wsb.c "real") = 1 :=
    gate_of_one (hold rfl (hc r hr5) (by show _ ∈ Wsb.constraints D; unfold Wsb.constraints; simp)) hwr
  rcases FieldWsb.wsb_index hc hlog hD30 r hr5 with ⟨a, _⟩ | ⟨_, b⟩
  · omega
  · exact ⟨ev tr 5 r pub (Wsb.c "i"), by omega, (WsLen.wsb_real_iff hc hlog hD30 hr5).2.1 hreal⟩

theorem wrRows_lt {tr : Trace Fp} {pub : List Fp} : (wrRows tr pub).Pairwise (· < ·) := by
  unfold wrRows
  refine List.Pairwise.filter _ ?_
  rw [List.range_eq_range']
  exact List.pairwise_lt_range'

/-- **The writing rows' keys are strictly increasing.** -/
theorem wr_sorted (h : Prem tr pub D extra nb np compress) {k₁ k₂ : Nat} (hk : k₁ < k₂)
    (h₂ : k₂ < (wrRows tr pub).length) :
    bytesLt (wkey tr pub ((wrRows tr pub).getD k₁ 0)) (wkey tr pub ((wrRows tr pub).getD k₂ 0)) = true := by
  have hD30 : D ≤ 30 := by have := h.hD; omega
  have s := h.hsil
  have hk1 : k₁ < (wrRows tr pub).length := by omega
  have m : ∀ k (hk' : k < (wrRows tr pub).length), (wrRows tr pub).getD k 0 = (wrRows tr pub)[k]'hk' := by
    intro k hk'; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
  rw [m k₁ (by omega), m k₂ h₂]
  have hlt := List.pairwise_iff_getElem.1 wrRows_lt k₁ k₂ (by omega) h₂ hk
  obtain ⟨i₁, e₁, hi₁⟩ := wr_row h (List.getElem_mem (show k₁ < (wrRows tr pub).length by omega))
  obtain ⟨i₂, e₂, hi₂⟩ := wr_row h (List.getElem_mem h₂)
  rw [e₁, e₂, final_key h hi₁, final_key h hi₂]
  have := wsb_sorted h.hH hD30 (fun T hT => (s T hT).1) (fun T hT => (s T hT).2.1) (fun T hT => (s T hT).2.2.1)
    (i₂ - i₁ - 1) i₁ (by omega)
  rwa [show i₁ + (i₂ - i₁ - 1) + 1 = i₂ by omega] at this

/-- **A `cs` matching the writing rows is strictly key-sorted.** -/
theorem fc_sorted (h : Prem tr pub D extra nb np compress) {cs : List (Bytes × Option Bytes)}
    (hlen : cs.length = (wrRows tr pub).length) (hcs : FinalChanges tr pub cs) : cs.Pairwise KR := by
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  have ka := (hcs a ha (by omega)).1
  have kb := (hcs b hb (by omega)).1
  show bytesLt cs[a].1 cs[b].1 = true
  rw [ka, kb]
  exact wr_sorted h hab (by omega)

end

/-! ## The assembly in the spec's order -/

section
open StateM5a.Sha512If StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsDecode4
open StateM5a.WsKey StateM5a.WsLeafF StateM5a.Store StateM5a.BusWalk StateM5a.DecodeWalk StateM5a.Traffic

variable {tr : Trace Fp} {pub : List Fp}

/-- **Batched FINAL in the spec's order.**  With `rest` the extra tables after the tape, for any
`committed` that is a permutation of a list `cs` matching the writing rows (`FinalChanges`):
`applyChanges (some T) (sortKV committed)` succeeds with `rootHash = post`.  `Ovl.finalize`
applies exactly `sortKV committed`. -/
theorem air_final_sorted (σ : Store) (Dc : Dec Ref Pay Res) (hDc : StdDec Dc) (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (SemS σ (keyOf tr)) r)
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (committed : List (Bytes × Option Bytes)) (hcomm : committed.Perm cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV committed) = some (some T') ∧ rootHash (some T') = post := by
  have hD30 : D ≤ 30 := by have := hP.hD; omega
  -- the number of writing rows is `n` (the `TCH` chain)
  have hT := tch_perm writes prev post n rest hP.hH (fun T hT i hi => (hr T hT i hi).2.2) hn hprev hpost
  have hN := (Traffic.tch_chain hT).1
  have hs := fc_sorted hP (by rw [hlen, hN]) hcs
  rw [sortKV_of_perm hs hcomm]
  exact air_final' hP.hCR σ Dc hDc D writes prev post n rest nb np hP.hH hD30 hr hrN hn hprev hpost hloc cs
    hlen hcs T hT0 hF

end

end StateM5a.FinalOrder
