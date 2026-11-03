import StateM5a.DecodeM5a
import StateM5a.BusWalk
import StateM5a.BusSplit2

/-!
# StateM5a.DecodeShape — `Traffic.WalkShape` of the decoded rows, and the AIR-level assembly

* **`walk_rootUniq`** (from `Holds`, no premise beyond `D ≤ 30`): one decoded `WSB` root per walk
  id.  A row is an INTAKE root (`g0 = (1 − ph)·real = 1`, so `ph = 0`, walk id `i = r`) or a FINAL
  root (`gw = ph·wr = 1`, so `ph = 1`, walk id `2^20 + i` with `i + 2^D = r`), never both
  (`FieldWsb.wsb_index`); heights are `≤ 2^20`, so the two kinds' ids are disjoint and no id wraps.
* **`walk_deeper`**: a decoded row's child `DOWN` is in the same walk and strictly deeper — `BR`:
  depth `d + 1`; `SN`: `d + klen` with `1 ≤ klen ≤ 64` (`FieldWalk2.sn_gdn_klen`).  Premises (open
  at field level): the depth of a descending row is `< P − 64` (from the `NIB` lookup at depth `d`
  against the `KEY` table, whose indices are `< 2^21`), and a descending `SN` row has a short key
  (`cont = 0`; a continued head's `klen = Σ a + rl` needs the `SNC` chain bound on `rl`).
* **`air_batched_changes`**: `bus_batched_changes` with its `DOWN`/`UP` permutations and its walk
  shape discharged from `Holds` of the AIR the prover runs (`walk_traffic`, `walk_rootUniq`,
  `walk_deeper`), for any decoder.  What remains a premise: the depth bounds above, every decoded
  row's `LocalOK` (the per-row facts), the `TCH` chain (public tape) and the writing roots' link to
  the committed changes.  `Sem` covers every walk op, the extension split `oEX` included
  (`UChain.extSplit`, `BusSplit2.localOK_extSplit`); `air_batched_changesS` is the same theorem
  on the alias `SemS` (`BusSplit2.localOK_semS_iff`).
-/

namespace StateM5a.DecodeShape

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Message heads -/

theorem br_di_head : brW.di.take 2 = [Br.c "w", Br.c "d"] := by simp [brW]; filt
theorem br_dd_head : brW.dd.take 2 = [Br.c "w", Br.c "d" + 1] := by simp [brW]; filt
theorem sn_di_head : snW.di.take 2 = [Sn.c "w", Sn.c "d"] := by simp [snW]; filt
theorem sn_dd_head : snW.dd.take 2 = [Sn.c "w", Sn.c "d" + Sn.c "klen"] := by simp [snW]; filt
theorem wsb_d1_head : wsbR.d₁.take 1 = [Wsb.c "i"] := by simp [wsbR]; filt
theorem wsb_d2_head : wsbR.d₂.take 1 = [K W_FINAL + Wsb.c "i"] := by simp [wsbR]; filt

theorem vals_getD {tr : Trace Fp} {t r : Nat} {pub : List Fp} {l : List Expr} {n : Nat} {es : List Expr}
    (h : l.take n = es) (i : Nat) (hi : i < n) (e : Expr) (he : es[i]? = some e) :
    (vals tr t r pub l).getD i 0 = e.eval tr t r pub := by
  have : l[i]? = some e := by rw [← List.getElem?_take_of_lt hi, h, he]
  simp [vals, List.getD_eq_getElem?_getD, List.getElem?_map, this]

/-! ## One root per walk id -/

theorem countP_flatMap_le_one {β : Type} (f : Nat → List β) (p : β → Bool) :
    ∀ (l : List Nat), (∀ r ∈ l, (f r).countP p ≤ 1) → l.Nodup →
      (∀ r ∈ l, ∀ r' ∈ l, ∀ x ∈ f r, ∀ y ∈ f r', p x → p y → r = r') →
      (l.flatMap f).countP p ≤ 1
  | [], _, _, _ => by simp
  | a :: l, hf, hnd, hinj => by
    rw [List.flatMap_cons, List.countP_append]
    have ih := countP_flatMap_le_one f p l (fun r hr => hf r (List.mem_cons_of_mem _ hr))
      (List.nodup_cons.1 hnd).2
      (fun r hr r' hr' => hinj r (List.mem_cons_of_mem _ hr) r' (List.mem_cons_of_mem _ hr'))
    have ha := hf a (List.mem_cons_self ..)
    rcases Nat.lt_or_ge ((f a).countP p) 1 with h0 | h1
    · omega
    · obtain ⟨x, hx, px⟩ := List.countP_pos_iff.1 (by omega : 0 < (f a).countP p)
      have : (l.flatMap f).countP p = 0 := by
        rw [List.countP_eq_zero]
        intro y hy py
        obtain ⟨r', hr', hy'⟩ := List.mem_flatMap.1 hy
        have := hinj a (List.mem_cons_self ..) r' (List.mem_cons_of_mem _ hr') x hx y hy' px py
        subst this
        exact (List.nodup_cons.1 hnd).1 hr'
      omega

section
variable {tr : Trace Fp} {pub : List Fp}

theorem ev_mul_one {a b : Expr} {t r : Nat} (h : ev tr t r pub (a * b) = 1) :
    ev tr t r pub a ≠ 0 ∧ ev tr t r pub b ≠ 0 := by
  rw [ev_hmul] at h
  constructor <;> intro h0 <;> rw [h0] at h <;> simp at h

theorem g1_ph {r D : Nat} (hc : ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0)
    (h : wsbR.g₁.eval tr 5 r pub = 1) : ev tr 5 r pub (Wsb.c "ph") = 0 := by
  have h1 := (ev_mul_one (eval_one_ev h)).1
  rcases ev_bool (hold rfl hc (FieldWsb.m_bool "ph" (by simp))) with h0 | h0
  · exact h0
  · exact absurd (FieldWsb.ev_one_sub1 h0) h1

theorem g2_ph {r D : Nat} (hc : ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0)
    (h : wsbR.g₂.eval tr 5 r pub = 1) : ev tr 5 r pub (Wsb.c "ph") = 1 := by
  have h1 := (ev_mul_one (eval_one_ev h)).1
  rcases ev_bool (hold rfl hc (FieldWsb.m_bool "ph" (by simp))) with h0 | h0
  · exact absurd h0 h1
  · exact h0

/-- The walk id of a decoded root, by kind. -/
theorem root_w {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) {D r : Nat} (hlog : tr.log 5 ≤ 20)
    (hc : ∀ r, r < tr.height 5 → ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0)
    (hD : D ≤ 30) (hr : r < tr.height 5) (q : Root Ref Pay Res) (hq : q ∈ rootRow Dc wsbR tr 5 pub r) :
    (q.dn.w = r ∧ r < 2 ^ 20) ∨ (2 ^ 20 ≤ q.dn.w ∧ ∃ i, q.dn.w = 2 ^ 20 + i ∧ i + 2 ^ D = r) := by
  have hH : tr.height 5 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hidx := FieldWsb.wsb_index hc hlog hD r hr
  simp only [rootRow, List.mem_append] at hq
  rcases hq with hq | hq
  · split at hq
    · rename_i hg
      simp only [List.mem_singleton] at hq; subst hq
      have hp := g1_ph (hc r hr) hg
      left
      simp only [Dec.down]
      rw [vals_getD wsb_d1_head 0 (by decide) _ rfl]
      change ev tr 5 r pub (Wsb.c "i") = r ∧ _
      rcases hidx with ⟨_, hi⟩ | ⟨h1, _⟩
      · exact ⟨hi, by omega⟩
      · omega
    · simp at hq
  · split at hq
    · rename_i hg
      simp only [List.mem_singleton] at hq; subst hq
      have hp := g2_ph (hc r hr) hg
      right
      simp only [Dec.down]
      rw [vals_getD wsb_d2_head 0 (by decide) _ rfl]
      change ev tr 5 r pub (K W_FINAL + Wsb.c "i") ≥ _ ∧ ∃ i, ev tr 5 r pub (K W_FINAL + Wsb.c "i") = _ ∧ _
      rcases hidx with ⟨h1, _⟩ | ⟨_, hi⟩
      · omega
      · have := Nat.one_le_two_pow (n := D)
        have e : ev tr 5 r pub (K W_FINAL + Wsb.c "i") = 2 ^ 20 + ev tr 5 r pub (Wsb.c "i") := by
          rw [ev_hadd, show K W_FINAL = Expr.const (2 ^ 20) from rfl, ev_const]
          rw [Nat.mod_eq_of_lt (by decide : 2 ^ 20 < P), Nat.mod_eq_of_lt (by omega)]
        rw [e]
        exact ⟨by omega, _, rfl, hi⟩
    · simp at hq

/-- **One decoded `WSB` root per walk id.** -/
theorem walk_rootUniq {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table)
    (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30) (w : Nat) :
    (walkRoots Dc tr pub).countP (fun q => decide (q.dn.w = w)) ≤ 1 := by
  have h5 : 5 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hlog : tr.log 5 ≤ 20 := (hH.logBound 5 h5).2
  have hc : ∀ r, r < tr.height 5 → ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0 :=
    fun r hr => hH.constr 5 h5 r hr
  refine countP_flatMap_le_one _ _ _ ?_ List.nodup_range ?_
  · intro r hr
    have hr0 := List.mem_range.1 hr
    simp only [rootRow, List.countP_append]
    by_cases h1 : wsbR.g₁.eval tr 5 r pub = 1 <;> by_cases h2 : wsbR.g₂.eval tr 5 r pub = 1
    · have := g1_ph (hc r hr0) h1; have := g2_ph (hc r hr0) h2; omega
    · simp only [h1, h2, ↓reduceIte, List.countP_cons, List.countP_nil]; split <;> simp
    · simp only [h1, h2, ↓reduceIte, List.countP_cons, List.countP_nil]; split <;> simp
    · simp [h1, h2]
  · intro r hr r' hr' x hx y hy px py
    have hr0 := List.mem_range.1 hr; have hr0' := List.mem_range.1 hr'
    have ex := root_w Dc hlog hc hD hr0 x hx
    have ey := root_w Dc hlog hc hD hr0' y hy
    simp only [decide_eq_true_eq] at px py
    rcases ex with ⟨a, b⟩ | ⟨a, i, b, c⟩ <;> rcases ey with ⟨a', b'⟩ | ⟨a', i', b', c'⟩ <;> omega

/-! ## Strictly deeper children -/

theorem mem_rowsOf {Ref Pay Res : Type} {Dc : Dec Ref Pay Res} {W : WalkIx} {t : Nat} {x : WRow Ref Pay Res}
    (hx : x ∈ rowsOf Dc W tr t pub) : ∃ r, r < tr.height t ∧ W.g.eval tr t r pub = 1 ∧
      x = { din := Dc.down (vals tr t r pub W.di),
            dout := if W.gdn.eval tr t r pub = 1 then some (Dc.down (vals tr t r pub W.dd)) else none,
            uin := Dc.dr ((vals tr t r pub W.ui).drop 2),
            uout := Dc.dr ((vals tr t r pub W.uo).drop 2) } := by
  obtain ⟨r, hr, hx⟩ := List.mem_filterMap.1 hx
  split at hx
  · exact ⟨r, List.mem_range.1 hr, by assumption, (Option.some.inj hx).symm⟩
  · simp at hx

/-- **Children are in the same walk and strictly deeper.**  Premises: a descending row's depth is
small (`d + 64 < P`), and a descending `SN` row has a short key (`cont = 0`). -/
theorem walk_deeper {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table)
    (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hbr : ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P)
    (hsn : ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 →
      ev tr 3 r pub (Sn.c "cont") = 0 ∧ ev tr 3 r pub (Sn.c "d") + 64 < P) :
    ∀ x ∈ walkRows Dc tr pub, ∀ c, x.dout = some c → c.w = x.din.w ∧ x.din.d < c.d := by
  intro x hx c hc
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨r, hr, -, rfl⟩ := mem_rowsOf hx
    simp only at hc
    split at hc
    · rename_i hg
      obtain rfl := Option.some.inj hc
      simp only [Dec.down]
      rw [vals_getD br_dd_head 0 (by decide) _ rfl, vals_getD br_di_head 0 (by decide) _ rfl,
        vals_getD br_dd_head 1 (by decide) _ rfl, vals_getD br_di_head 1 (by decide) _ rfl]
      refine ⟨rfl, ?_⟩
      change ev tr 2 r pub (Br.c "d") < ev tr 2 r pub (Br.c "d" + 1)
      have := hbr r hr hg
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt this]
      omega
    · simp at hc
  · obtain ⟨r, hr, -, rfl⟩ := mem_rowsOf hx
    simp only at hc
    split at hc
    · rename_i hg
      obtain rfl := Option.some.inj hc
      simp only [Dec.down]
      rw [vals_getD sn_dd_head 0 (by decide) _ rfl, vals_getD sn_di_head 0 (by decide) _ rfl,
        vals_getD sn_dd_head 1 (by decide) _ rfl, vals_getD sn_di_head 1 (by decide) _ rfl]
      refine ⟨rfl, ?_⟩
      change ev tr 3 r pub (Sn.c "d") < ev tr 3 r pub (Sn.c "d" + Sn.c "klen")
      obtain ⟨hcont, hd⟩ := hsn r hr hg
      have hc3 := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
      obtain ⟨h1, h2⟩ := FieldWalk2.sn_gdn_klen hc3 (eval_one_ev hg) hcont
      rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
      omega
    · simp at hc

/-- **The walk shape of the decoded rows, from `Holds`** (with the depth premises). -/
theorem walk_shape {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table)
    (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hbr : ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P)
    (hsn : ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 →
      ev tr 3 r pub (Sn.c "cont") = 0 ∧ ev tr 3 r pub (Sn.c "d") + 64 < P) :
    WalkShape (walkRoots Dc tr pub) (walkRows Dc tr pub) :=
  ⟨walk_deeper Dc D extra nb np hH hbr hsn, walk_rootUniq Dc D extra nb np hH hD⟩

/-! ## The AIR-level assembly -/

open StateM5a.Store StateM5a.BusWalk NearSpec NearSpecV3.D2 in
/-- **Batched FINAL from `Holds` of the AIR the prover runs.**  `bus_batched_changes` with its
`DOWN` / `UP` permutations (`walk_traffic`) and walk shape (`walk_shape`) discharged, for any
field decoder `Dc` of the walk messages into refs / payloads / results.  Premises still open at
field level: the depth bounds (`hbr`, `hsn`), every decoded row's local step (`hloc`: the per-row
facts of the `step_*` lemmas), the `TCH` chain against the public tape (`hT`) and the writing roots
as the roots of the committed changes (`hroot`). -/
theorem air_batched_changes (hCR : Walk.Sha256CR) (σ : Store) (keyOf : Nat → List Nat)
    (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hbr : ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P)
    (hsn : ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 →
      ev tr 3 r pub (Sn.c "cont") = 0 ∧ ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (Sem σ keyOf) r)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ walkRoots Dc tr pub, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post := by
  obtain ⟨hDn, hUp⟩ := walk_traffic Dc D extra nb np hH hx
  exact bus_batched_changes hCR σ keyOf (walk_shape Dc D extra nb np hH hD hbr hsn) hDn hUp hloc cs prev
    post N a b hT hroot T hT0 hF

open StateM5a.Store StateM5a.BusWalk NearSpec NearSpecV3.D2 in
/-- **The same on the alias `SemS`** (`BusSplit2`: `SemS = Sem`, `localOK_semS_iff`), kept for code
written against it; a corollary of `air_batched_changes`. -/
theorem air_batched_changesS (hCR : Walk.Sha256CR) (σ : Store) (keyOf : Nat → List Nat)
    (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hbr : ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") + 1 < P)
    (hsn : ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 →
      ev tr 3 r pub (Sn.c "cont") = 0 ∧ ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (SemS σ keyOf) r)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ walkRoots Dc tr pub, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post :=
  air_batched_changes hCR σ keyOf Dc D extra nb np hH hD hx hbr hsn
    (fun r hr => localOK_semS_iff.1 (hloc r hr)) cs prev post N a b hT hroot T hT0 hF

end

end StateM5a.DecodeShape
