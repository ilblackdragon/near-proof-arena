import ZkFormal.NearV3.Sched.Link.ScanPubIdx
import ZkFormal.NearV3.Sched.Link.EntryLink

/-!
# Key records: `htau` and `hseed` from the public key records (`PubIdx`)

The process table receives its 16 key limbs `[τ, TAG_KEY, i, lo, hi, 0, 0]` on `SPUBB`, where
only public segments send (`recv_pub`). If the public `SPUBB` sends are `render`'s `pubb`
records (`PubIdx`), then each received limb is a key record of instance `τ < |Ps|`. So:
* `htau`: every active process row has `τ < |Ps|` (`tau_witness`: its τ is that of a key-block
  start);
* `hseed`: the instance's ChaCha key is `leWords` of its seed (32 bytes).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

namespace Proc
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

/-- `tau_step` with the key-block start in the increment case. -/
theorem tau_step' (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (ha : cv tr tp w act = 1) (hw1 : w + 1 < tr.height tp) (ha1 : cv tr tp (w + 1) act = 1) :
    cv tr tp (w + 1) tau = cv tr tp w tau ∨
      (cv tr tp (w + 1) kK = 1 ∧ cv tr tp (w + 1) kc = 0) := by
  have K0 := kinds hL hw
  have K1 := kinds hL hw1
  have tauR : tau ∈ roundCols := by simp [roundCols]
  have tauI : tau ∈ instCols := by simp [instCols]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K1.2.1 with k1 | k1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.1 with h0 | h0
    · exact Or.inl (inst_next hL hw (by omega) hw1 k1 tau tauI)
    · exact Or.inl ((round_next hL hw (Or.inl h0)).2.2 tau tauR)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.1 with h0 | h0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.1 with h1 | h1
      · have hE : cv tr tp w kE = 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.2.2.2.1 with hl | hl
        · have := (round_next hL hw (Or.inr ⟨hE, hl⟩)).2.1; omega
        · exact Or.inr ⟨k1, (blk_next hL hw (Or.inr hl) hw1 k1).1⟩
      · have := (round_next hL hw (Or.inl h1)).2.1; omega
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.1 with hl | hl
      · exact Or.inl (key_next hL hw h0 hl).2.2.2
      · exact Or.inr ⟨k1, (blk_next hL hw (Or.inl hl) hw1 k1).1⟩

/-- **Every active row's τ is that of a key-block start.** -/
theorem tau_witness (hL : PLocal tr tp pub) :
    ∀ w, w < tr.height tp → cv tr tp w act = 1 →
      ∃ f, f ≤ w ∧ cv tr tp f kK = 1 ∧ cv tr tp f kc = 0 ∧ cv tr tp f tau = cv tr tp w tau := by
  intro w
  induction w with
  | zero =>
    intro h0 ha
    have := row_first hL h0
    exact ⟨0, Nat.le_refl _, this.2.2 ha, this.1, rfl⟩
  | succ w ih =>
    intro hw1 ha1
    have ha : cv tr tp w act = 1 := act_prev hL hw1 ha1
    rcases tau_step' hL (by omega) ha hw1 ha1 with e | ⟨hk, hc⟩
    · obtain ⟨f, hf, h1, h2, h3⟩ := ih (by omega) ha
      exact ⟨f, by omega, h1, h2, h3.trans e.symm⟩
    · exact ⟨w + 1, Nat.le_refl _, hk, hc, rfl⟩

end Proc

variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- **A message received on a bus no table sends on is a public send.** -/
theorem recv_pub {AP : AirP} {pub : List F} {tr : Trace F} (hH : HoldsP AP pub tr) {b : Nat}
    (hnone : ∀ t, t < AP.tables.length → ∀ i ∈ AP.tables[t]!.interactions, i.bus = b → i.send = false)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus = b → seg.send = true)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = b) (hs : i.send = false)
    (hm : i.multNat tr t r pub ≠ 0) :
    pubCount AP pub b true (i.msgVal tr t r pub) ≠ 0 := by
  have hbal := hH.balance b (i.msgVal tr t r pub)
  rw [pubCount_zero (s := false) (fun seg h1 h2 => by rw [hpub seg h1 h2]; simp) _] at hbal
  have hrecv : busCount AP.toAir tr pub b false (i.msgVal tr t r pub) ≠ 0 := by
    have h1 := tableBusCount_pos hr hi hm
    rw [hb, hs] at h1
    have h2 := busCount_go_ge tr pub b false (i.msgVal tr t r pub) AP.tables 0 t ht
    simp only [Nat.zero_add] at h2
    unfold busCount; omega
  have hsend : busCount AP.toAir tr pub b true (i.msgVal tr t r pub) = 0 := by
    rcases Nat.eq_zero_or_pos (busCount AP.toAir tr pub b true (i.msgVal tr t r pub)) with h0 | h0
    · exact h0
    exfalso
    obtain ⟨t', ht', hc⟩ := busCount_go_pos tr pub b true _ AP.tables 0 (by unfold busCount at h0; exact Nat.pos_iff_ne_zero.1 h0)
    simp only [Nat.zero_add] at hc
    obtain ⟨r', -, i', hi', hb', hs', -, -⟩ := exists_of_tableBusCount hc
    rw [hnone t' ht' i' hi' hb'] at hs'; simp at hs'
  omega

/-! ## The key records -/

/-- The `pubb` records of one instance. -/
theorem render_pubb (Ps : List InstPub) (fwd : List (Nat × Nat)) :
    (render Ps fwd).pubb = (List.range Ps.length).flatMap (fun τ =>
      keyRecs τ (Ps.getD τ instD).seed ++ ashRecs τ (Ps.getD τ instD).ash) ++
      fwdRecs (Ps.getD 0 instD) fwd := rfl

/-- A key record received by the process table names instance `τ < |Ps|`, limb `i`, and that
instance's seed bytes. -/
theorem key_msg {Ps : List InstPub} {fwd : List (Nat × Nat)} (hlen : Ps.length < 2013265921)
    {M : List Fp} (hM : M ∈ (render Ps fwd).pubb.map (·.map Fp.ofNat))
    {τ i lo hi : Nat} (hτ : τ < 2013265921) (hi16 : i < 16) (hlo : lo < 2013265921) (hhi : hi < 2013265921)
    (e : M = [τ, TAG_KEY, i, lo, hi, 0, 0].map Fp.ofNat) :
    τ < Ps.length ∧ lo = ((Ps.getD τ instD).seed.getD (2 * i) 0).toNat ∧
      hi = ((Ps.getD τ instD).seed.getD (2 * i + 1) 0).toNat := by
  subst e
  obtain ⟨r, hr, hre⟩ := List.mem_map.1 hM
  rw [render_pubb, List.mem_append, List.mem_flatMap] at hr
  have u8 : ∀ (x : UInt8), x.toNat < 2013265921 := fun x => by have := x.toNat_lt; omega
  rcases hr with ⟨τ', hτ', hr⟩ | hr
  · rw [List.mem_append] at hr
    rcases hr with hr | hr
    · simp only [keyRecs, List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hre
      obtain ⟨e1, -, e3, e4, e5, -⟩ := hre
      have h1 := ofNat_inj' (by have := List.mem_range.1 hτ'; omega) hτ e1
      have h3 := ofNat_inj' (by omega) (by omega) e3
      have h4 := ofNat_inj' (u8 _) hlo e4
      have h5 := ofNat_inj' (u8 _) hhi e5
      subst h1 h3
      exact ⟨List.mem_range.1 hτ', h4.symm, h5.symm⟩
    · simp only [ashRecs, List.mem_map] at hr
      obtain ⟨k, -, rfl⟩ := hr
      simp only [List.map_cons, List.cons.injEq] at hre
      exact absurd (ofNat_inj' (by decide) (by decide) hre.2.1) (by simp [TAG_ASH, TAG_KEY])
  · simp only [fwdRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr
    simp only [List.map_cons, List.map_append, List.cons_append, List.cons.injEq] at hre
    exact absurd (ofNat_inj' (by decide) (by decide) hre.2.1) (by simp [TAG_FWD, TAG_KEY])

/-- Public-record ownership of `SPUBB`: no table sends, every public segment sends. -/
structure PubbOwn (AP : AirP) : Prop where
  none : ∀ t, t < AP.tables.length → ∀ i ∈ AP.tables[t]!.interactions, i.bus = B_SPUBB → i.send = false
  pub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SPUBB → seg.send = true

/-- **Key block of the process table.** Its τ is an instance `< |Ps|`, and its 16 limbs are that
instance's seed bytes. -/
theorem key_block {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp : Nat} (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table)
    (PO : PubbOwn AP) (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPUBB true = (render Ps fwd).pubb) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0) :
    cv tr tp f Proc.tau < Ps.length ∧ ∀ i, i < 16 →
      cv tr tp (f + i) Proc.sbIn = ((Ps.getD (cv tr tp f Proc.tau) instD).seed.getD (2 * i) 0).toNat ∧
      cv tr tp (f + i) Proc.sbOut = ((Ps.getD (cv tr tp f Proc.tau) instD).seed.getD (2 * i + 1) 0).toNat := by
  have hL := pLocal_of hH htp htab
  have hH22 := proc_height hH htp htab
  have K := (Proc.proc_keys hL hH22 hf hk hc).1
  have one : ∀ i, i < 16 → cv tr tp f Proc.tau < Ps.length ∧
      cv tr tp (f + i) Proc.sbIn = ((Ps.getD (cv tr tp f Proc.tau) instD).seed.getD (2 * i) 0).toNat ∧
      cv tr tp (f + i) Proc.sbOut = ((Ps.getD (cv tr tp f Proc.tau) instD).seed.getD (2 * i + 1) 0).toNat := by
    intro i hi
    obtain ⟨hfi, -, -, -, hm, hmsg⟩ := K i hi
    have hp := recv_pub hH PO.none PO.pub htp hfi (by rw [htab]; exact mem_i 0 (by decide))
      (by rw [Proc.i0_def]) (by rw [Proc.i0_def]) (by rw [hm]; exact Nat.one_ne_zero)
    rw [I.count, hrec, hmsg] at hp
    have hmem := List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
    exact key_msg hlen hmem (cv_lt _ _) hi (cv_lt _ _) (cv_lt _ _) rfl
  exact ⟨(one 0 (by decide)).1, fun i hi => (one i hi).2⟩

/-- **`htau`**: every active process row belongs to an instance `< |Ps|`. -/
theorem proc_htau {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp : Nat} (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table)
    (PO : PubbOwn AP) (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPUBB true = (render Ps fwd).pubb) (hlen : Ps.length < 2013265921) :
    ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < Ps.length := by
  intro w hw ha
  obtain ⟨f, hfw, hk, hc, he⟩ := Proc.tau_witness (pLocal_of hH htp htab) w hw ha
  rw [← he]
  exact (key_block hH htp htab PO I Ps fwd hrec hlen (by omega) hk hc).1

/-! ## `leWords` of a 32-byte seed -/

def wordAt (s : List UInt8) (j : Nat) : Nat :=
  (s.getD (4 * j) 0).toNat + 256 * (s.getD (4 * j + 1) 0).toNat +
    65536 * (s.getD (4 * j + 2) 0).toNat + 16777216 * (s.getD (4 * j + 3) 0).toNat

theorem leWords_eq : ∀ (m : Nat) (s : List UInt8), s.length = 4 * m →
    leWords s = (List.range m).map (wordAt s)
  | 0, s, h => by
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | m + 1, a :: b :: c :: d :: rest, h => by
    simp only [List.length_cons] at h
    rw [leWords, leWords_eq m rest (by omega), List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
  | m + 1, [], h => by simp at h
  | m + 1, [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | m + 1, [_, _], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | m + 1, [_, _, _], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- **`hseed`**: the process key of an instance block is `leWords` of the instance's seed. -/
theorem proc_hseed {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp : Nat} (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table)
    (PO : PubbOwn AP) (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPUBB true = (render Ps fwd).pubb) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (hs32 : (Ps.getD (cv tr tp f Proc.tau) instD).seed.length = 32) :
    procKey tr tp f = leWords (Ps.getD (cv tr tp f Proc.tau) instD).seed := by
  obtain ⟨-, hB⟩ := key_block hH htp htab PO I Ps fwd hrec hlen hf hk hc
  rw [leWords_eq 8 _ (by omega), procKey]
  apply List.map_congr_left
  intro j hj
  have hj8 := List.mem_range.1 hj
  generalize (Ps.getD (cv tr tp f Proc.tau) instD).seed = s at hB ⊢
  have l1 : limbOf tr tp f (2 * j) = (s.getD (4 * j) 0).toNat + 256 * (s.getD (4 * j + 1) 0).toNat := by
    obtain ⟨a, b⟩ := hB (2 * j) (by omega)
    unfold limbOf; rw [a, b]
    rw [show 2 * (2 * j) = 4 * j by omega]
    have := (s.getD (4 * j) 0).toNat_lt; have := (s.getD (4 * j + 1) 0).toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  have l2 : limbOf tr tp f (2 * j + 1) = (s.getD (4 * j + 2) 0).toNat + 256 * (s.getD (4 * j + 3) 0).toNat := by
    obtain ⟨a, b⟩ := hB (2 * j + 1) (by omega)
    unfold limbOf; rw [a, b]
    rw [show 2 * (2 * j + 1) = 4 * j + 2 by omega, show 4 * j + 2 + 1 = 4 * j + 3 by omega]
    have := (s.getD (4 * j + 2) 0).toNat_lt; have := (s.getD (4 * j + 3) 0).toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  rw [l1, l2, wordAt]
  omega

end ZkFormal.NearV3.Sched
