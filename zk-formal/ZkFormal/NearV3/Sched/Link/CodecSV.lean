import ZkFormal.NearV3.Sched.Link.CodecVal

/-!
# `codec_schedVal`: the trie lane's `SchedVal` interface

There is a function `sv : Nat → List Nat` (instance τ ↦ its new `0x0f` encoding, the post bytes
of τ's codec block) with:
* bytes `< 256` and length `< 2^24`;
* every received `SPLEN` message is `(τ, |sv τ|)`;
* every received `SPOST` message is `(τ, d, (sv τ)[d])` with `d < |sv τ|`.

Ingredients:
* `codec_cover`: every active codec row lies in an instance block;
* `enc_row`: an encoding row is `f + i` with `i < L = 37 + 24·N`;
* `block_unique`: distinct blocks have distinct τ. Each block's first row receives its `SPAR`
  codec parameters `[τ, 0, …]`. Only public segments send on `SPAR`, and `render` has one such
  record per τ, so two blocks with the same τ would need the record twice.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem pad_next (hL : CLocal tr t pub) {w : Nat} (hw : w + 1 < tr.height t)
    (ha : cv tr t w act = 0) : cv tr t (w + 1) act = 0 := by
  have hw0 : w < tr.height t := by omega
  obtain ⟨q, c1⟩ := zd hL hw0 (e := mul3 .isTransition (notE (c act)) (n act))
    (by simp [constraints, cKind])
  zs c1 [nx hw, ha]
  simp only [zev, Mem.tenv_last_zero hw] at c1
  have := lt (tr := tr) (t := t) (w + 1) act
  omega

theorem act_prev (hL : CLocal tr t pub) {w : Nat} (hw1 : w + 1 < tr.height t)
    (ha : cv tr t (w + 1) act = 1) : cv tr t w act = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (kinds hL (show w < tr.height t by omega)).1 with h | h
  · have := pad_next hL hw1 h; omega
  · exact h

theorem row_first_kF (hL : CLocal tr t pub) (h0 : 0 < tr.height t) (ha : cv tr t 0 act = 1) :
    cv tr t 0 kF = 1 := by
  have hf : (tenv tr t 0 pub).first = 1 := by simp [tenv]
  obtain ⟨q, c1⟩ := zd hL h0 (e := .mul .isFirst (.mul (c act) (notE (c kF))))
    (by simp [constraints, cKind])
  zs c1 [zev_isFirst, hf, ha]
  have := (kinds hL h0).2.2.2.2.2.1
  omega

/-- **Every active row lies in an instance block.** -/
theorem codec_cover (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) :
    ∀ r, r < tr.height t → cv tr t r act = 1 →
      ∃ f, f ≤ r ∧ cv tr t f kF = 1 ∧ r < f + 5 + 24 * cv tr t f NN + 64 := by
  intro r
  induction r with
  | zero => intro h0 ha; exact ⟨0, Nat.le_refl _, row_first_kF hL h0 ha, by omega⟩
  | succ r ih =>
    intro hr1 ha1
    obtain ⟨f, hfr, hF, hrf⟩ := ih (by omega) (act_prev hL hr1 ha1)
    by_cases hlt : r + 1 < f + 5 + 24 * cv tr t f NN + 64
    · exact ⟨f, by omega, hF, hlt⟩
    · have he : r + 1 = f + 5 + 24 * cv tr t f NN + 64 := by omega
      have hB := codec_block hL hH (show f < tr.height t by omega) hF
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hend⟩ := hB
      rw [← he] at hend
      rcases hend with h | h
      · omega
      · exact ⟨r + 1, Nat.le_refl _, h, by omega⟩

/-- The encoding gate is `kH + kR + kZ`. -/
theorem encG_eval (r : Nat) (h : (encG).eval tr t r pub = 1) (hL : CLocal tr t pub)
    (hr : r < tr.height t) : cv tr t r kH + cv tr t r kR + cv tr t r kZ = 1 := by
  have K := kinds hL hr
  have e : (encG).eval tr t r pub = Fp.ofNat (cv tr t r kH + cv tr t r kR + cv tr t r kZ) :=
    ev_of (by simp only [encG, zev_add, zev_c, cur_cv]; omega)
  rw [e] at h
  have h1 : Fp.ofNat (cv tr t r kH + cv tr t r kR + cv tr t r kZ) = Fp.ofNat 1 := h
  exact ofNat_inj' (by omega) (by decide) h1

/-- **An encoding row is `f + i` with `i < 37 + 24·N` in its block.** -/
theorem enc_row (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {r : Nat} (hr : r < tr.height t)
    (he : cv tr t r kH + cv tr t r kR + cv tr t r kZ = 1) :
    ∃ f, f ≤ r ∧ cv tr t f kF = 1 ∧ r - f < 37 + 24 * cv tr t f NN := by
  have K := kinds hL hr
  obtain ⟨f, hfr, hF, hrf⟩ := codec_cover hL hH r hr (by omega)
  refine ⟨f, hfr, hF, ?_⟩
  apply Nat.lt_of_not_le; intro hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hA, -⟩ := codec_block hL hH (show f < tr.height t by omega) hF
  obtain ⟨-, hkA, -⟩ := hA (r - f - (5 + 24 * cv tr t f NN + 32)) (by omega)
  rw [show f + 5 + 24 * cv tr t f NN + 32 + (r - f - (5 + 24 * cv tr t f NN + 32)) = r by omega] at hkA
  omega

end Codec

/-! ## One codec block per τ -/

theorem count_two {α : Type} [BEq α] [LawfulBEq α] (g : Nat → List α) (m : α) {a b : Nat}
    (hab : a ≠ b) (ha : m ∈ g a) (hb : m ∈ g b) :
    ∀ (l : List Nat), l.Nodup → a ∈ l → b ∈ l → 2 ≤ (l.flatMap g).count m
  | [], _, h, _ => by simp at h
  | x :: tl, hnd, hal, hbl => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.1 hal with e | e <;> rcases List.mem_cons.1 hbl with e' | e'
    · exact absurd (e.trans e'.symm) hab
    · subst e
      have h1 := List.count_pos_iff.2 ha
      have h2 := List.count_pos_iff.2 (List.mem_flatMap.2 ⟨b, e', hb⟩)
      omega
    · subst e'
      have h1 := List.count_pos_iff.2 hb
      have h2 := List.count_pos_iff.2 (List.mem_flatMap.2 ⟨a, e, ha⟩)
      omega
    · have := count_two g m hab ha hb tl hnd.2 e e'
      omega

theorem parBlock_head {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parBlock τ P) :
    r.head? = some τ := by
  simp only [parBlock, List.mem_append, List.mem_singleton] at hr
  rcases hr with (((rfl | hr) | hr) | hr) | hr
  · simp [parCodec]
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr; simp [parScan]
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr; simp
  · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨side, -, x, -, rfl⟩ := hr; simp
  · simp only [linkRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr; simp

theorem parBlock_tag {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parBlock τ P) :
    r = parCodec τ P ∨ ∃ a, r[1]? = some a ∧ 1 ≤ a ∧ a ≤ 4 := by
  simp only [parBlock, List.mem_append, List.mem_singleton] at hr
  rcases hr with (((rfl | hr) | hr) | hr) | hr
  · exact Or.inl rfl
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact Or.inr ⟨1, by simp [parScan, PT_SCAN], by decide, by decide⟩
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
    exact Or.inr ⟨2, by simp [PT_RAW], by decide, by decide⟩
  · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨side, -, x, -, rfl⟩ := hr
    exact Or.inr ⟨3, by simp [PT_SHD], by decide, by decide⟩
  · simp only [linkRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr
    exact Or.inr ⟨4, by simp [PT_LINK], by decide, by decide⟩

theorem ne_tag0 {r : List Nat} {M : List Fp} {a : Nat} (hr : r[1]? = some a) (ha1 : 1 ≤ a) (ha4 : a ≤ 4)
    (hM : M[1]? = some (Fp.ofNat 0)) : r.map Fp.ofNat ≠ M := by
  intro e; subst e
  rw [List.getElem?_map, hr] at hM
  simp only [Option.map_some, Option.some.injEq] at hM
  have := ofNat_inj' (by omega) (by decide) hM
  omega

/-- A tag-0 `SPAR` record of head `τ` is `τ`'s codec parameter record. -/
theorem par_codec_mem {Ps : List InstPub} {fwd : List (Nat × Nat)} (hlen : Ps.length < 2013265921)
    {M : List Fp} (hM : M ∈ (render Ps fwd).par.map (·.map Fp.ofNat)) {τ : Nat} (hτ : τ < 2013265921)
    (h0 : M.head? = some (Fp.ofNat τ)) (h1 : M[1]? = some (Fp.ofNat 0)) :
    τ < Ps.length ∧ M = (parCodec τ (Ps.getD τ instD)).map Fp.ofNat := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [render_par, List.mem_flatMap] at hr
  obtain ⟨τ', hτ', hr⟩ := hr
  have hτ'l := List.mem_range.1 hτ'
  have hh := parBlock_head hr
  have e : τ' = τ := by
    by_cases hne : τ' = τ
    · exact hne
    · exact absurd rfl (ne_of_head hh h0 (by omega) hτ hne)
  subst e
  refine ⟨hτ'l, ?_⟩
  rcases parBlock_tag hr with e | ⟨a, ha, h1a, h4a⟩
  · rw [e]
  · exact absurd rfl (ne_tag0 ha h1a h4a h1)

/-- The non-codec records of a block. -/
def parRest (τ : Nat) (P : InstPub) : List (List Nat) :=
  (if P.raw.isEmpty then [] else [parScan τ P]) ++ rawRecs τ P ++ shardRecs τ P ++ linkRecs τ P

theorem parBlock_split (τ : Nat) (P : InstPub) : parBlock τ P = [parCodec τ P] ++ parRest τ P := by
  simp [parBlock, parRest, List.append_assoc]

theorem parRest_tag {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parRest τ P) :
    ∃ a, r[1]? = some a ∧ 1 ≤ a ∧ a ≤ 4 := by
  simp only [parRest, List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨1, by simp [parScan, PT_SCAN], by decide, by decide⟩
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
    exact ⟨2, by simp [PT_RAW], by decide, by decide⟩
  · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨side, -, x, -, rfl⟩ := hr
    exact ⟨3, by simp [PT_SHD], by decide, by decide⟩
  · simp only [linkRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr
    exact ⟨4, by simp [PT_LINK], by decide, by decide⟩

theorem par_codec_count {Ps : List InstPub} {fwd : List (Nat × Nat)} (hlen : Ps.length < 2013265921)
    (τ : Nat) (hτ : τ < Ps.length) :
    ((render Ps fwd).par.map (·.map Fp.ofNat)).count ((parCodec τ (Ps.getD τ instD)).map Fp.ofNat) ≤ 1 := by
  rw [render_par]
  rw [count_flatMap_one Fp.ofNat _ _ τ _ List.nodup_range (List.mem_range.2 hτ) ?_]
  · rw [parBlock_split, List.map_append, List.count_append]
    have h0 : ((parRest τ (Ps.getD τ instD)).map (·.map Fp.ofNat)).count
        ((parCodec τ (Ps.getD τ instD)).map Fp.ofNat) = 0 := by
      apply count_zero_of
      intro r hr
      obtain ⟨a, ha, h1, h4⟩ := parRest_tag hr
      exact ne_tag0 ha h1 h4 (by simp [parCodec])
    rw [h0]
    simp
  · intro τ' hmem hne r hr
    exact ne_of_head (parBlock_head hr) (by simp [parCodec]) (by have := List.mem_range.1 hmem; omega)
      (by omega) hne

theorem codec_mem (k : Nat) (hk : k < 16) : Codec.interactions[k]! ∈ Codec.interactions := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Codec.interactions]; omega)]
  exact List.getElem_mem _

/-- Ownership of `SPAR`: only public segments send. -/
structure SparOwn (AP : AirP) : Prop where
  none : ∀ t, t < AP.tables.length → ∀ i ∈ AP.tables[t]!.interactions, i.bus = B_SPAR → i.send = false
  pub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SPAR → seg.send = true

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem codec_local (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) : Codec.CLocal tr tc pub := by
  have := local_of_holdsP hH O.lt; rw [O.tab] at this; exact this

theorem codec_h22 (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) : tr.height tc ≤ 2 ^ 22 :=
  height_le hH O.lt O.tab rfl

/-- The codec parameter message of a first row is `render`'s `parCodec` record of its τ. -/
theorem first_par (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) :
    cv tr tc f Codec.tau < Ps.length ∧
      (Codec.interactions[6]!).msgVal tr tc f pub =
        (parCodec (cv tr tc f Codec.tau) (Ps.getD (cv tr tc f Codec.tau) instD)).map Fp.ofNat := by
  obtain ⟨-, -, -, -, m6, msg6, -⟩ := Codec.codec_first (codec_local hH O) (codec_h22 hH O) hf hF
  have hp := recv_pub hH SO.none SO.pub O.lt hf (by rw [O.tab]; exact codec_mem 6 (by decide))
    (by rw [Codec.i6_def]) (by rw [Codec.i6_def]) (by rw [m6]; exact Nat.one_ne_zero)
  rw [I.count, hrec] at hp
  have hmem := List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
  exact par_codec_mem hlen hmem (cv_lt _ _) (by rw [msg6]; rfl) (by rw [msg6]; rfl)

theorem busCount_send_zero {b : Nat}
    (hnone : ∀ t, t < AP.tables.length → ∀ i ∈ AP.tables[t]!.interactions, i.bus = b → i.send = false)
    (m : List Fp) : busCount AP.toAir tr pub b true m = 0 := by
  rcases Nat.eq_zero_or_pos (busCount AP.toAir tr pub b true m) with h0 | h0
  · exact h0
  exfalso
  obtain ⟨t', ht', hc⟩ := busCount_go_pos tr pub b true _ AP.tables 0
    (by unfold busCount at h0; exact Nat.pos_iff_ne_zero.1 h0)
  simp only [Nat.zero_add] at hc
  obtain ⟨r', -, i', hi', hb', hs', -, -⟩ := exists_of_tableBusCount hc
  rw [hnone t' ht' i' hi' hb'] at hs'; simp at hs'

/-- **One codec block per τ.** -/
theorem block_unique (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921)
    {f1 f2 : Nat} (hf1 : f1 < tr.height tc) (hF1 : cv tr tc f1 Codec.kF = 1)
    (hf2 : f2 < tr.height tc) (hF2 : cv tr tc f2 Codec.kF = 1)
    (hτ : cv tr tc f1 Codec.tau = cv tr tc f2 Codec.tau) : f1 = f2 := by
  by_cases e : f1 = f2
  · exact e
  exfalso
  obtain ⟨hl1, P1⟩ := first_par hH O SO I Ps fwd hrec hlen hf1 hF1
  obtain ⟨-, P2⟩ := first_par hH O SO I Ps fwd hrec hlen hf2 hF2
  rw [← hτ] at P2
  generalize hMdef : (parCodec (cv tr tc f1 Codec.tau) (Ps.getD (cv tr tc f1 Codec.tau) instD)).map Fp.ofNat = M at P1 P2
  obtain ⟨-, -, -, -, m61, -⟩ := Codec.codec_first (codec_local hH O) (codec_h22 hH O) hf1 hF1
  obtain ⟨-, -, -, -, m62, -⟩ := Codec.codec_first (codec_local hH O) (codec_h22 hH O) hf2 hF2
  have hin : ∀ w, (Codec.interactions[6]!).multNat tr tc w pub = 1 →
      (Codec.interactions[6]!).msgVal tr tc w pub = M →
      M ∈ rowTraffic Codec.interactions tr tc w pub B_SPAR false := by
    intro w hm hmsg
    unfold rowTraffic
    refine List.mem_flatMap.2 ⟨Codec.interactions[6]!, codec_mem 6 (by decide), ?_⟩
    rw [if_pos (by rw [Codec.i6_def]; exact ⟨rfl, rfl⟩), hm, hmsg]
    simp
  have h2 : 2 ≤ tableBusCount Codec.interactions tr tc pub B_SPAR false M := by
    rw [tableBusCount_eq]
    exact count_two _ M e (hin f1 m61 P1) (hin f2 m62 P2) _ List.nodup_range
      (List.mem_range.2 hf1) (List.mem_range.2 hf2)
  have hge := busCount_go_ge tr pub B_SPAR false M AP.tables 0 tc O.lt
  rw [Nat.zero_add, O.tab, show Codec.table.interactions = Codec.interactions from rfl] at hge
  have hbal := hH.balance B_SPAR M
  rw [busCount_send_zero SO.none, pubCount_zero (s := false) (fun seg h1 h2 => by rw [SO.pub seg h1 h2]; simp) _,
    I.count, hrec] at hbal
  have hle := par_codec_count (fwd := fwd) hlen _ hl1
  rw [hMdef] at hle
  unfold busCount at hbal
  omega

/-! ## The new `0x0f` value of each instance -/

theorem msg1_eq (t w : Nat) : (Codec.interactions[1]!).msgVal tr t w pub =
    [cv tr t w Codec.tau, cv tr t w Codec.pos, cv tr t w Codec.bpost].map Fp.ofNat := by
  rw [Codec.i1_def]
  simp only [Interaction.msgVal, List.map_cons, List.map_nil]
  simp only [cv, Fp.ofNat_toNat]
  rfl

theorem mult1_enc {t w : Nat} (h : (Codec.interactions[1]!).multNat tr t w pub ≠ 0) :
    (Codec.encG).eval tr t w pub = 1 := by
  rw [Codec.i1_def] at h
  unfold Interaction.multNat at h
  simp only [Interaction.multNat.go] at h
  by_cases e : (Codec.encG).eval tr t w pub = 1
  · exact e
  · simp [e] at h

open Classical in
/-- Instance τ's post bytes: the encoding of its (unique) codec block, `[]` without a block. -/
noncomputable def svOf (tr : Trace Fp) (tc τ : Nat) : List Nat :=
  if h : ∃ f, f < tr.height tc ∧ cv tr tc f Codec.kF = 1 ∧ cv tr tc f Codec.tau = τ then
    (List.range (37 + 24 * cv tr tc (Classical.choose h) Codec.NN)).map
      fun i => cv tr tc (Classical.choose h + i) Codec.bpost
  else []

theorem svOf_block (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) :
    svOf tr tc (cv tr tc f Codec.tau) =
      (List.range (37 + 24 * cv tr tc f Codec.NN)).map fun i => cv tr tc (f + i) Codec.bpost := by
  have hex : ∃ f', f' < tr.height tc ∧ cv tr tc f' Codec.kF = 1 ∧ cv tr tc f' Codec.tau = cv tr tc f Codec.tau :=
    ⟨f, hf, hF, rfl⟩
  unfold svOf
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have e := block_unique hH O SO I Ps fwd hrec hlen h1 h2 hf hF h3
  rw [e]

/-- **`SchedVal`** (the trie lane's `UpsVal` interface): one byte string per instance, whose
length is every `SPLEN` and whose bytes are every `SPOST`. -/
theorem codec_schedVal (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921) :
    ∃ sv : Nat → List Nat,
      (∀ τ, ∀ x ∈ sv τ, x < 256) ∧ (∀ τ, (sv τ).length < 2 ^ 24) ∧
      (∀ t r (i : Interaction), t < AP.tables.length → r < tr.height t → i ∈ AP.tables[t]!.interactions →
        i.bus = B_SPLEN → i.send = false → i.multNat tr t r pub ≠ 0 →
        ∃ τ, i.msgVal tr t r pub = [τ, (sv τ).length].map Fp.ofNat) ∧
      (∀ t r (i : Interaction), t < AP.tables.length → r < tr.height t → i ∈ AP.tables[t]!.interactions →
        i.bus = B_SPOST → i.send = false → i.multNat tr t r pub ≠ 0 →
        ∃ τ d, d < (sv τ).length ∧ i.msgVal tr t r pub = [τ, d, (sv τ).getD d 0].map Fp.ofNat) := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  refine ⟨svOf tr tc, ?_, ?_, ?_, ?_⟩
  · intro τ x hx
    unfold svOf at hx
    split at hx
    · rename_i h
      obtain ⟨hf, hF, -⟩ := Classical.choose_spec h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have hi' := List.mem_range.1 hi
      obtain ⟨P1, -⟩ := Codec.codec_post hL hH22 hf hF
      obtain ⟨m1, -⟩ := P1 i (by omega)
      have hrow : Classical.choose h + i < tr.height tc := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hf hF
        omega
      have he := Codec.encG_eval _ (mult1_enc (by rw [m1]; exact Nat.one_ne_zero)) hL hrow
      exact (Codec.bytes hL hrow he).2.1
    · simp at hx
  · intro τ
    unfold svOf
    split
    · rename_i h
      obtain ⟨hf, hF, -⟩ := Classical.choose_spec h
      obtain ⟨-, hN, -⟩ := Codec.codec_block hL hH22 hf hF
      simp only [List.length_map, List.length_range]
      omega
    · simp
  · intro t r i ht hr hi hb hs hm
    obtain ⟨f, hf, hF, hmsg, -, -⟩ := codec_splen_sole hH O ht hr hi hb hs hm
    refine ⟨cv tr tc f Codec.tau, ?_⟩
    rw [hmsg, svOf_block hH O SO I Ps fwd hrec hlen hf hF]
    simp
  · intro t r i ht hr hi hb hs hm
    obtain ⟨r', hr', hm', hmsg⟩ := codec_spost_sole hH O ht hr hi hb hs hm
    have he := Codec.encG_eval _ (mult1_enc hm') hL hr'
    obtain ⟨f, hfr, hF, hlt⟩ := Codec.enc_row hL hH22 hr' he
    have hf : f < tr.height tc := by omega
    obtain ⟨P1, -⟩ := Codec.codec_post hL hH22 hf hF
    obtain ⟨-, hpm⟩ := P1 (r' - f) (by omega)
    rw [show f + (r' - f) = r' by omega, msg1_eq] at hpm
    refine ⟨cv tr tc f Codec.tau, r' - f, ?_, ?_⟩
    · rw [svOf_block hH O SO I Ps fwd hrec hlen hf hF]; simp; omega
    · rw [hmsg, hpm, svOf_block hH O SO I Ps fwd hrec hlen hf hF]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp [show f + (r' - f) = r' by omega]

end ZkFormal.NearV3.Sched
