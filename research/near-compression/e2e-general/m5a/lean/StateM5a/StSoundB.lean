import StateM5a.StSoundA
import StateM5a.M5b

/-!
# StateM5a.StSoundB — who sends on the M5b buses (M5a-7, STATE rows soundness, part 2)

For the M5b AIR the prover runs, `fullAir D (m5bX host prev post n) nb np` (`M5b.lean`; tables
`0..11` = `m5aAir`, `12` = the M5a tape with no writes, `13` = `SHAS`, `14` = `STB`, `15` = `STW`,
`16` = the execution side's tape `tapeTable host`), with `HostOK host` (the host tape carries only
`SREQ`/`HB` entries):

* no `m5aAir` table sends on `SB2`, `SD2`, `DESC`, `HB`, `SREQ` or `WRITE` (`m5a_newOk`, `decide`
  per table);
* **`sb2_sent`**: every `SB2` message sent is an active `STB` row's `(ID_ST + m, j, b)`;
* **`desc_sent`**: every `DESC` message sent is a closing `STB` row's `(m, ts, base, j + 1)`;
* **`sd2_sent`**: every `SD2` message sent is a `SHAS` digest row's (`colDmult = 1`);
* **`write_sent_row`**: every `WRITE` message sent is an active `STW` row's.
-/

namespace StateM5a.StSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.FieldRows
open StateM5a.KeyDecode StateM5a.DecodeM5a StateM5a.KcChain StateM5a.Tape StateM5a.M5b

set_option maxRecDepth 100000

/-! ## The tables of the M5b AIR -/

theorem m5a_len (D : Nat) : (m5aAir D).tables.length = 12 := by simp [m5aAir]

theorem x_get {D : Nat} {extra : List Table} {nb np t k : Nat} (htk : t = 12 + k)
    (ht : t < (fullAir D extra nb np).tables.length) (hk : k < extra.length) :
    (fullAir D extra nb np).tables[t] = extra[k] := by
  subst htk
  simp only [fullAir]
  rw [List.getElem_append_right (by rw [m5a_len]; omega)]
  congr 1
  rw [m5a_len]; omega

theorem m5bX_len (host : List (Nat × Bool × List Nat)) (prev post : NearSpec.Bytes) (n : Nat) :
    (m5bX host prev post n).length = 5 := by simp [m5bX, m5bRest, m5bExtra]

theorem bx_len {D : Nat} {host : List (Nat × Bool × List Nat)} {prev post : NearSpec.Bytes} {n nb np : Nat} :
    (fullAir D (m5bX host prev post n) nb np).tables.length = 17 := by
  rw [fullAir_len, m5bX_len]

/-- Senders that are not `m5aAir` tables send from `extra`. -/
def newOk (is : List Interaction) : Bool :=
  is.all fun i => !i.send || (decide (i.bus < NUM_BUSES_WS) && decide (i.bus ≠ B_WRITE))

theorem m5a_newOk (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length),
    newOk ((m5aAir D).tables[t]).interactions = true
  | 0, _ => by show newOk shaTable.interactions = true; decide
  | 1, _ => by show newOk Key.interactions = true; decide
  | 2, _ => by show newOk Br.interactions = true; decide
  | 3, _ => by show newOk Sn.interactions = true; decide
  | 4, _ => by show newOk Kcmp.interactions = true; decide
  | 5, _ => by show newOk Wsb.interactions = true; decide
  | 6, _ => by show newOk Wsn.interactions = true; decide
  | 7, _ => by show newOk Wsa.interactions = true; decide
  | 8, _ => by show newOk Snc.interactions = true; decide
  | 9, _ => by show newOk Rng.interactions = true; decide
  | 10, _ => by show newOk Wsl.interactions = true; decide
  | 11, _ => by show newOk Wsp.interactions = true; decide
  | n + 12, h => absurd h (by simp [m5aAir])

theorem m5a_no (D : Nat) {b : Nat} (hb : NUM_BUSES_WS ≤ b ∨ b = B_WRITE) :
    ∀ t (ht : t < (m5aAir D).tables.length), sendsOn ((m5aAir D).tables[t]).interactions b = false := by
  intro t ht
  cases h : sendsOn ((m5aAir D).tables[t]).interactions b with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hs⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    have := List.all_eq_true.1 (m5a_newOk D t ht) i hi
    simp only [hs.2, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
    rw [hs.1] at this
    rcases hb with hb | hb
    · omega
    · exact (this.2 hb).elim

section
variable {tr : Trace Fp} {pub : List Fp}

/-- **A sender outside `m5aAir`.** -/
theorem sender_x {D : Nat} {extra : List Table} {nb np b : Nat}
    (hS : ∀ t (ht : t < (m5aAir D).tables.length), sendsOn ((m5aAir D).tables[t]).interactions b = false)
    {m : List Fp} (hm : m ∈ busList (fullAir D extra nb np) tr pub b true) :
    ∃ k, ∃ hk : k < extra.length, ∃ r, r < tr.height (12 + k) ∧ ∃ i ∈ (extra[k]).interactions,
      i.bus = b ∧ i.send = true ∧ 0 < i.multNat tr (12 + k) r pub ∧ m = i.msgVal tr (12 + k) r pub := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hp, rfl⟩ := mem_busList.1 hm
  by_cases hlt : t < (m5aAir D).tables.length
  · rw [fullAir_get hlt ht] at hi
    exact (not_sends (hS t hlt) hi hb hs).elim
  · rw [m5a_len] at hlt
    have hk : t - 12 < extra.length := by rw [fullAir_len] at ht; omega
    have htk : t = 12 + (t - 12) := by omega
    rw [x_get htk ht hk] at hi
    refine ⟨t - 12, hk, r, by rw [← htk]; exact hr, i, hi, hb, hs, ?_, ?_⟩
    · rw [← htk]; exact hp
    · rw [← htk]

end

theorem tape0_bus (prev post : NearSpec.Bytes) (n : Nat) :
    ∀ i ∈ (tapeTable (m5aTape [] prev post n)).interactions, i.bus = B_TCH := by
  intro i hi
  simp only [tapeTable, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  simp only [m5aTape, List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

/-- The five extra tables. -/
theorem x_cases {host : List (Nat × Bool × List Nat)} (hh : HostOK host) {prev post : NearSpec.Bytes} {n k : Nat}
    (hk : k < (m5bX host prev post n).length) {i : Interaction}
    (hi : i ∈ ((m5bX host prev post n)[k]).interactions) :
    (k = 0 ∧ i.bus = B_TCH) ∨ (k = 1 ∧ i ∈ shaTableS.interactions) ∨ (k = 2 ∧ i ∈ Stb.interactions) ∨
      (k = 3 ∧ i ∈ Stw.interactions) ∨ (k = 4 ∧ (i.bus = B_SREQ ∨ i.bus = B_HB)) := by
  have hk5 : k < 5 := by rw [m5bX_len] at hk; exact hk
  match k, hk, hi, hk5 with
  | 0, _, hi, _ => exact .inl ⟨rfl, tape0_bus prev post n i hi⟩
  | 1, _, hi, _ => exact .inr (.inl ⟨rfl, hi⟩)
  | 2, _, hi, _ => exact .inr (.inr (.inl ⟨rfl, hi⟩))
  | 3, _, hi, _ => exact .inr (.inr (.inr (.inl ⟨rfl, hi⟩)))
  | 4, _, hi, _ =>
    refine .inr (.inr (.inr (.inr ⟨rfl, ?_⟩)))
    change i ∈ (tapeTable host).interactions at hi
    simp only [tapeTable, List.mem_map] at hi
    obtain ⟨e, he, rfl⟩ := hi
    exact hh e he
  | _ + 5, _, _, h => exact absurd h (by omega)

/-! ## Interactions of the new tables -/

theorem stb_sb2_s : Stb.interactions.filter (fun i => decide (i.bus = B_SB2 ∧ i.send = true)) =
    [snd B_SB2 (Stb.c "act") [K ID_ST + Stb.c "m", Stb.c "j", Stb.c "b"]] := by decide
theorem stb_desc_s : Stb.interactions.filter (fun i => decide (i.bus = B_DESC ∧ i.send = true)) =
    [snd B_DESC (Stb.c "last") [Stb.c "m", Stb.c "ts", Stb.c "base", Stb.c "j" + 1]] := by decide
theorem stb_hb_r_mem : rcv B_HB (Stb.c "act") [Stb.c "ts", Stb.c "base" + Stb.c "j", Stb.c "b"] ∈
    Stb.interactions := memD_mem (by decide)
theorem shas_sd2_s : shaTableS.interactions.filter (fun i => decide (i.bus = B_SD2 ∧ i.send = true)) =
    [(ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[16]!] := by decide
theorem stw_write_s : Stw.interactions.filter (fun i => decide (i.bus = B_WRITE ∧ i.send = true)) =
    [snd B_WRITE (Stw.c "act") ([Stw.c "seg", Stw.c "ts"] ++ pack2 (fun b => Stw.c "dk" b) ++
      [Stw.c "pr", Stw.c "vlen"] ++ pack2 (fun b => Stw.c "dv" b))] := by decide

theorem shas_no_sb2 : sendsOn shaTableS.interactions B_SB2 = false := by decide
theorem shas_no_desc : sendsOn shaTableS.interactions B_DESC = false := by decide
theorem shas_no_write : sendsOn shaTableS.interactions B_WRITE = false := by decide
theorem stb_no_sd2 : sendsOn Stb.interactions B_SD2 = false := by decide
theorem stb_no_write : sendsOn Stb.interactions B_WRITE = false := by decide
theorem stw_no_sb2 : sendsOn Stw.interactions B_SB2 = false := by decide
theorem stw_no_sd2 : sendsOn Stw.interactions B_SD2 = false := by decide
theorem stw_no_desc : sendsOn Stw.interactions B_DESC = false := by decide

theorem shas_rcv (q : Nat) (hq : q < 16) :
    (ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[q]! ∈ shaTableS.interactions ∧
    ((ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[q]!).bus = B_SB2 ∧
    ((ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[q]!).send = false ∧
    ((ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[q]!).mult =
      [Expr.col (ZkFormal.Sha.Layout.colF q) false] := by
  have hl : q < (ZkFormal.Sha.Table.interactions B_SB2 B_SD2).length := by
    simp [ZkFormal.Sha.Table.interactions]; omega
  have he : (ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[q]! =
      (ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[q] := by
    simp [getElem!_def, List.getElem?_eq_getElem hl]
  rw [he]
  refine ⟨List.getElem_mem hl, ?_⟩
  simp [ZkFormal.Sha.Table.interactions, hq, ZkFormal.Sha.Table.E.c]

/-! ## Senders on the M5b buses -/

section
variable {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {host : List (Nat × Bool × List Nat)}
  {prev post : NearSpec.Bytes} {n : Nat} (hh : HostOK host)
include hh

theorem sb2_sent {m : List Fp}
    (hm : m ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SB2 true) :
    ∃ r, r < tr.height 14 ∧ (Stb.c "act").eval tr 14 r pub = 1 ∧
      m = [(K ID_ST + Stb.c "m").eval tr 14 r pub, (Stb.c "j").eval tr 14 r pub,
        (Stb.c "b").eval tr 14 r pub] := by
  obtain ⟨k, hk, r, hr, i, hi, hb, hs, hp, rfl⟩ := sender_x (m5a_no D (.inl (by decide))) hm
  rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact absurd (hb.symm.trans h) (by decide)
  · exact (not_sends shas_no_sb2 h hb hs).elim
  · obtain rfl := filter_one_mem stb_sb2_s h hb hs
    exact ⟨r, hr, multNat_one_bit rfl hp, rfl⟩
  · exact (not_sends stw_no_sb2 h hb hs).elim
  · rcases h with h | h <;> exact absurd (hb.symm.trans h) (by decide)

theorem desc_sent {m : List Fp}
    (hm : m ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_DESC true) :
    ∃ r, r < tr.height 14 ∧ (Stb.c "last").eval tr 14 r pub = 1 ∧
      m = [(Stb.c "m").eval tr 14 r pub, (Stb.c "ts").eval tr 14 r pub, (Stb.c "base").eval tr 14 r pub,
        (Stb.c "j" + 1).eval tr 14 r pub] := by
  obtain ⟨k, hk, r, hr, i, hi, hb, hs, hp, rfl⟩ := sender_x (m5a_no D (.inl (by decide))) hm
  rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact absurd (hb.symm.trans h) (by decide)
  · exact (not_sends shas_no_desc h hb hs).elim
  · obtain rfl := filter_one_mem stb_desc_s h hb hs
    exact ⟨r, hr, multNat_one_bit rfl hp, rfl⟩
  · exact (not_sends stw_no_desc h hb hs).elim
  · rcases h with h | h <;> exact absurd (hb.symm.trans h) (by decide)

theorem sd2_sent {m : List Fp}
    (hm : m ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SD2 true) :
    ∃ d, d < tr.height 13 ∧ tr.cell 13 d ZkFormal.Sha.Layout.colDmult = 1 ∧
      m = ((ZkFormal.Sha.Table.interactions B_SB2 B_SD2)[16]!).msgVal tr 13 d pub := by
  obtain ⟨k, hk, r, hr, i, hi, hb, hs, hp, rfl⟩ := sender_x (m5a_no D (.inl (by decide))) hm
  rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact absurd (hb.symm.trans h) (by decide)
  · obtain rfl := filter_one_mem shas_sd2_s h hb hs
    exact ⟨r, hr, multNat_one_bit (g := Expr.col ZkFormal.Sha.Layout.colDmult false) (by decide) hp, rfl⟩
  · exact (not_sends stb_no_sd2 h hb hs).elim
  · exact (not_sends stw_no_sd2 h hb hs).elim
  · rcases h with h | h <;> exact absurd (hb.symm.trans h) (by decide)

theorem write_sent_row {m : List Fp}
    (hm : m ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_WRITE true) :
    ∃ r, r < tr.height 15 ∧ (Stw.c "act").eval tr 15 r pub = 1 ∧
      m = (snd B_WRITE (Stw.c "act") ([Stw.c "seg", Stw.c "ts"] ++ pack2 (fun b => Stw.c "dk" b) ++
        [Stw.c "pr", Stw.c "vlen"] ++ pack2 (fun b => Stw.c "dv" b))).msgVal tr 15 r pub := by
  obtain ⟨k, hk, r, hr, i, hi, hb, hs, hp, rfl⟩ := sender_x (m5a_no D (.inr rfl)) hm
  rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact absurd (hb.symm.trans h) (by decide)
  · exact (not_sends shas_no_write h hb hs).elim
  · exact (not_sends stb_no_write h hb hs).elim
  · obtain rfl := filter_one_mem stw_write_s h hb hs
    exact ⟨r, hr, multNat_one_bit rfl hp, rfl⟩
  · rcases h with h | h <;> exact absurd (hb.symm.trans h) (by decide)

end

end StateM5a.StSound
