import M5T1.MsgRowBase

/-!
# M5T1.MsgRowSch — every `MSG` row's descriptor is a schema entry (the `SCH` bus; F-2)

`sch_row`: on a `Holds (fullAir tape xtape)` trace whose `SCHT` descriptor columns are the
preprocessed schema rows (`SchtFixed`) and whose public tapes send nothing on `SCH`, every `MSG`
row's 23 descriptor columns (`desc`) are `g.msg` for an entry `g` of `schema`; hence (`desc_of`)
each descriptor column is the corresponding field of `g`, and (`segAt_of_mem`, the schema's
`(mt, s)` keys are distinct) `g = segAt mt s` for the row's own `mt`, `s` columns.
-/

namespace M5T1.MsgRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus

/-- **Premise**: the `e` columns of `SCHT` (table 2) are the preprocessed schema rows
(`Scht.row`: entry `r`, then the `PAD` entry). The verifying key fixes them. -/
def SchtFixed (tr : Trace Fp) : Prop :=
  ∀ r < tr.height 2, (List.range 23).map (fun j => (tr.cell 2 r j).toNat) = Scht.row r

/-- **Premise** on a public tape: it sends nothing on bus `b` (it may receive). -/
def NoSendOn (b : Nat) (tape : List (Nat × Bool × List Nat)) : Prop :=
  ∀ e ∈ tape, e.1 = b → e.2.1 = false

/-- The 23 descriptor columns of `MSG` row `r`. -/
def desc (tr : Trace Fp) (r : Nat) : List Nat := (List.range 23).map fun j => (tr.cell 3 r j).toNat

/-! ## Who sends on a bus -/

section
variable {tape xtape : List (Nat × Bool × List Nat)}

theorem tape_sender {b : Nat} {tape : List (Nat × Bool × List Nat)} (h : NoSendOn b tape) {i : Interaction}
    (hi : i ∈ (tapeTable tape).interactions) (hb : i.bus = b) (hs : i.send = true) : False := by
  simp only [tapeTable, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  have := h e he hb
  simp only at hs; rw [this] at hs; cases hs

/-- If every Lean table other than `k` never sends on `b` and the tapes do not either, a sender
on `b` is table `k`. -/
theorem sender_idx {b k : Nat}
    (hns : ∀ t, t ≠ k → NoSend (m5t1Air.tables.getD t default) b = true)
    (h1 : NoSendOn b tape) (h2 : NoSendOn b xtape) {t : Nat} (ht : t < (fullAir tape xtape).tables.length)
    {i : Interaction} (hi : i ∈ ((fullAir tape xtape).tables[t]'ht).interactions) (hb : i.bus = b)
    (hs : i.send = true) : t = k := by
  have ht8 : t < 11 := fullAir_len (tape := tape) (xtape := xtape) ▸ ht
  by_cases h6 : t < 9
  · by_cases hne : t = k
    · exact hne
    have := hns t hne
    have h6' : t < m5t1Air.tables.length := by simpa [m5t1Air] using h6
    have e : ((fullAir tape xtape).tables[t]'ht) = m5t1Air.tables.getD t default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h6', Option.getD_some]
      simp only [fullAir]; rw [List.getElem_append_left]
    rw [e] at hi
    exact (noSend_spec this hi hb hs).elim
  · obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
    all_goals try omega
    · exact (tape_sender h1 hi hb hs).elim
    · exact (tape_sender h2 hi hb hs).elim

theorem getD_big {b t : Nat} (h : 9 ≤ t) : NoSend (m5t1Air.tables.getD t default) b = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [m5t1Air]; omega)]; rfl

theorem noSend_sch : ∀ t, t ≠ 2 → NoSend (m5t1Air.tables.getD t default) B_SCH = true := by
  intro t hne
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  all_goals first | decide +kernel | exact absurd rfl hne | exact getD_big (by omega)
end

/-! ## Interaction messages of plain columns -/

theorem msgVal_cols {tr : Trace Fp} {pub : List Fp} (t r n : Nat) :
    ((List.range n).map fun j => Expr.col j false).map (fun e => e.eval tr t r pub) =
      (List.range n).map fun j => tr.cell t r j := by
  rw [List.map_map]; rfl

theorem msg_sch_cols : (schFields.map fun f => Msg.c f) = (List.range 23).map fun j => Expr.col j false := by
  decide +kernel

theorem scht_e_cols : ((List.range Scht.NE).map fun j => Scht.T.c "e" j) =
    (List.range 23).map fun j => Expr.col j false := by
  decide +kernel

theorem padSeg_mem : Scht.padSeg ∈ schema := by decide +kernel

theorem getD_mem (i : Nat) : schema.getD i Scht.padSeg ∈ schema := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < schema.length
  · rw [List.getElem?_eq_getElem h]; exact List.getElem_mem h
  · rw [List.getElem?_eq_none (by omega)]; exact padSeg_mem

/-! ## `sch_row` -/

section
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}

theorem eval_one {t r : Nat} : (1 : Expr).eval tr t r pub = 1 := rfl

/-- **Every `MSG` row's descriptor is a schema entry.** -/
theorem sch_row (H : Holds (fullAir tape xtape) pub tr) (hS : SchtFixed tr)
    (h1 : NoSendOn B_SCH tape) (h2 : NoSendOn B_SCH xtape) {r : Nat} (hr : r < tr.height 3) :
    ∃ g ∈ schema, desc tr r = g.msg := by
  have hi : rcv B_SCH 1 (schFields.map fun f => Msg.c f) ∈ ((fullAir tape xtape).tables[3]'msg_lt).interactions :=
    List.mem_cons_self ..
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, -⟩ :=
    recv_sender H msg_lt hr hi rfl (by rw [multNat_one eval_one]; decide)
  have h2' := sender_idx noSend_sch h1 h2 ht' hi' hb' hs'
  subst h2'
  have hi1 : i' = sndBits B_SCH ((List.range Scht.NBITS).map fun b => Scht.T.c "m" b)
      ((List.range Scht.NE).map fun j => Scht.T.c "e" j) := List.mem_singleton.1 hi'
  subst hi1
  refine ⟨schema.getD r' Scht.padSeg, getD_mem r', ?_⟩
  have e1 : desc tr r = ((rcv B_SCH 1 (schFields.map fun f => Msg.c f)).msgVal tr 3 r pub).map Fp.toNat := by
    simp only [Interaction.msgVal, rcv, msg_sch_cols, desc, List.map_map]; rfl
  rw [e1, ← hmv]
  simp only [Interaction.msgVal, sndBits, scht_e_cols, List.map_map]
  exact hS r' hr'
end

/-! ## The descriptor columns of a row -/

/-- The descriptor columns of `MSG` row `r` are the fields of entry `g`. -/
structure Desc (tr : Trace Fp) (pub : List Fp) (r : Nat) (g : Seg) : Prop where
  mt : V tr pub r "mt" = g.mt
  s : V tr pub r "s" = g.s
  act : V tr pub r "act" = b2n (g.kind != K_PAD)
  kC : V tr pub r "kC" = b2n (g.kind == K_C)
  kD : V tr pub r "kD" = b2n (g.kind == K_D)
  kU : V tr pub r "kU" = b2n (g.kind == K_U)
  kUV : V tr pub r "kUV" = b2n (g.kind == K_UV)
  kLP : V tr pub r "kLP" = b2n (g.kind == K_LP)
  kLE : V tr pub r "kLE" = b2n (g.kind == K_LE)
  kCNT : V tr pub r "kCNT" = b2n (g.kind == K_CNT)
  var : V tr pub r "var" = b2n g.var
  fid : V tr pub r "fid" = g.fid
  fixL : V tr pub r "fixL" = g.fixL
  cv : V tr pub r "cv" = g.cv
  nextS : V tr pub r "nextS" = g.nextS
  skipS : V tr pub r "skipS" = g.skipS
  endOK : V tr pub r "endOK" = b2n g.endOK
  cont : V tr pub r "cont" = b2n g.cont
  newR : V tr pub r "newR" = b2n g.newR
  skipEnd : V tr pub r "skipEnd" = b2n g.skipEnd
  hsh : V tr pub r "hsh" = b2n (mflags g.mt).1
  hb : V tr pub r "hb" = b2n (mflags g.mt).2.1
  hbr : V tr pub r "hbr" = b2n (mflags g.mt).2.2

theorem range23 : List.range 23 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22] := rfl

theorem desc_of {tr : Trace Fp} {pub : List Fp} {r : Nat} {g : Seg} (h : desc tr r = g.msg) :
    Desc tr pub r g := by
  simp only [desc, range23, List.map_cons, List.map_nil, Seg.msg] at h
  generalize hm : mflags g.mt = m at h
  obtain ⟨a, b, c⟩ := m
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩ := h
  exact
    { mt := (V_eq (by decide) r).trans h0, s := (V_eq (by decide) r).trans h1,
      act := (V_eq (by decide) r).trans h2, kC := (V_eq (by decide) r).trans h3,
      kD := (V_eq (by decide) r).trans h4, kU := (V_eq (by decide) r).trans h5,
      kUV := (V_eq (by decide) r).trans h6, kLP := (V_eq (by decide) r).trans h7,
      kLE := (V_eq (by decide) r).trans h8, kCNT := (V_eq (by decide) r).trans h9,
      var := (V_eq (by decide) r).trans h10, fid := (V_eq (by decide) r).trans h11,
      fixL := (V_eq (by decide) r).trans h12, cv := (V_eq (by decide) r).trans h13,
      nextS := (V_eq (by decide) r).trans h14, skipS := (V_eq (by decide) r).trans h15,
      endOK := (V_eq (by decide) r).trans h16, cont := (V_eq (by decide) r).trans h17,
      newR := (V_eq (by decide) r).trans h18, skipEnd := (V_eq (by decide) r).trans h19,
      hsh := (V_eq (c := 20) (by decide) r).trans (by rw [h20, hm]),
      hb := (V_eq (c := 21) (by decide) r).trans (by rw [h21, hm]),
      hbr := (V_eq (c := 22) (by decide) r).trans (by rw [h22, hm]) }

/-! ## `segAt` of a schema entry -/

theorem find_key {l : List Seg} (hn : (l.map fun g => (g.mt, g.s)).Nodup) {g : Seg} (hg : g ∈ l) :
    l.find? (fun x => x.mt == g.mt && x.s == g.s) = some g := by
  induction l with
  | nil => simp at hg
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [List.find?_cons]
    rcases List.mem_cons.1 hg with rfl | hg'
    · simp
    · by_cases hk : a.mt = g.mt ∧ a.s = g.s
      · exact absurd ⟨g, hg', by rw [hk.1, hk.2]⟩ hn.1
      · have : (a.mt == g.mt && a.s == g.s) = false := by
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; omega
        rw [this]; exact ih hn.2 hg'

theorem segAt_of_mem {g : Seg} (hg : g ∈ schema) : segAt g.mt g.s = some g := by
  have hn : (schema.map fun g => (g.mt, g.s)).Nodup := of_decide_eq_true schemaKeysNodup_true
  exact find_key hn hg

/-! ## Schema facts the row lemma uses (decidable) -/

/-- Constants are one fixed byte; length kinds are four fixed bytes. -/
def schemaShape : Bool := schema.all fun g =>
  (g.kind != K_C || (!g.var && g.fixL == 1)) && (!g.isLen || (!g.var && g.fixL == 4))

theorem schemaShape_true : schemaShape = true := by decide +kernel

theorem shape_of_mem {g : Seg} (hg : g ∈ schema) :
    (g.kind = K_C → g.var = false ∧ g.fixL = 1) ∧ (g.isLen = true → g.var = false ∧ g.fixL = 4) := by
  have := List.all_eq_true.1 schemaShape_true g hg
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    beq_iff_eq] at this
  constructor
  · intro hk; rcases this.1 with h | h
    · exact absurd hk h
    · exact h
  · intro hk; rcases this.2 with h | h
    · rw [hk] at h; cases h
    · exact h

/-- Every descriptor value is a field element (`< p`): `SchtFixed` is satisfiable. -/
def schemaSmall : Bool := schema.all fun g => g.msg.all fun v => decide (v < 2013265921)

theorem schemaSmall_true : schemaSmall = true := by decide +kernel

end M5T1.MsgRow
