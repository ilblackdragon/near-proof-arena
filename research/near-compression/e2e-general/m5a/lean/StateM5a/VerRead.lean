import StateM5a.VerDec

/-!
# StateM5a.VerRead — every part a `BR` row reads on `VER` is a `BR` row's publication

**`br_rd_part`**: a `BR` row with `gold − gsha = 1` (it reads its old node on `VER`) receives, for
each part `p < 17`, the message `(VT_BR, p, oref, ho₁₆, payload_p)`; by `VER` balance it was sent,
and the only sender with tag `VT_BR` is a `BR` row `r'` publishing either its old record (`gsha`,
ref flag `0`, ref `ho`) or its new record (`gnew`, ref flag `nref`, ref `hn`), part `p`.
-/

namespace StateM5a.VerRead

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.VerBus StateM5a.VerDec StateM5a.KeyDecode

set_option maxRecDepth 100000

/-- Message expressions of part `p`: read, old publication, new publication. -/
def rdE (p : Nat) : List Expr :=
  [K VT_BR, K p, Br.c "oref"] ++ (pack2 fun b => Br.c "ho" b) ++
    brPay (fun i => Br.c "f" i) (fun i => Br.c "isn" i) Br.ch (Br.c "hasv") (fun t => Br.c "vl" t)
      (fun t => Br.c "vh" t) Br.M p
def oldE (p : Nat) : List Expr :=
  [K VT_BR, K p, 0] ++ (pack2 fun b => Br.c "ho" b) ++
    brPay (fun i => Br.c "f" i) (fun i => Br.c "isn" i) Br.ch (Br.c "hasv") (fun t => Br.c "vl" t)
      (fun t => Br.c "vh" t) Br.M p
def newE (p : Nat) : List Expr :=
  [K VT_BR, K p, Br.c "nref"] ++ (pack2 fun b => Br.c "hn" b) ++
    brPay (fun i => Br.c "nf" i) Br.nisn Br.newch (Br.c "nhv") (fun t => Br.c "nvl" t)
      (fun t => Br.c "nvh" t) Br.NM p

theorem rd_get (p : Nat) (hp : p < 17) : brRcvParts[p]? = some (rdE p) := by
  unfold brRcvParts rdE; rw [brRec_get _ _ _ _ _ _ _ _ _ p hp]
theorem old_get (p : Nat) (hp : p < 17) : brOldParts[p]? = some (oldE p) := by
  unfold brOldParts oldE; rw [brRec_get _ _ _ _ _ _ _ _ _ p hp]
theorem new_get (p : Nat) (hp : p < 17) : brNewParts[p]? = some (newE p) := by
  unfold brNewParts newE; rw [brRec_get _ _ _ _ _ _ _ _ _ p hp]

theorem parts_len : brOldParts.length = 17 ∧ brNewParts.length = 17 ∧ brRcvParts.length = 17 := by
  simp [brOldParts, brNewParts, brRcvParts, Br.rec]


/-- **Every `BR` publication on `VER` carries the tag `VT_BR`** (for the `SN` readers). -/
theorem br_ver_head : ∀ i ∈ Br.interactions, i.bus = B_VER → i.send = true → i.msg.head? = some (K VT_BR) := by
  intro i hi hb hs
  have : i ∈ Br.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) :=
    List.mem_filter.2 ⟨hi, by simp [hb, hs]⟩
  rw [br_ver_filter] at this
  rcases List.mem_append.1 this with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
    have := old_get q (by have := parts_len.1; omega)
    rw [List.getElem?_eq_getElem hq] at this
    rw [Option.some.inj this]; rfl
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
    have := new_get q (by have := parts_len.2.1; omega)
    rw [List.getElem?_eq_getElem hq] at this
    rw [Option.some.inj this]; rfl

theorem fp_one_ne_two : (Fp.ofNat 1 : Fp) ≠ Fp.ofNat 2 := by decide

section
variable {tr : Trace Fp} {pub : List Fp}

/-- `K n` evaluates to `n` (`n < P`). -/
theorem evK (t r : Nat) (n : Nat) (h : n < 2013265921) : ((K n).eval tr t r pub).toNat = n := by
  show (Fp.ofNat n).toNat = n
  rw [Fp.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- **Who published a part read by a `BR` row.** -/
theorem br_rd_part {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) {r : Nat} (hr : r < tr.height 2)
    (hg : (Br.gold - Br.c "gsha").eval tr 2 r pub = 1) (p : Nat) (hp : p < 17) :
    ∃ r', r' < tr.height 2 ∧
      ((ev tr 2 r' pub (Br.c "gsha") = 1 ∧ (rdE p).map (E tr 2 r pub) = (oldE p).map (E tr 2 r' pub)) ∨
       (ev tr 2 r' pub (Br.c "gnew") = 1 ∧ (rdE p).map (E tr 2 r pub) = (newE p).map (E tr 2 r' pub))) := by
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hT2 : (fullAir D extra nb np).tables[2] = Br.table := by
    rw [fullAir_get (by simp [m5aAir]) h2]; rfl
  -- the read interaction
  have hrd : rcv B_VER (Br.gold - Br.c "gsha") (rdE p) ∈ Br.interactions := by
    have : rcv B_VER (Br.gold - Br.c "gsha") (rdE p) ∈
        Br.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = false)) := by
      rw [br_ver_rfilter]
      exact List.mem_map.2 ⟨rdE p, List.mem_of_getElem? (rd_get p hp), rfl⟩
    exact (List.mem_filter.1 this).1
  have hm := msg_mem_busList h2 (by rw [hT2]; exact hrd) hr (g := Br.gold - Br.c "gsha") rfl hg
  have hs := recv_sent hH hm
  obtain ⟨t, ht, r', hr', i, hi, hb, hsd, hpos, hmsg⟩ := mem_busList.1 hs
  simp only [rcv] at hb hmsg
  have hmsg' : (rdE p).map (E tr 2 r pub) = i.msgVal tr t r' pub := hmsg
  -- the head of the message is `VT_BR`
  have hhead : ((rdE p).map (E tr 2 r pub)).head? = some (Fp.ofNat 1) := by
    simp [rdE, E, eval_K, VT_BR]; rfl
  by_cases ht12 : t < 12
  · by_cases t2 : t = 2
    · subst t2
      rw [hT2] at hi
      have hf : i ∈ Br.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) :=
        List.mem_filter.2 ⟨hi, by simp [hb, hsd]⟩
      rw [br_ver_filter] at hf
      have hc := tbl_br D extra nb np hH r' (List.mem_range.2 hr')
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hf
        obtain ⟨q, hq, hq'⟩ := List.getElem_of_mem hm'
        have hq17 : q < 17 := by have := parts_len.1; omega
        have em : m = oldE q := by
          have := old_get q hq17; rw [List.getElem?_eq_getElem hq] at this; rw [← hq']; exact Option.some.inj this
        subst em
        obtain ⟨b, hbm, hb1⟩ := multNat_pos _ hpos
        simp only [sndBits, Br.bitsOf, List.mem_map, List.mem_range] at hbm
        obtain ⟨k, hk, rfl⟩ := hbm
        have hgs := FieldVer.br_vm_gsha hc k hk (eval_one_ev hb1)
        -- the part index
        have hpq : p = q := by
          have e1 := congrArg (fun l => (l.getD 1 0).toNat) hmsg'
          simp only [rdE, oldE, Interaction.msgVal, sndBits, List.map_append, List.map_cons, List.cons_append,
            List.getD_cons_succ, List.getD_cons_zero] at e1
          rw [evK 2 r p (by omega), evK 2 r' q (by omega)] at e1
          exact e1
        subst hpq
        exact ⟨r', hr', Or.inl ⟨hgs, hmsg'⟩⟩
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hf
        obtain ⟨q, hq, hq'⟩ := List.getElem_of_mem hm'
        have hq17 : q < 17 := by have := parts_len.2.1; omega
        have em : m = newE q := by
          have := new_get q hq17; rw [List.getElem?_eq_getElem hq] at this; rw [← hq']; exact Option.some.inj this
        subst em
        obtain ⟨b, hbm, hb1⟩ := multNat_pos _ hpos
        simp only [sndBits, Br.bitsOf, List.mem_map, List.mem_range] at hbm
        obtain ⟨k, hk, rfl⟩ := hbm
        have hgn := FieldVer.br_vmn_gnew hc k hk (eval_one_ev hb1)
        have hpq : p = q := by
          have e1 := congrArg (fun l => (l.getD 1 0).toNat) hmsg'
          simp only [rdE, newE, Interaction.msgVal, sndBits, List.map_append, List.map_cons, List.cons_append,
            List.getD_cons_succ, List.getD_cons_zero] at e1
          rw [evK 2 r p (by omega), evK 2 r' q (by omega)] at e1
          exact e1
        subst hpq
        exact ⟨r', hr', Or.inr ⟨hgn, hmsg'⟩⟩
    · by_cases t3 : t = 3
      · subst t3
        have hT3 : (fullAir D extra nb np).tables[3] = Sn.table := by
          rw [fullAir_get (by simp [m5aAir]) ht]; rfl
        rw [hT3] at hi
        have h1 := sn_ver_head i hi hb hsd
        exfalso
        have e2 : (i.msgVal tr 3 r' pub).head? = some (Fp.ofNat 2) := by
          simp only [Interaction.msgVal, List.head?_map, h1, Option.map_some]
          rfl
        rw [← hmsg', hhead] at e2
        exact fp_one_ne_two (Option.some.inj e2)
      · exfalso
        have := ver_nosend D t ht12 t2 t3
        rw [← WsDecode.full_get t ht12 (extra := extra) (nb := nb) (np := np),
          getElem!_pos _ t ht] at this
        exact not_sends this hi hb hsd
  · exfalso
    have hmem : (fullAir D extra nb np).tables[t] ∈ extra := by
      simp only [fullAir]
      rw [List.getElem_append_right (by simp [m5aAir]; omega)]
      exact List.getElem_mem ..
    exact not_sends (hxV _ hmem) hi hb hsd

end

end StateM5a.VerRead
