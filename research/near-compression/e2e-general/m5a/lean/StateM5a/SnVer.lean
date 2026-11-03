import StateM5a.SnRec

/-!
# StateM5a.SnVer — every part an `SN` row reads on `VER` is an `SN` row's publication

An `SN` record on `VER` is 3 parts (`Sn.rec`): part 0 `(isL, klen, payload ref flag, 36 payload
bytes, memory limbs)`, parts 1 / 2 the key nibbles `0..31` / `32..63`.

**`sn_rd_part`**: an `SN` row with `gold − gsha = 1` (it reads its old node on `VER`) receives, for
each part `p < 3`, `(VT_SN, p, oref, ho₁₆, payload_p)`; by `VER` balance it was sent, and the only
senders with tag `VT_SN` are `SN` rows `r'` publishing their old record (`gsha`, ref flag `0`, ref
`ho`) or their new record (`gnew`, ref flag `nref`, ref `hn`), part `p`.
-/

namespace StateM5a.SnVer

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.VerBus StateM5a.VerDec StateM5a.VerRead StateM5a.KeyDecode StateM5a.FieldRows

set_option maxRecDepth 100000

def snOldParts : List (List Expr) := Sn.rec 0 (pack2 fun b => Sn.c "ho" b) (Sn.c "xf") (fun t => Sn.c "x" t) Sn.M
def snNewParts : List (List Expr) :=
  Sn.rec (Sn.c "nref") (pack2 fun b => Sn.c "hn" b) (Sn.c "nxf") (fun t => Sn.c "nx" t) Sn.NM
def snRcvParts : List (List Expr) :=
  Sn.rec (Sn.c "oref") (pack2 fun b => Sn.c "ho" b) (Sn.c "xf") (fun t => Sn.c "x" t) Sn.M

theorem sn_ver_filter : Sn.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) =
    snOldParts.map (fun m => sndBits B_VER (Sn.bitsOf "vm") m) ++
      snNewParts.map (fun m => sndBits B_VER (Sn.bitsOf "vmn") m) := by
  simp only [snOldParts, snNewParts]; filt

theorem sn_ver_rfilter : Sn.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = false)) =
    snRcvParts.map (fun m => rcv B_VER (Sn.c "gold" - Sn.c "gsha") m) := by
  simp only [snRcvParts]; filt

/-- Part `p` as the reader / the old publisher / the new publisher send it. -/
def sRdE (p : Nat) : List Expr := snRcvParts.getD p []
def sOldE (p : Nat) : List Expr := snOldParts.getD p []
def sNewE (p : Nat) : List Expr := snNewParts.getD p []

theorem sparts_len : snOldParts.length = 3 ∧ snNewParts.length = 3 ∧ snRcvParts.length = 3 := by
  simp [snOldParts, snNewParts, snRcvParts, Sn.rec]

section
variable {tr : Trace Fp} {pub : List Fp} {t r : Nat}

theorem sn_vm_gsha (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Sn.c "vm" k) = 1) : ev tr t r pub (Sn.c "gsha") = 1 := by
  refine FieldVer.one_of_gate (hold (L := Sn.constraints) rfl hc ?_) hv
  unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem sn_vmn_gnew (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Sn.c "vmn" k) = 1) : ev tr t r pub (Sn.c "gnew") = 1 := by
  refine FieldVer.one_of_gate (hold (L := Sn.constraints) rfl hc ?_) hv
  unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem ev_mul_one_r {a b : Expr} (h : ev tr t r pub (a * b) = 0) (hb : ev tr t r pub b = 1) :
    ev tr t r pub a = 0 := by
  rw [ev_hmul, hb, Nat.mul_one, Nat.mod_eq_of_lt (ev_lt _)] at h; exact h

theorem sn_vm_cont (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Sn.c "vm" k) = 1) : ev tr t r pub (Sn.c "cont") = 0 := by
  refine ev_mul_one_r (hold (L := Sn.constraints) rfl hc ?_) hv
  unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem sn_vmn_cont (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (k : Nat) (hk : k < VBITS)
    (hv : ev tr t r pub (Sn.c "vmn" k) = 1) : ev tr t r pub (Sn.c "cont") = 0 := by
  refine ev_mul_one_r (hold (L := Sn.constraints) rfl hc ?_) hv
  unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

end

section
variable {tr : Trace Fp} {pub : List Fp}

set_option maxHeartbeats 4000000 in
/-- **Who published a part read by an `SN` row.** -/
theorem sn_rd_part {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) {r : Nat} (hr : r < tr.height 3)
    (hg : (Sn.c "gold" - Sn.c "gsha").eval tr 3 r pub = 1) (p : Nat) (hp : p < 3) :
    ∃ r', r' < tr.height 3 ∧ ev tr 3 r' pub (Sn.c "cont") = 0 ∧
      ((ev tr 3 r' pub (Sn.c "gsha") = 1 ∧ (sRdE p).map (E tr 3 r pub) = (sOldE p).map (E tr 3 r' pub)) ∨
       (ev tr 3 r' pub (Sn.c "gnew") = 1 ∧ (sRdE p).map (E tr 3 r pub) = (sNewE p).map (E tr 3 r' pub))) := by
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hT3 : (fullAir D extra nb np).tables[3] = Sn.table := by
    rw [fullAir_get (by simp [m5aAir]) h3]; rfl
  have hrd : rcv B_VER (Sn.c "gold" - Sn.c "gsha") (sRdE p) ∈ Sn.interactions := by
    have : rcv B_VER (Sn.c "gold" - Sn.c "gsha") (sRdE p) ∈
        Sn.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = false)) := by
      rw [sn_ver_rfilter]
      exact List.mem_map.2 ⟨sRdE p, by
        rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> simp [sRdE, snRcvParts, Sn.rec], rfl⟩
    exact (List.mem_filter.1 this).1
  have hm := msg_mem_busList h3 (by rw [hT3]; exact hrd) hr (g := Sn.c "gold" - Sn.c "gsha") rfl hg
  have hs := recv_sent hH hm
  obtain ⟨t, ht, r', hr', i, hi, hb, hsd, hpos, hmsg⟩ := mem_busList.1 hs
  simp only [rcv] at hb hmsg
  have hmsg' : (sRdE p).map (E tr 3 r pub) = i.msgVal tr t r' pub := hmsg
  have hhead : ((sRdE p).map (E tr 3 r pub)).head? = some (Fp.ofNat 2) := by
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;>
      simp [sRdE, snRcvParts, Sn.rec, E, eval_K, VT_SN] <;> rfl
  have hpart : ((sRdE p).map (E tr 3 r pub)).getD 1 0 = Fp.ofNat p := by
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;>
      simp [sRdE, snRcvParts, Sn.rec, E, eval_K] <;> rfl
  by_cases ht12 : t < 12
  · by_cases t3 : t = 3
    · subst t3
      rw [hT3] at hi
      have hf : i ∈ Sn.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) :=
        List.mem_filter.2 ⟨hi, by simp [hb, hsd]⟩
      rw [sn_ver_filter] at hf
      have hc := tbl_sn D extra nb np hH r' (List.mem_range.2 hr')
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hf
        obtain ⟨q, hq, hq'⟩ := List.getElem_of_mem hm'
        have hq3 : q < 3 := by have := sparts_len.1; omega
        obtain ⟨b, hbm, hb1⟩ := multNat_pos _ hpos
        simp only [sndBits, Sn.bitsOf, List.mem_map, List.mem_range] at hbm
        obtain ⟨k, hk, rfl⟩ := hbm
        have hgs := sn_vm_gsha hc k hk (eval_one_ev hb1)
        have hco := sn_vm_cont hc k hk (eval_one_ev hb1)
        have em : m = sOldE q := by
          simp only [sOldE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some, hq']
        subst em
        have hpq : p = q := by
          have e1 := congrArg (fun l => l.getD 1 0) hmsg'
          simp only [hpart] at e1
          have e2 : ((sOldE q).map (E tr 3 r' pub)).getD 1 0 = Fp.ofNat q := by
            rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl <;> rfl
          have e3 := congrArg Fp.toNat (e1.trans e2)
          rw [KeyDigest.ofNat_toNat', KeyDigest.ofNat_toNat'] at e3
          omega
        subst hpq
        exact ⟨r', hr', hco, Or.inl ⟨hgs, hmsg'⟩⟩
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hf
        obtain ⟨q, hq, hq'⟩ := List.getElem_of_mem hm'
        have hq3 : q < 3 := by have := sparts_len.2.1; omega
        obtain ⟨b, hbm, hb1⟩ := multNat_pos _ hpos
        simp only [sndBits, Sn.bitsOf, List.mem_map, List.mem_range] at hbm
        obtain ⟨k, hk, rfl⟩ := hbm
        have hgn := sn_vmn_gnew hc k hk (eval_one_ev hb1)
        have hco := sn_vmn_cont hc k hk (eval_one_ev hb1)
        have em : m = sNewE q := by
          simp only [sNewE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some, hq']
        subst em
        have hpq : p = q := by
          have e1 := congrArg (fun l => l.getD 1 0) hmsg'
          simp only [hpart] at e1
          have e2 : ((sNewE q).map (E tr 3 r' pub)).getD 1 0 = Fp.ofNat q := by
            show ((sNewE q).map (E tr 3 r' pub)).getD 1 0 = _
            rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl <;> rfl
          have e3 := congrArg Fp.toNat (e1.trans e2)
          rw [KeyDigest.ofNat_toNat', KeyDigest.ofNat_toNat'] at e3
          omega
        subst hpq
        exact ⟨r', hr', hco, Or.inr ⟨hgn, hmsg'⟩⟩
    · by_cases t2 : t = 2
      · subst t2
        have hT2 : (fullAir D extra nb np).tables[2] = Br.table := by
          rw [fullAir_get (by simp [m5aAir]) ht]; rfl
        rw [hT2] at hi
        have h1 := br_ver_head i hi hb hsd
        exfalso
        have e2 : (i.msgVal tr 2 r' pub).head? = some (Fp.ofNat 1) := by
          simp only [Interaction.msgVal, List.head?_map, h1, Option.map_some]
          rfl
        rw [← hmsg', hhead] at e2
        exact fp_one_ne_two (Option.some.inj e2).symm
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

end StateM5a.SnVer
