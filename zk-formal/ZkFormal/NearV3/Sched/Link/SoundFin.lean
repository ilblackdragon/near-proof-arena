import ZkFormal.NearV3.Sched.Link.SoundPre

/-!
# ZkFormal.NearV3.Sched.Link.SoundFin — final memory values (stage D step 2)

The memory sends `SFIN (addr, v, w)` on the last row of every segment (`lst = 1`). For instance τ
(process key block `f`, `MemCtx`):

* **`stAt_end`**: the simulation after all entry slots, `stAt 2^29`, has the arrays of the spec's
  final process state `stF = specSt … m` (every slot is at a time `< T0 + height ≤ 2^29`);
* **`fin_val`**: the last row of the segment of a τ-address `a` holds `simσ 2^29 a`: either the
  segment is its `INIT` row (no op on `a`, the frame keeps the `INIT` value), or the last row is
  the op on `a` with the largest time (`StepOk` writes `simσ (t + 1) a`, the frame keeps it);
* **`fin_link`** / `fin_snd` / `fin_rcv`: hence the final value of link `l` is
  `stF.allowance[l]`, of sender / receiver budget `x` is `stF.senderBudget[x]` /
  `stF.receiverBudget[x]`;
* **`codec_afin`**: the codec's `afin` of record `k` (received on `SFIN`, whose only sender is the
  memory) is `stF.allowance[k]`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd f m : Nat}
  {P : InstPub} {allowed : Array Bool} {st : St}

namespace MemCtx
variable (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
include C

/-- Rounds end by the last round's end. -/
theorem rounds_end : ∀ d i, i + d + 1 = m →
    cv tr tp (Proc.hdrAt tr tp f i) Proc.T + cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr ≤
      cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr
  | 0, i, h => by rw [show m - 1 = i by omega]; exact Nat.le_refl _
  | d + 1, i, h => by
    have ih := rounds_end d (i + 1) (by omega)
    rw [(C.I.chain i (by omega)).1] at ih
    omega

/-- No entry slot at or after the end time. -/
theorem entAt_after {t : Nat} (h0 : 0 < m)
    (ht : cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr ≤ t) :
    entAt tr tp f m t = none := by
  cases he : entAt tr tp f m t with
  | none => rfl
  | some p =>
    obtain ⟨i, j⟩ := p
    obtain ⟨hi, hj, hT⟩ := entAt_some he
    have := C.rounds_end (m - 1 - i) i (by omega)
    omega

theorem stAt_from {E : Nat} (hE : ∀ t, E ≤ t → entAt tr tp f m t = none) :
    ∀ d, stAt P.n allowed tr tp f m st (E + d) = stAt P.n allowed tr tp f m st E
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc, stAt_none _ _ _ _ _ _ _ (hE _ (by omega)), stAt_from hE d]

/-- **The simulation after all slots is the spec's final process state.** -/
theorem stAt_end :
    Arr (stAt P.n allowed tr tp f m st (2 ^ 29)) = Arr (specSt P.n allowed (reqsOf P) tr tp f st m) := by
  have hHt := C.hHt
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    have hnone : ∀ t, 0 ≤ t → entAt tr tp f 0 t = none := by
      intro t _
      cases he : entAt tr tp f 0 t with
      | none => rfl
      | some p => obtain ⟨i, j⟩ := p; exact absurd (entAt_some he).1 (Nat.not_lt_zero _)
    have := C.stAt_from hnone (2 ^ 29)
    rw [Nat.zero_add] at this
    rw [this]; rfl
  · have hlt := (C.I.hdr (m - 1) (by omega)).2
    have hT0 : T0 = 1048576 := rfl
    have hA := stAt_slot (n := P.n) (allowed := allowed) (reqs := reqsOf P) (st := st) C.hL C.hHt C.I
      (fun i hi j hj => by
        obtain ⟨⟨rest, h1, -⟩, h2, -⟩ := entry_inc C.hH C.O C.OS C.SP C.PO C.I rfl hi hj
        exact ⟨⟨rest, h1⟩, h2⟩) (m - 1) (by omega) _ (Nat.le_refl _)
    have hs := C.stAt_from (fun t ht => C.entAt_after h0 ht)
      (2 ^ 29 - (cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr))
    rw [show cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr +
      (2 ^ 29 - (cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.T + cv tr tp (Proc.hdrAt tr tp f (m - 1)) Proc.Lr)) =
      2 ^ 29 by omega] at hs
    rw [hs, hA, show m = m - 1 + 1 by omega, specSt_succ, show m - 1 + 1 - 1 = m - 1 by omega]

/-- **The last row of a τ-address segment holds the final simulated value.** -/
theorem fin_val {r : Nat} (hr : r < tr.height tm) (hl : cv tr tm r Mem.lst = 1)
    (hq : QT (cv tr tp f Proc.tau) P.n (cv tr tm r Mem.addr) = true) :
    cv tr tm r Mem.v =
      simσ (cv tr tp f Proc.tau) P.n allowed tr tp f m st (2 ^ 29) (cv tr tm r Mem.addr) := by
  have hM := C.hM
  have hn := C.PO.n64
  have hI := initOnce_of C.hτ hn C.hV
  have hT := mem_timeQ C.hH C.O C.OS C.OO C.PS C.htau C.hf C.hk C.hc C.I C.SP C.PO hn
  have huniq := mem_seg_uniqueQ C.hH C.O.mem hI
  have ha : cv tr tm r Mem.act = 1 := by
    have F := Mem.row_flags hM hr; omega
  obtain ⟨f0, hf0r, hff0, hact, hrest⟩ := Mem.seg_of hM hr ha
  have hf0 : f0 < tr.height tm := by omega
  have ea : cv tr tm r Mem.addr = cv tr tm f0 Mem.addr := (hact r hf0r (Nat.le_refl _)).2
  have hq0 : QT (cv tr tp f Proc.tau) P.n (cv tr tm f0 Mem.addr) = true := by rw [← ea]; exact hq
  -- every op row on the address lies in `(f0, r]`
  have inseg : ∀ r', r' < tr.height tm → cv tr tm r' Mem.act = 1 → cv tr tm r' Mem.fst = 0 →
      cv tr tm r' Mem.addr = cv tr tm r Mem.addr → f0 < r' ∧ r' ≤ r := by
    intro r' hr' ha' hf' he
    obtain ⟨f1, hf1, hff1, hact1, hrest1⟩ := Mem.seg_of hM hr' ha'
    have e1 : cv tr tm r' Mem.addr = cv tr tm f1 Mem.addr := (hact1 r' hf1 (Nat.le_refl _)).2
    have e : f1 = f0 := huniq f1 f0 (by omega) hf0 hff1 hff0 (by rw [← e1, he]; exact hq)
      (by rw [← e1, he, ea])
    rw [e] at hf1 hrest1
    have hlt : f0 < r' := by
      rcases Nat.lt_or_ge f0 r' with h | h
      · exact h
      · have : f0 = r' := by omega
        rw [← this] at hf'; omega
    refine ⟨hlt, Nat.le_of_not_lt fun hrr => ?_⟩
    have := (hrest1 (r + 1) (by omega) (by omega)).2
    rw [Nat.add_sub_cancel] at this
    omega
  have hσ0 : simσ (cv tr tp f Proc.tau) P.n allowed tr tp f m st 0 (cv tr tm r Mem.addr) =
      memInit tr tm (cv tr tm r Mem.addr) := by
    unfold simσ
    rw [if_pos hq]
    exact (memInit_tau C.hH C.O.mem C.hτ hn C.hB C.hV hq).symm
  rcases Nat.eq_or_lt_of_le hf0r with e | hlt
  · -- the segment is its `INIT` row
    rw [e] at hff0
    have hv : memInit tr tm (cv tr tm r Mem.addr) = cv tr tm r Mem.v :=
      memInit_eqQ huniq hr hff0 hq
    have hfr := frame_iter _ _ C.frame (cv tr tm r Mem.addr) (2 ^ 29) 0 (fun o ho hoa _ => by
      obtain ⟨r', hr', ha', hf', rfl⟩ := mem_memOps (mem_memOpsQ.1 ho).1
      have := inseg r' hr' ha' hf' hoa
      omega)
    rw [Nat.zero_add] at hfr
    rw [hfr, hσ0, hv]
  · -- the last row is the latest op on the address
    have hfr0 : cv tr tm r Mem.fst = 0 := (hrest r hlt (Nat.le_refl _)).1
    have ho : (⟨cv tr tm r Mem.addr, cv tr tm r Mem.t, cv tr tm r Mem.vin, cv tr tm r Mem.v⟩ : MOp) ∈
        memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n) :=
      mem_memOpsQ.2 ⟨memOps_mem hr ha hfr0, hq⟩
    have hstep := C.step_ok (cv tr tm r Mem.t) (fun o2 ho2 h2 => by
      have := C.mem_reads o2 ho2; rw [h2] at this; exact this) _ ho rfl
    simp only at hstep
    have htr := hT r hr ha hq
    have hmono := mem_seg_timeQ C.hH C.O.mem C.O.cmp hT hr (fun x h1 h2 => (hact x h1 h2).1)
      (fun x h1 h2 => (hrest x h1 h2).1)
      (fun x h1 h2 => by rw [(hact x h1 h2).2, ← ea]; exact hq)
    have hfr := frame_iter _ _ C.frame (cv tr tm r Mem.addr) (2 ^ 29 - (cv tr tm r Mem.t + 1))
      (cv tr tm r Mem.t + 1) (fun o ho' hoa hin => by
        obtain ⟨r', hr', ha', hf', rfl⟩ := mem_memOps (mem_memOpsQ.1 ho').1
        simp only at hoa hin
        obtain ⟨h1, h2⟩ := inseg r' hr' ha' hf' hoa
        rcases Nat.eq_or_lt_of_le h2 with e | e
        · rw [e] at hin; omega
        · have := hmono r' r (by omega) e (Nat.le_refl _); omega)
    rw [show cv tr tm r Mem.t + 1 + (2 ^ 29 - (cv tr tm r Mem.t + 1)) = 2 ^ 29 by omega] at hfr
    rw [hfr, hstep]

/-- **Final link allowance.** -/
theorem fin_link {r l : Nat} (hr : r < tr.height tm) (hl : cv tr tm r Mem.lst = 1) (hll : l < P.n * P.n)
    (ha : cv tr tm r Mem.addr = addrOf (cv tr tp f Proc.tau) 0 l) :
    cv tr tm r Mem.v = (specSt P.n allowed (reqsOf P) tr tp f st m).allowance[l]! := by
  have hn := C.PO.n64
  rw [C.fin_val hr hl (by rw [ha]; exact QT_link hn hll), ha]
  unfold simσ
  rw [if_pos (QT_link hn hll), rd_link _ hn hll]
  have := C.stAt_end
  simp only [Arr, Prod.mk.injEq] at this
  rw [this.2.2]

/-- **Final sender budget.** -/
theorem fin_snd {r x : Nat} (hr : r < tr.height tm) (hl : cv tr tm r Mem.lst = 1) (hx : x < P.n)
    (ha : cv tr tm r Mem.addr = addrOf (cv tr tp f Proc.tau) 1 x) :
    cv tr tm r Mem.v = (specSt P.n allowed (reqsOf P) tr tp f st m).senderBudget[x]! := by
  have hn := C.PO.n64
  rw [C.fin_val hr hl (by rw [ha]; exact QT_snd hn hx), ha]
  unfold simσ
  rw [if_pos (QT_snd hn hx), rd_snd _ hn hx]
  have := C.stAt_end
  simp only [Arr, Prod.mk.injEq] at this
  rw [this.1]

/-- **Final receiver budget.** -/
theorem fin_rcv {r x : Nat} (hr : r < tr.height tm) (hl : cv tr tm r Mem.lst = 1) (hx : x < P.n)
    (ha : cv tr tm r Mem.addr = addrOf (cv tr tp f Proc.tau) 2 x) :
    cv tr tm r Mem.v = (specSt P.n allowed (reqsOf P) tr tp f st m).receiverBudget[x]! := by
  have hn := C.PO.n64
  rw [C.fin_val hr hl (by rw [ha]; exact QT_rcv hn hx), ha]
  unfold simσ
  rw [if_pos (QT_rcv hn hx), rd_rcv _ hn hx]
  have := C.stAt_end
  simp only [Arr, Prod.mk.injEq] at this
  rw [this.2.1]

end MemCtx

/-! ## The codec's final allowances -/

theorem mem_fin_i {i : Interaction} (hi : i ∈ Mem.interactions) (hb : i.bus = B_SFIN) (hs : i.send = true) :
    i = Mem.iFin := by
  rw [Mem.interactions_eq] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e <;> subst e <;>
    simp_all [Mem.iOp, Mem.iFin, Mem.iTime, Mem.iSf, B_SOP, B_SFIN, B_SCMP]

/-- **A received `SFIN` message is sent by a last memory row.** -/
theorem fin_src (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {t r : Nat} (ht : t < AP.tables.length)
    (hr : r < tr.height t) {i : Interaction} (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = B_SFIN)
    (hs : i.send = false) (hm : i.multNat tr t r pub ≠ 0) :
    ∃ r', r' < tr.height tm ∧ cv tr tm r' Mem.lst = 1 ∧
      i.msgVal tr t r pub = [tr.cell tm r' Mem.addr, tr.cell tm r' Mem.v, tr.cell tm r' Mem.w] := by
  rcases recv_src hH ht hr hi hb hs hm with hp | ⟨t', ht', r', hr', i', hi', hb', hs', hmsg, hm'⟩
  · exact absurd (pubCount_zero (s := true) (fun seg h1 h2 => absurd h2 (hM.pubFin seg h1)) _) hp
  · have htm : t' = tm := Classical.byContradiction fun hne => by
      have := hM.fin t' ht' hne i' hi' hb'; rw [this] at hs'; cases hs'
    rw [htm] at hi' hm' hmsg hr'
    rw [hM.tab] at hi'
    have e := mem_fin_i hi' hb' hs'
    subst e
    rw [Mem.multNat_c rfl] at hm'
    refine ⟨r', hr', ?_, ?_⟩
    · by_cases h : cv tr tm r' Mem.lst = 1
      · exact h
      · simp [h] at hm'
    · rw [← hmsg]; rfl

/-- **The codec's final allowance of record `k` is the spec's final allowance.** -/
theorem codec_afin (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
    (O : CodecValOwn AP tcd) {fc : Nat} (hfc : fc < tr.height tcd) (hF : cv tr tcd fc Codec.kF = 1)
    (hτ : cv tr tcd fc Codec.tau = cv tr tp f Proc.tau) (hNN : cv tr tcd fc Codec.NN = P.n * P.n)
    {k : Nat} (hk : k < P.n * P.n) :
    cv tr tcd (fc + 5 + 24 * k + 23) Codec.afin = (specSt P.n allowed (reqsOf P) tr tp f st m).allowance[k]! := by
  have hL := codec_local C.hH O
  have hH22 := codec_h22 C.hH O
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hfc hF
  have hkN : k < cv tr tcd fc Codec.NN := by rw [hNN]; exact hk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, m11, msg11, -⟩ := Codec.codec_rec_msgs hL (RR k hkN) (RS k hkN)
  have hw : fc + 5 + 24 * k + 23 < tr.height tcd := (RR k hkN 23 (by omega)).1
  obtain ⟨r, hr, hl, hmsg⟩ := fin_src C.hH C.O.mem O.lt hw (by rw [O.tab]; exact codec_mem 11 (by decide))
    (by rw [Codec.i11_def]) (by rw [Codec.i11_def]) (by rw [m11]; exact Nat.one_ne_zero)
  rw [msg11] at hmsg
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨e1, e2, -⟩ := hmsg
  have hτ' := C.hτ
  have hn := C.PO.n64
  have hkk : k < 4096 := by have := Nat.mul_le_mul hn hn; omega
  have ha : cv tr tm r Mem.addr = addrOf (cv tr tp f Proc.tau) 0 k := by
    show (tr.cell tm r Mem.addr).toNat = _
    rw [← e1, toNat_ofNat_lt' (by omega)]; unfold addrOf; rw [← hτ]; omega
  have hv : cv tr tm r Mem.v = cv tr tcd (fc + 5 + 24 * k + 23) Codec.afin := by
    show (tr.cell tm r Mem.v).toNat = _
    rw [← e2, toNat_ofNat_lt' (cv_lt _ _)]
  rw [← hv]
  exact C.fin_link hr hl hk ha

end

end ZkFormal.NearV3.Sched
