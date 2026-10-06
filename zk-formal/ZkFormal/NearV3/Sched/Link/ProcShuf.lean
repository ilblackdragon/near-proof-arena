import ZkFormal.NearV3.Sched.Link.ProcSim
import ZkFormal.Chacha.Statements

/-!
# ZkFormal.NearV3.Sched.Link.ProcShuf — the shuffle of each round (lane v3-chacha link)

* `latest_start`, **`entry_T`**: every entry row of `sprV3` lies in a round of the instance of
  the latest key block above it, so its round start `T` is in `[T0, T0 + height)`;
* `lid_inj`: the list ids `lidOf τ T = τ·2^22 + T` are injective for `τ < 256`,
  `T ∈ [T0, T0 + 2^22)`;
* **`entry_ident`**: an entry row sending / receiving with the list id of round `i` of instance
  `f` is entry `x` of that round;
* **`round_shuffle`**: with the shuffle tables of lane v3-chacha (`ShufOwn`: ownership of
  `SSHUF`, `SSIN`, `SSOUT` and of the lane's buses), round `i`'s entries shuffled with
  `rngAt key kq_i` give the round's shuffle outputs and `rngAt key kend_i`
  (`key = procKey`, the public key records' words);
* **`proc_sim`**: hence `simR … (roundsOf …) T0 st = some (specSt …, specPushes …)` when
  `st.rng = rngAt (procKey …) 0`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler

namespace Proc

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

def IsStart (tr : Trace Fp) (tp g : Nat) : Prop := cv tr tp g kK = 1 ∧ cv tr tp g kc = 0

theorem latest_start (hL : PLocal tr tp pub) :
    ∀ w, w < tr.height tp → cv tr tp w act = 1 →
      ∃ g, g ≤ w ∧ IsStart tr tp g ∧ ∀ g', g < g' → g' ≤ w → ¬ IsStart tr tp g' := by
  intro w
  induction w with
  | zero =>
    intro h0 ha
    obtain ⟨hc, -, hk⟩ := row_first hL h0
    exact ⟨0, Nat.le_refl _, ⟨hk ha, hc⟩, fun g' h1 h2 => by omega⟩
  | succ w ih =>
    intro hw1 ha1
    by_cases hs : IsStart tr tp (w + 1)
    · exact ⟨w + 1, Nat.le_refl _, hs, fun g' h1 h2 => by omega⟩
    · obtain ⟨g, hg, hgs, hlat⟩ := ih (by omega) (act_prev hL hw1 ha1)
      refine ⟨g, by omega, hgs, fun g' h1 h2 => ?_⟩
      rcases Nat.lt_or_ge g' (w + 1) with h | h
      · exact hlat g' h1 (by omega)
      · rw [show g' = w + 1 by omega]; exact hs

/-- **The round start of an entry row** is in `[T0, T0 + height)`. -/
theorem entry_T (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {w : Nat}
    (hw : w < tr.height tp) (hE : cv tr tp w kE = 1) :
    T0 ≤ cv tr tp w T ∧ cv tr tp w T < T0 + tr.height tp := by
  have ha : cv tr tp w act = 1 := act_of hL hw (Or.inr (Or.inr hE))
  obtain ⟨g, hgw, ⟨hgk, hgc⟩, hlat⟩ := latest_start hL w hw ha
  have hg : g < tr.height tp := by omega
  obtain ⟨m', I⟩ := inst_exists hL hH hg hgk hgc
  have Kw := kinds hL hw
  -- not a key row of the block
  have h16 : g + 16 ≤ w := by
    rcases Nat.lt_or_ge w (g + 16) with h | h
    · obtain ⟨K, -⟩ := proc_keys hL hH hg hgk hgc
      have := (K (w - g) (by omega)).2.1
      rw [show g + (w - g) = w by omega] at this
      omega
    · exact h
  -- before the end of the instance
  have hend : w < hdrAt tr tp g m' := by
    rcases Nat.lt_or_ge w (hdrAt tr tp g m') with h | h
    · exact h
    · exfalso
      obtain ⟨hgm, hB⟩ := I.fin
      rcases hB with hp | ⟨hk', hc', -⟩
      · have := pad_after hL hp (w - hdrAt tr tp g m') (by omega)
        rw [show hdrAt tr tp g m' + (w - hdrAt tr tp g m') = w by omega] at this
        omega
      · have := hdrAt_ge tr tp g m'
        exact hlat _ (by omega) h ⟨hk', hc'⟩
  obtain ⟨i, hi, h1, h2⟩ := cover tr tp g m' w h16 hend
  obtain ⟨⟨hh0, hh, -, -, hT⟩, hTb⟩ := I.hdr i hi
  rcases Nat.eq_or_lt_of_le h1 with e | e
  · rw [e] at hh; omega
  rw [hdrAt_succ] at h2
  obtain ⟨-, -, RS⟩ := round_shape hL hH hh0 hh
  obtain ⟨⟨-, -, -, RC, -⟩, -⟩ := RS (w - hdrAt tr tp g i - 1) (by omega)
  rw [show hdrAt tr tp g i + 1 + (w - hdrAt tr tp g i - 1) = w by omega] at RC
  rw [RC T (by simp [roundCols])]
  have := hdrAt_ge tr tp g i
  omega

theorem lid_inj {a b T1 T2 : Nat} (ha : a < 256) (hb : b < 256) (h1 : T0 ≤ T1) (h1' : T1 < T0 + 2 ^ 22)
    (h2 : T0 ≤ T2) (h2' : T2 < T0 + 2 ^ 22) (h : lidOf a T1 = lidOf b T2) : a = b ∧ T1 = T2 := by
  unfold lidOf at h
  have := T0_val
  rcases Nat.lt_trichotomy a b with e | e | e
  · have : a * 4194304 + 4194304 ≤ b * 4194304 := by
      have := Nat.mul_le_mul_right 4194304 (show a + 1 ≤ b by omega); omega
    omega
  · subst e; omega
  · have : b * 4194304 + 4194304 ≤ a * 4194304 := by
      have := Nat.mul_le_mul_right 4194304 (show b + 1 ≤ a by omega); omega
    omega

/-- Round starts strictly increase. -/
theorem T_strict (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f m : Nat}
    (I : Inst tr tp f m) {i : Nat} : ∀ {i'}, i < i' → i' < m →
    cv tr tp (hdrAt tr tp f i) T < cv tr tp (hdrAt tr tp f i') T
  | 0, hii, _ => by omega
  | i' + 1, hii, hi' => by
    obtain ⟨⟨hh0, hh, -⟩, -⟩ := I.hdr i' (by omega)
    have h1 := (round_shape hL hH hh0 hh).1
    have h2 := (I.chain i' hi').1
    rcases Nat.lt_or_ge i i' with h | h
    · have := T_strict hL hH I h (by omega); omega
    · have e : i' = i := by omega
      subst e; omega

/-- **Entry identification by list id.** -/
theorem entry_ident (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22)
    (htau : ∀ w, w < tr.height tp → cv tr tp w act = 1 → cv tr tp w tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0)
    (I : Inst tr tp f m) {i : Nat} (hi : i < m)
    {w : Nat} (hw : w < tr.height tp) (hE : cv tr tp w kE = 1)
    (hlid : lidOf (cv tr tp w tau) (cv tr tp w T) = lidOf (cv tr tp f tau) (cv tr tp (hdrAt tr tp f i) T)) :
    cv tr tp w x < cv tr tp (hdrAt tr tp f i) Lr ∧ w = hdrAt tr tp f i + 1 + cv tr tp w x := by
  have haw := act_of hL hw (Or.inr (Or.inr hE))
  have haf := act_of hL hf (Or.inl hk)
  obtain ⟨tw1, tw2⟩ := entry_T hL hH hw hE
  obtain ⟨⟨hh0, hh, -, -, hT⟩, hTb⟩ := I.hdr i hi
  have := hdrAt_ge tr tp f i
  obtain ⟨e1, e2⟩ := lid_inj (htau w hw haw) (htau f hf haf) tw1 (by omega) (by omega) (by omega) hlid
  obtain ⟨i', hi', j', hj', rfl⟩ := mem_entRows.1 ((ent_iff hL hH hf hk hc I w).1 ⟨hw, hE, e1⟩)
  obtain ⟨⟨hh0', hh', -⟩, -⟩ := I.hdr i' hi'
  obtain ⟨-, -, RS⟩ := round_shape hL hH hh0' hh'
  obtain ⟨⟨-, -, hx, RC, -⟩, -⟩ := RS j' hj'
  rw [RC T (by simp [roundCols])] at e2
  have hii : i' = i := by
    rcases Nat.lt_trichotomy i' i with h | h | h
    · have := T_strict hL hH I h hi; omega
    · exact h
    · have := T_strict hL hH I h hi'; omega
  subst hii
  rw [hx]
  exact ⟨hj', rfl⟩

end

end Proc

/-! ## Ownership of the shuffle buses -/

/-- The shuffle tables of lane v3-chacha and the ownership of their buses (shuffle input /
output / header buses: the process table is the only sender of inputs and the only receiver of
outputs, the shuffle table the only sender of headers). -/
structure ShufOwn (AP : AirP) (tp ts tc tg : Nat) : Prop where
  ts_lt : ts < AP.tables.length
  ts_tab : AP.tables[ts]! = Shuffle.Table.table B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF
  tc_lt : tc < AP.tables.length
  tc_tab : AP.tables[tc]! = Table.table B_SCHACHA
  tg_lt : tg < AP.tables.length
  tg_tab : AP.tables[tg]! = Rng.Table.table B_SCHACHA B_SGEN
  onlyC : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SCHACHA → i.send = false
  pubC : ∀ seg ∈ AP.pubSegs, seg.bus = B_SCHACHA → seg.send = false
  onlyG : ∀ t, t < AP.tables.length → t ≠ tg → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SGEN → i.send = false
  pubG : ∀ seg ∈ AP.pubSegs, seg.bus = B_SGEN → seg.send = false
  onlyM : ∀ u, u < AP.tables.length → u ≠ ts → ∀ i ∈ AP.tables[u]!.interactions, i.bus ≠ B_SSMEM
  pubM : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SSMEM
  onlyShuf : ∀ t, t < AP.tables.length → t ≠ ts → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SSHUF → i.send = false
  pubShuf : ∀ seg ∈ AP.pubSegs, seg.bus = B_SSHUF → seg.send = false
  onlyIn : ∀ t, t < AP.tables.length → t ≠ tp → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SSIN → i.send = false
  pubIn : ∀ seg ∈ AP.pubSegs, seg.bus = B_SSIN → seg.send = false
  onlyOut : ∀ t, t < AP.tables.length → t ≠ tp → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SSOUT → i.send = true
  pubOut : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SSOUT

/-- The shuffle tables' buses. -/
def shufB : Shuffle.Buses := ⟨B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF⟩

theorem shufB_ok : shufB.ok := by unfold Shuffle.Buses.ok shufB; decide

/-! ## Messages -/

theorem msg20 {α β : Type} (F : α → β) (a b c d : α) (g : Nat → α) :
    (([a] ++ (List.range 16).map g ++ [b, c, d]).map F)[0]? = some (F a) ∧
    (∀ q, q < 16 → (([a] ++ (List.range 16).map g ++ [b, c, d]).map F)[1 + q]? = some (F (g q))) ∧
    (([a] ++ (List.range 16).map g ++ [b, c, d]).map F)[17]? = some (F b) ∧
    (([a] ++ (List.range 16).map g ++ [b, c, d]).map F)[18]? = some (F c) ∧
    (([a] ++ (List.range 16).map g ++ [b, c, d]).map F)[19]? = some (F d) := by
  refine ⟨by simp, fun q hq => ?_, by simp [List.range_succ], by simp [List.range_succ],
    by simp [List.range_succ]⟩
  rw [List.getElem?_map, List.append_assoc, List.singleton_append, show 1 + q = q + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega)]
  simp [hq]

theorem ofNat_inj' {a b : Nat} (ha : a < 2013265921) (hb : b < 2013265921) (h : Fp.ofNat a = Fp.ofNat b) :
    a = b := (Proc.ofNat_cv_eq ha hb).1 h

theorem cell_ofNat {tr : Trace Fp} {t r col : Nat} {v : Nat} (h : tr.cell t r col = Fp.ofNat v)
    (hv : v < 2013265921) : cv tr t r col = v := by
  unfold cv; rw [h, Fp.toNat_ofNat, P_val, Nat.mod_eq_of_lt hv]

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- An active process interaction on a bus `b` other than the ones listed is impossible, and the
ones on `SSIN` (send), `SSOUT` (receive), `SSHUF` (receive) are `interactions[4]`, `[5]`, `[1]`. -/
theorem proc_ssin {i : Interaction} (hi : i ∈ Proc.interactions) (hb : i.bus = B_SSIN) (hs : i.send = true) :
    i = Proc.interactions[4]! := by
  rw [Proc.i4_def]
  simp only [Proc.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SSIN, B_SPUBB, B_SSHUF, B_SCMP, B_SPUSH, B_SSOUT, B_SINC, B_SOP]

theorem proc_ssout {i : Interaction} (hi : i ∈ Proc.interactions) (hb : i.bus = B_SSOUT) (hs : i.send = false) :
    i = Proc.interactions[5]! := by
  rw [Proc.i5_def]
  simp only [Proc.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SSIN, B_SPUBB, B_SSHUF, B_SCMP, B_SPUSH, B_SSOUT, B_SINC, B_SOP]

theorem shuf_fin {i : Interaction} (hi : i ∈ Shuffle.Table.interactions B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF)
    (hb : i.bus = B_SSHUF) (hs : i.send = true) :
    i = Interaction.mk B_SSHUF [ZkFormal.Chacha.Table.E.c Shuffle.Table.colFin]
      ([ZkFormal.Chacha.Table.E.c Shuffle.Table.colLid] ++ Shuffle.Table.keyMsg ++
        [ZkFormal.Chacha.Table.E.c Shuffle.Table.colKs, ZkFormal.Chacha.Table.E.c Shuffle.Table.colL,
          ZkFormal.Chacha.Table.E.c Shuffle.Table.colKq]) true := by
  simp only [Shuffle.Table.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SSIN, B_SSHUF, B_SSOUT, B_SSMEM, B_SGEN]

theorem mem_i (k : Nat) (hk : k < 11) : Proc.interactions[k]! ∈ Proc.interactions := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Proc.interactions]; omega)]
  exact List.getElem_mem _

/-- The process input / output message at an entry row `w`. -/
theorem msg4 {tp : Nat} (w : Nat) : (Proc.interactions[4]!).msgVal tr tp w pub =
    [Fp.ofNat (lidOf (cv tr tp w Proc.tau) (cv tr tp w Proc.T)), tr.cell tp w Proc.x, tr.cell tp w Proc.ein] := by
  rw [Proc.i4_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, Proc.ev_lid]; rfl

theorem msg5 {tp : Nat} (w : Nat) : (Proc.interactions[5]!).msgVal tr tp w pub =
    [Fp.ofNat (lidOf (cv tr tp w Proc.tau) (cv tr tp w Proc.T)), tr.cell tp w Proc.x, tr.cell tp w Proc.eout] := by
  rw [Proc.i5_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, Proc.ev_lid]; rfl

theorem kE_of_mult {k : Nat} (hk : (Proc.interactions[k]!).mult = [ZkFormal.Chacha.Table.E.c Proc.kE])
    {tp w : Nat} (hm : (Proc.interactions[k]!).multNat tr tp w pub ≠ 0) : cv tr tp w Proc.kE = 1 := by
  rw [Mem.multNat_c hk] at hm
  by_cases h : cv tr tp w Proc.kE = 1
  · exact h
  · simp [h] at hm

section
variable {tp ts tc tg f m : Nat}

theorem lid_lt (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {w : Nat} (hw : w < tr.height tp) (ha : cv tr tp w Proc.act = 1) {Tv : Nat} (hT : Tv < T0 + 2 ^ 22) :
    lidOf (cv tr tp w Proc.tau) Tv < 2013265921 := by
  have := htau w hw ha
  have := Proc.T0_val
  unfold lidOf
  have : cv tr tp w Proc.tau * 4194304 ≤ 255 * 4194304 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The shuffle of round `i`.** -/
theorem round_shuffle (hH : HoldsP AP pub tr) (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table) (SO : ShufOwn AP tp ts tc tg)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) {i : Nat} (hi : i < m) :
    shuffle ((rOf tr tp f i).ents.map Prod.snd)
        (rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kq)) =
      some (eoutsOf tr tp f i, rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend)) := by
  have hL := pLocal_of hH htp htab
  have hHt := proc_height hH htp htab
  have haf := Proc.act_of hL hf (Or.inl hk)
  obtain ⟨⟨hh0, hh, htauh, hlimb, hT⟩, hTb⟩ := I.hdr i hi
  have hge := Proc.hdrAt_ge tr tp f i
  have := Proc.T0_val
  generalize hhd : Proc.hdrAt tr tp f i = h at hh0 hh htauh hlimb hT hTb hge
  have hTi : cv tr tp h Proc.T < T0 + 2 ^ 22 := by omega
  have hlidlt := lid_lt htau hf haf hTi
  -- the header's shuffle message is sent by a final shuffle row `r'`
  obtain ⟨m1, v1, -, -⟩ := Proc.hdr_msgs hL hh0 hh
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := recv_matched hH SO.ts_lt SO.onlyShuf SO.pubShuf htp hh0
    (by rw [htab]; exact mem_i 1 (by decide)) (by rw [Proc.i1_def]) (by rw [Proc.i1_def])
    (by rw [m1]; exact Nat.one_ne_zero)
  rw [SO.ts_tab] at hi'
  have hfin_i := shuf_fin hi' hb' hs'
  subst hfin_i
  have hfin : cv tr ts r' Shuffle.Table.colFin = 1 := by
    rw [Mem.multNat_c rfl] at hm'
    by_cases e : cv tr ts r' Shuffle.Table.colFin = 1
    · exact e
    · simp [e] at hm'
  rw [v1] at hmsg
  simp only [Interaction.msgVal, Shuffle.Table.keyMsg, List.map_append, List.map_map] at hmsg
  -- read the message
  have M1 := msg20 (fun e => e.eval tr ts r' pub) (ZkFormal.Chacha.Table.E.c Shuffle.Table.colLid)
    (ZkFormal.Chacha.Table.E.c Shuffle.Table.colKs) (ZkFormal.Chacha.Table.E.c Shuffle.Table.colL)
    (ZkFormal.Chacha.Table.E.c Shuffle.Table.colKq)
    (fun q => ZkFormal.Chacha.Table.E.c (Shuffle.Table.colK (q / 2) (q % 2)))
  have M2 := msg20 Fp.ofNat (lidOf (cv tr tp h Proc.tau) (cv tr tp h Proc.T)) (cv tr tp h Proc.kq)
    (cv tr tp h Proc.Lr) (cv tr tp h Proc.kend) (fun q => cv tr tp h (Proc.colL q))
  simp only [List.map_append, List.map_map] at M1 M2
  have get : ∀ k : Nat, (([ZkFormal.Chacha.Table.E.c Shuffle.Table.colLid].map fun e => e.eval tr ts r' pub) ++
      (List.range 16).map ((fun e => e.eval tr ts r' pub) ∘
        fun q => ZkFormal.Chacha.Table.E.c (Shuffle.Table.colK (q / 2) (q % 2))) ++
      ([ZkFormal.Chacha.Table.E.c Shuffle.Table.colKs, ZkFormal.Chacha.Table.E.c Shuffle.Table.colL,
        ZkFormal.Chacha.Table.E.c Shuffle.Table.colKq].map fun e => e.eval tr ts r' pub))[k]? =
      (([lidOf (cv tr tp h Proc.tau) (cv tr tp h Proc.T)].map Fp.ofNat) ++
        (List.range 16).map (Fp.ofNat ∘ fun q => cv tr tp h (Proc.colL q)) ++
        ([cv tr tp h Proc.kq, cv tr tp h Proc.Lr, cv tr tp h Proc.kend].map Fp.ofNat))[k]? := by
    intro k; rw [hmsg]
  have eLid : tr.cell ts r' Shuffle.Table.colLid = Fp.ofNat (lidOf (cv tr tp h Proc.tau) (cv tr tp h Proc.T)) := by
    have := get 0; rw [M1.1, M2.1] at this; exact Option.some.inj this
  have eKs : tr.cell ts r' Shuffle.Table.colKs = Fp.ofNat (cv tr tp h Proc.kq) := by
    have := get 17; rw [M1.2.2.1, M2.2.2.1] at this; exact Option.some.inj this
  have eL : tr.cell ts r' Shuffle.Table.colL = Fp.ofNat (cv tr tp h Proc.Lr) := by
    have := get 18; rw [M1.2.2.2.1, M2.2.2.2.1] at this; exact Option.some.inj this
  have eKq : tr.cell ts r' Shuffle.Table.colKq = Fp.ofNat (cv tr tp h Proc.kend) := by
    have := get 19; rw [M1.2.2.2.2, M2.2.2.2.2] at this; exact Option.some.inj this
  have eK : ∀ q, q < 16 → tr.cell ts r' (Shuffle.Table.colK (q / 2) (q % 2)) = Fp.ofNat (cv tr tp h (Proc.colL q)) := by
    intro q hq
    have := get (1 + q); rw [M1.2.1 q hq, M2.2.1 q hq] at this; exact Option.some.inj this
  -- the key
  have hkey : Shuffle.skey tr ts r' = procKey tr tp f := by
    unfold Shuffle.skey procKey
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.1 hj
    have k0 := eK (2 * j) (by omega)
    have k1 := eK (2 * j + 1) (by omega)
    rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega] at k0
    rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega] at k1
    rw [cell_ofNat k0 (cv_lt _ _), cell_ofNat k1 (cv_lt _ _), hlimb _ (by omega), hlimb _ (by omega)]
    rfl
  -- the shuffle contract
  have hts := SO.ts_lt
  have hlog : tr.log ts ≤ 20 := by
    have := (hH.logBound ts SO.ts_lt).2
    have e : AP.tables[ts] = Shuffle.Table.table B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF := by
      rw [← SO.ts_tab, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem SO.ts_lt]; rfl
    rw [e] at this; exact this
  obtain ⟨L, hL1, -, -, hLc, hrows, l', hsh, hout⟩ := shuffle_sound (B := shufB) hH shufB_ok (by decide)
    SO.tc_lt SO.tc_tab SO.tg_lt SO.tg_tab SO.ts_lt SO.ts_tab SO.onlyC SO.pubC SO.onlyG SO.pubG SO.onlyM
    SO.pubM hlog hr' hfin
  have hLr : L = cv tr tp h Proc.Lr := by rw [← hLc, cell_ofNat eL (cv_lt _ _)]
  subst hLr
  rw [hkey, cell_ofNat eKs (cv_lt _ _), cell_ofNat eKq (cv_lt _ _)] at hsh
  -- the input of position `x`
  have hin : ∀ x, x < cv tr tp h Proc.Lr →
      tr.cell ts (r' - x) Shuffle.Table.colV0 = tr.cell tp (h + 1 + x) Proc.ein := by
    intro x hx
    obtain ⟨ha, hq, hlid⟩ := hrows x hx
    have hmem : (Shuffle.Table.interactions B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF)[0]! ∈
        AP.tables[ts]!.interactions := by rw [SO.ts_tab]; simp [Shuffle.Table.table, Shuffle.Table.interactions]
    obtain ⟨w, hw, i'', hi'', hb'', hs'', hmsg'', hm''⟩ := recv_matched hH htp SO.onlyIn SO.pubIn SO.ts_lt
      (show r' - x < tr.height ts by omega) hmem rfl rfl
      (by rw [Mem.multNat_c rfl]; simp [ha])
    rw [htab] at hi''
    have e4 := proc_ssin hi'' hb'' hs''
    subst e4
    have hE := kE_of_mult (k := 4) (by rw [Proc.i4_def]) hm''
    rw [msg4] at hmsg''
    simp only [Shuffle.Table.interactions, Interaction.msgVal, List.map_cons, List.map_nil,
      List.getElem!_cons_zero] at hmsg''
    simp only [List.cons.injEq] at hmsg''
    obtain ⟨l1, l2, l3, -⟩ := hmsg''
    have hlw : tr.cell ts (r' - x) Shuffle.Table.colLid = tr.cell ts r' Shuffle.Table.colLid := Fp.ext hlid
    have hT' := Proc.entry_T hL hHt hw hE
    have hlid' := ofNat_inj' (a := lidOf (cv tr tp w Proc.tau) (cv tr tp w Proc.T))
      (lid_lt htau hw (Proc.act_of hL hw (Or.inr (Or.inr hE))) (Tv := cv tr tp w Proc.T) (by omega))
      hlidlt (by
        rw [l1]; show tr.cell ts (r' - x) Shuffle.Table.colLid = _; rw [hlw, eLid, htauh])
    rw [← hhd] at hlid'
    obtain ⟨hxl, hwx⟩ := Proc.entry_ident hL hHt htau hf hk hc I hi hw hE hlid'
    rw [hhd] at hwx
    have hxx : cv tr tp w Proc.x = x := by
      have : tr.cell tp w Proc.x = Fp.ofNat x := by
        rw [l2]; show tr.cell ts (r' - x) Shuffle.Table.colQ = _
        unfold cv at hq; exact (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat hq)
      exact cell_ofNat this (by omega)
    rw [hxx] at hwx
    rw [← hwx]; exact l3.symm
  -- the output of position `x`
  have hout' : ∀ x, x < cv tr tp h Proc.Lr →
      Shuffle.Table.outE.eval tr ts (r' - x) pub = tr.cell tp (h + 1 + x) Proc.eout := by
    intro x hx
    obtain ⟨ha, hq, hlid⟩ := hrows x hx
    have hmem : (Shuffle.Table.interactions B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF)[5]! ∈
        AP.tables[ts]!.interactions := by rw [SO.ts_tab]; simp [Shuffle.Table.table, Shuffle.Table.interactions]
    obtain ⟨w, hw, i'', hi'', hb'', hs'', hmsg'', hm''⟩ := send_matched hH htp SO.onlyOut SO.pubOut SO.ts_lt
      (show r' - x < tr.height ts by omega) hmem rfl rfl
      (by rw [Mem.multNat_c rfl]; simp [ha])
    rw [htab] at hi''
    have e5 := proc_ssout hi'' hb'' hs''
    subst e5
    have hE := kE_of_mult (k := 5) (by rw [Proc.i5_def]) hm''
    rw [msg5] at hmsg''
    simp only [Shuffle.Table.interactions, Interaction.msgVal, List.map_cons, List.map_nil,
      List.getElem!_cons_succ, List.getElem!_cons_zero] at hmsg''
    simp only [List.cons.injEq] at hmsg''
    obtain ⟨l1, l2, l3, -⟩ := hmsg''
    have hlw : tr.cell ts (r' - x) Shuffle.Table.colLid = tr.cell ts r' Shuffle.Table.colLid := Fp.ext hlid
    have hT' := Proc.entry_T hL hHt hw hE
    have hlid' := ofNat_inj' (a := lidOf (cv tr tp w Proc.tau) (cv tr tp w Proc.T))
      (lid_lt htau hw (Proc.act_of hL hw (Or.inr (Or.inr hE))) (Tv := cv tr tp w Proc.T) (by omega))
      hlidlt (by
        rw [l1]; show tr.cell ts (r' - x) Shuffle.Table.colLid = _; rw [hlw, eLid, htauh])
    rw [← hhd] at hlid'
    obtain ⟨hxl, hwx⟩ := Proc.entry_ident hL hHt htau hf hk hc I hi hw hE hlid'
    rw [hhd] at hwx
    have hxx : cv tr tp w Proc.x = x := by
      have : tr.cell tp w Proc.x = Fp.ofNat x := by
        rw [l2]; show tr.cell ts (r' - x) Shuffle.Table.colQ = _
        unfold cv at hq; exact (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat hq)
      exact cell_ofNat this (by omega)
    rw [hxx] at hwx
    rw [← hwx]; exact l3.symm
  -- assemble
  have hins : (rOf tr tp f i).ents.map Prod.snd =
      ((List.range (cv tr tp h Proc.Lr)).map fun x => tr.cell ts (r' - x) Shuffle.Table.colV0).map Fp.toNat := by
    simp only [rOf, hhd, List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp, hin x (List.mem_range.1 hx)]
    rfl
  rw [hins, shuffle_map, hsh]
  simp only [Option.map_some]
  congr 2
  have hlen := length_shuffle hsh
  simp only [List.length_map, List.length_range] at hlen
  apply List.ext_getElem (by simp [eoutsOf, hhd, hlen])
  intro x h1 h2
  have hx : x < cv tr tp h Proc.Lr := by rw [List.length_map] at h1; omega
  have := hout x hx
  rw [List.getElem?_eq_getElem (by omega)] at this
  simp only [List.getElem_map, eoutsOf, hhd, List.getElem_range]
  rw [Option.some.inj this, hout' x hx]
  rfl

/-- **`hsim`** for the instance: the recorded rounds replay to the spec's state. -/
theorem proc_sim (hH : HoldsP AP pub tr) (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table) (SO : ShufOwn AP tp ts tc tg)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hR : ∀ q ∈ reqs, q.incs.length < 64) (st : St) (hst : st.rng = rngAt (procKey tr tp f) 0) :
    simR n allowed reqs (roundsOf tr tp f m) T0 st =
      some (specSt n allowed reqs tr tp f st m, (List.range m).flatMap (specPush n allowed reqs tr tp f st)) :=
  simR_spec n allowed reqs hR I (fun _ hi => round_shuffle hH htp htab SO htau hf hk hc I hi) st hst

end

end ZkFormal.NearV3.Sched
