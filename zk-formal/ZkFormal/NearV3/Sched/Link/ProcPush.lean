import ZkFormal.NearV3.Sched.Link.ProcOrd

/-!
# ZkFormal.NearV3.Sched.Link.ProcPush — the push log of an instance (`hperm` of `process_rounds`)

The `SPUSH` bus restricted to instance τ (messages whose first element is τ):

* received: only by `sprV3` (ownership), on its entry rows; those with `τ` are exactly the
  instance's entry rows (`Proc.ent_iff`), i.e. `entriesOf (roundsOf …)`;
* sent by `sprV3`: the re-pushes of the instance's entries with `pm = 1` (`pushRec`);
* sent by the other tables: the initial pushes (`pushOther`, the scan; an explicit hypothesis
  here, discharged by the scan's global view).

**`rounds_perm`**: `entriesOf (roundsOf tr tp f m) ~ initPushes reqs st ++ pushRec tr tp f m`.
`initMsgs_eq` turns the scan's end-row pushes `(τ, key_cid, [key_cid = 0], cid, 64·cid)` with
`key_cid = st.allowance[link_cid]` into `initPushes reqs st`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3.Scheduler

/-! ## Traffic of one table, all tables -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Messages of table `t` on bus `b`, side `s`. -/
def tabTraffic (Ts : List Air.Table) (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (t : Nat) :
    List (List F) :=
  (List.range (tr.height t)).flatMap fun r => rowTraffic Ts[t]!.interactions tr t r pub b s

theorem busTraffic_eq (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) :
    ∀ (Ts : List Air.Table) (k : Nat),
      busTraffic tr pub b s Ts k = (List.range Ts.length).flatMap fun u =>
        (List.range (tr.height (k + u))).flatMap fun r => rowTraffic Ts[u]!.interactions tr (k + u) r pub b s
  | [], _ => rfl
  | T :: Ts, k => by
    rw [busTraffic, busTraffic_eq tr pub b s Ts (k + 1), List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.succ_eq_add_one,
      show ∀ u, k + 1 + u = k + (u + 1) from fun u => by omega]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- All traffic = the traffic of table `tp` and of the others. -/
theorem traffic_split (Ts : List Air.Table) (tr : Trace F) (pub : List F) (b : Nat) (s : Bool)
    {tp : Nat} (htp : tp < Ts.length) :
    (busTraffic tr pub b s Ts 0).Perm
      (tabTraffic Ts tr pub b s tp ++ ((List.range Ts.length).filter (· != tp)).flatMap (tabTraffic Ts tr pub b s)) := by
  rw [busTraffic_eq]
  simp only [Nat.zero_add]
  have h1 := (List.perm_cons_erase (List.mem_range.2 htp)).flatMap_right (tabTraffic Ts tr pub b s)
  rw [List.flatMap_cons, List.nodup_range.erase_eq_filter] at h1
  exact h1

/-- Messages of a list of rows emitting one message each under a condition. -/
theorem filter_flatMap_single {α : Type} (l : List Nat) (p : Nat → Bool) (g : Nat → α) (q : α → Bool) :
    (l.flatMap fun r => if p r then [g r] else []).filter q =
      (l.filter fun r => p r && q (g r)).map g := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [List.flatMap_cons, List.filter_append, ih, List.filter_cons]
    by_cases hp : p r <;> by_cases hq : q (g r) <;> simp [hp, hq]

end

/-! ## The bus balance as permutations -/

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem traffic_perm (hH : HoldsP AP pub tr) {b : Nat} (hpub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ b) :
    (busTraffic tr pub b true AP.tables 0).Perm (busTraffic tr pub b false AP.tables 0) := by
  refine List.perm_iff_count.2 fun m => ?_
  have hbal := hH.balance b m
  rw [pubCount_zero (fun seg h1 h2 => absurd h2 (hpub seg h1)) _,
    pubCount_zero (fun seg h1 h2 => absurd h2 (hpub seg h1)) _] at hbal
  rw [count_busTraffic, count_busTraffic]
  exact hbal

/-- A bus side used only by table `tp` carries exactly its traffic. -/
theorem traffic_single {b : Nat} {s : Bool} {tp : Nat} (htp : tp < AP.tables.length)
    (h : ∀ t, t < AP.tables.length → t ≠ tp → ∀ i ∈ AP.tables[t]!.interactions, i.bus = b → i.send ≠ s) :
    (busTraffic tr pub b s AP.tables 0).Perm (tabTraffic AP.tables tr pub b s tp) := by
  refine List.perm_iff_count.2 fun m => ?_
  rw [count_busTraffic]
  have := busCount_single (A := AP.toAir) (tr := tr) (pub := pub) (m := m) htp h
  unfold busCount at this
  rw [this, tableBusCount_eq]
  rfl

/-! ## Push messages -/

/-- The `SPUSH` message of a push of instance `τ`. -/
def pmMsg (τ : Nat) (p : PM) : List Fp := [τ, p.key, p.z, p.ts, p.v].map Fp.ofNat

/-- First element `τ`. -/
def headIs (τ : Nat) (m : List Fp) : Bool := decide (m.head? = some (Fp.ofNat τ))

/-- All fields below `P`. -/
def PMOk (p : PM) : Prop := p.key < 2013265921 ∧ p.z < 2013265921 ∧ p.ts < 2013265921 ∧ p.v < 2013265921

/-- Decode a push message. -/
def unMsg (m : List Fp) : PM := ⟨(m.getD 1 0).toNat, (m.getD 2 0).toNat, (m.getD 3 0).toNat, (m.getD 4 0).toNat⟩

theorem unMsg_pmMsg (τ : Nat) {p : PM} (h : PMOk p) : unMsg (pmMsg τ p) = p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [unMsg, pmMsg, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
    Fp.toNat_ofNat, P_val, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
    Nat.mod_eq_of_lt h4]

theorem perm_of_map_pmMsg (τ : Nat) {A B : List PM} (hA : ∀ p ∈ A, PMOk p) (hB : ∀ p ∈ B, PMOk p)
    (h : (A.map (pmMsg τ)).Perm (B.map (pmMsg τ))) : A.Perm B := by
  have eA : (A.map (pmMsg τ)).map unMsg = A := by
    rw [List.map_map]; conv => rhs; rw [← List.map_id A]
    exact List.map_congr_left fun p hp => unMsg_pmMsg τ (hA p hp)
  have eB : (B.map (pmMsg τ)).map unMsg = B := by
    rw [List.map_map]; conv => rhs; rw [← List.map_id B]
    exact List.map_congr_left fun p hp => unMsg_pmMsg τ (hB p hp)
  rw [← eA, ← eB]; exact h.map unMsg

/-- `SPUSH` messages sent by the tables other than `tp`. -/
def pushOther (AP : AirP) (tr : Trace Fp) (pub : List Fp) (tp : Nat) : List (List Fp) :=
  ((List.range AP.tables.length).filter (· != tp)).flatMap (tabTraffic AP.tables tr pub B_SPUSH true)

/-- Re-pushes recorded by the instance: entry `j` of round `i` with `pm = 1` pushes
`(alOut, [alOut = 0]·(z + 1), T + j, eout + 1)`. -/
def pushRec (tr : Trace Fp) (tp f m : Nat) : List PM :=
  (List.range m).flatMap fun i =>
    let h := Proc.hdrAt tr tp f i
    ((List.range (cv tr tp h Proc.Lr)).filter fun j => cv tr tp (h + 1 + j) Proc.pm == 1).map fun j =>
      ⟨cv tr tp (h + 1 + j) Proc.alOut,
        (if cv tr tp (h + 1 + j) Proc.alOut = 0 then cv tr tp h Proc.z + 1 else 0),
        cv tr tp h Proc.T + j, (cv tr tp (h + 1 + j) Proc.eout + 1) % 2013265921⟩

/-- The scan's initial pushes `(τ, key_cid, [key_cid = 0], cid, 64·cid)` with
`key_cid = st.allowance[link_cid]` are `initPushes reqs st`. -/
theorem initMsgs_eq (τ : Nat) (reqs : List Req) (st : St) (key : Nat → Nat)
    (hkey : ∀ cid, cid < reqs.length → key cid = st.allowance[(reqs.getD cid ⟨0, []⟩).link]!) :
    (List.range reqs.length).map (fun cid =>
        [τ, key cid, (if key cid = 0 then 1 else 0), cid, 64 * cid].map Fp.ofNat) =
      (initPushes reqs st).map (pmMsg τ) := by
  rw [initPushes, List.map_map]
  apply List.map_congr_left
  intro cid hc
  simp only [Function.comp, pmMsg, zNext, hkey cid (List.mem_range.1 hc), Nat.mul_comm 64 cid]
  simp

/-! ## The process table on `SPUSH` -/

namespace Proc
open ZkFormal.Chacha.Table.E

variable {tp : Nat}

theorem row_recv (tr : Trace Fp) (tp r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tp r pub B_SPUSH false =
      List.replicate ((interactions[3]!).multNat tr tp r pub) ((interactions[3]!).msgVal tr tp r pub) := by
  rw [i3_def]
  simp [rowTraffic, interactions, B_SPUSH, B_SPUBB, B_SSHUF, B_SCMP, B_SSIN, B_SSOUT, B_SINC, B_SOP]

theorem row_send (tr : Trace Fp) (tp r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tp r pub B_SPUSH true =
      List.replicate ((interactions[10]!).multNat tr tp r pub) ((interactions[10]!).msgVal tr tp r pub) := by
  rw [i10_def]
  simp [rowTraffic, interactions, B_SPUSH, B_SPUBB, B_SSHUF, B_SCMP, B_SSIN, B_SSOUT, B_SINC, B_SOP]

theorem replicate_bit {α : Type} {n : Nat} {P : Prop} [Decidable P] (x : α) (h : n = if P then 1 else 0) :
    List.replicate n x = if P then [x] else [] := by
  subst h; split <;> rfl

theorem head_msg3 (w : Nat) :
    ((interactions[3]!).msgVal tr tp w pub).head? = some (Fp.ofNat (cv tr tp w tau)) := by
  rw [i3_def]; simp [Interaction.msgVal, ev_c]

theorem head_msg10 (w : Nat) :
    ((interactions[10]!).msgVal tr tp w pub).head? = some (Fp.ofNat (cv tr tp w tau)) := by
  rw [i10_def]; simp [Interaction.msgVal, ev_c]

theorem ofNat_cv_eq {a b : Nat} (ha : a < 2013265921) (hb : b < 2013265921) :
    (Fp.ofNat a = Fp.ofNat b) ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fp.toNat h
    rwa [Fp.toNat_ofNat, Fp.toNat_ofNat, P_val, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

/-- `pm = 1` only on entry rows. -/
theorem pm_kE (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp) (hp : cv tr tp w pm = 1) :
    cv tr tp w kE = 1 := by
  obtain ⟨q, c1⟩ := zd hL hw (e := sub (c pm) (mul3 (c kE) (c ok) (notE (c lastf))))
    (by simp [constraints, cEnt])
  pz c1 [hp]
  have K := kinds hL hw
  have hO := bool_of hL hw (x := ok) (by simp [boolCols])
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.2.2.1 with h1 | h1
  · rw [h1] at c1; push_cast at c1; omega
  · exact h1

end Proc

section
variable {tp f m : Nat}

/-- The instance's receives with `τ`, as messages. -/
theorem recv_inst (hH : HoldsP AP pub tr) (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table)
    (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) :
    ((tabTraffic AP.tables tr pub B_SPUSH false tp).filter (headIs (cv tr tp f Proc.tau))).Perm
      ((entriesOf (roundsOf tr tp f m)).map (pmMsg (cv tr tp f Proc.tau))) := by
  have hL := pLocal_of hH htp htab
  have hHt := proc_height hH htp htab
  -- the rows
  have e1 : tabTraffic AP.tables tr pub B_SPUSH false tp =
      (List.range (tr.height tp)).flatMap fun r =>
        if (cv tr tp r Proc.kE == 1) then [(Proc.interactions[3]!).msgVal tr tp r pub] else [] := by
    unfold tabTraffic
    apply flatMap_congr'
    intro r _
    rw [htab]
    show rowTraffic Proc.interactions tr tp r pub B_SPUSH false = _
    rw [Proc.row_recv]
    apply Proc.replicate_bit
    rw [Mem.multNat_c (i := Proc.interactions[3]!) (by rw [Proc.i3_def])]
    simp
  rw [e1, filter_flatMap_single]
  have e2 : ((List.range (tr.height tp)).filter fun r =>
      (cv tr tp r Proc.kE == 1) && headIs (cv tr tp f Proc.tau) ((Proc.interactions[3]!).msgVal tr tp r pub)).Perm
      (Proc.entRows tr tp f m) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.sublist List.filter_sublist) (Proc.entRows_nodup ..)]
    intro r
    rw [← Proc.ent_iff hL hHt hf hk hc I r, List.mem_filter, List.mem_range]
    simp only [headIs, Proc.head_msg3, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Proc.ofNat_cv_eq (cv_lt _ _) (cv_lt _ _)]
  refine (e2.map _).trans (List.Perm.of_eq ?_)
  -- message by message
  unfold Proc.entRows entriesOf roundsOf
  rw [List.map_flatMap, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr'
  intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨⟨hh0, hh, ht, -⟩, -⟩ := I.hdr i hi'
  rw [List.map_map, rOf, List.map_map, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.1 hj
  obtain ⟨-, v3, -⟩ := Proc.ent_msgs hL hHt hh0 hh hj'
  simp only [Function.comp, v3, pmMsg, ht]

/-- The instance's re-pushes, as messages. -/
theorem send_inst (hH : HoldsP AP pub tr) (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table)
    (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) :
    ((tabTraffic AP.tables tr pub B_SPUSH true tp).filter (headIs (cv tr tp f Proc.tau))).Perm
      ((pushRec tr tp f m).map (pmMsg (cv tr tp f Proc.tau))) := by
  have hL := pLocal_of hH htp htab
  have hHt := proc_height hH htp htab
  have e1 : tabTraffic AP.tables tr pub B_SPUSH true tp =
      (List.range (tr.height tp)).flatMap fun r =>
        if (cv tr tp r Proc.pm == 1) then [(Proc.interactions[10]!).msgVal tr tp r pub] else [] := by
    unfold tabTraffic
    apply flatMap_congr'
    intro r _
    rw [htab]
    show rowTraffic Proc.interactions tr tp r pub B_SPUSH true = _
    rw [Proc.row_send]
    apply Proc.replicate_bit
    rw [Mem.multNat_c (i := Proc.interactions[10]!) (by rw [Proc.i10_def])]
    simp
  rw [e1, filter_flatMap_single]
  have e2 : ((List.range (tr.height tp)).filter fun r =>
      (cv tr tp r Proc.pm == 1) && headIs (cv tr tp f Proc.tau) ((Proc.interactions[10]!).msgVal tr tp r pub)).Perm
      ((Proc.entRows tr tp f m).filter fun r => cv tr tp r Proc.pm == 1) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.sublist List.filter_sublist)
      ((Proc.entRows_nodup ..).sublist List.filter_sublist)]
    intro r
    rw [List.mem_filter, List.mem_filter, ← Proc.ent_iff hL hHt hf hk hc I r, List.mem_range]
    simp only [headIs, Proc.head_msg10, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Proc.ofNat_cv_eq (cv_lt _ _) (cv_lt _ _)]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, Proc.pm_kE hL a b, c⟩, b⟩
    · rintro ⟨⟨a, -, c⟩, b⟩; exact ⟨a, b, c⟩
  refine (e2.map _).trans (List.Perm.of_eq ?_)
  unfold Proc.entRows pushRec
  rw [List.filter_flatMap, List.map_flatMap, List.map_flatMap]
  apply flatMap_congr'
  intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨⟨hh0, hh, ht, -⟩, -⟩ := I.hdr i hi'
  simp only
  rw [List.filter_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.1 (List.mem_filter.1 hj).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, v10, -⟩ := Proc.ent_msgs hL hHt hh0 hh hj'
  simp only [Function.comp, v10, pmMsg, ht, List.map_cons, List.map_nil, Proc.ofNat_mod]

/-- Fields of the recorded entries are below `P`. -/
theorem entries_ok (tp f m : Nat) : ∀ p ∈ entriesOf (roundsOf tr tp f m), PMOk p := by
  intro p hp
  obtain ⟨R, hR, h1, h2, h3⟩ := mem_entriesOf hp
  simp only [roundsOf, List.mem_map, List.mem_range] at hR
  obtain ⟨i, -, rfl⟩ := hR
  simp only [rOf, List.mem_map, List.mem_range] at h3
  obtain ⟨j, -, e⟩ := h3
  have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
  simp only at e1 e2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; exact cv_lt _ _
  · rw [h2]; exact cv_lt _ _
  · rw [← e1]; exact cv_lt _ _
  · rw [← e2]; exact cv_lt _ _

/-- Fields of the recorded re-pushes are below `P`. -/
theorem pushRec_ok (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m) :
    ∀ p ∈ pushRec tr tp f m, PMOk p := by
  intro p hp
  simp only [pushRec, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter] at hp
  obtain ⟨i, hi, j, ⟨hj, -⟩, rfl⟩ := hp
  have hz := (z_le hL hH I i hi).1
  have hil := i_lt I hi
  have hT := (I.hdr i hi).2
  have := Proc.T0_val
  refine ⟨cv_lt _ _, ?_, by simp only; omega, Nat.mod_lt _ (by decide)⟩
  simp only; split <;> omega

/-- **`hperm`**: the recorded entries are the initial pushes and the recorded re-pushes. -/
theorem rounds_perm (hH : HoldsP AP pub tr) (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table)
    (hrecv : ∀ t, t < AP.tables.length → t ≠ tp → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = B_SPUSH → i.send = true)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SPUSH)
    (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) {reqs : List Req} {st : St}
    (hinit : ((pushOther AP tr pub tp).filter (headIs (cv tr tp f Proc.tau))).Perm
      ((initPushes reqs st).map (pmMsg (cv tr tp f Proc.tau))))
    (hinitOk : ∀ p ∈ initPushes reqs st, PMOk p) :
    (entriesOf (roundsOf tr tp f m)).Perm (initPushes reqs st ++ pushRec tr tp f m) := by
  have hL := pLocal_of hH htp htab
  have hHt := proc_height hH htp htab
  have hbal := (traffic_perm hH hpub).filter (headIs (cv tr tp f Proc.tau))
  have hS := ((traffic_split AP.tables tr pub B_SPUSH true htp).filter (headIs (cv tr tp f Proc.tau)))
  have hR := (traffic_single (b := B_SPUSH) (s := false) (tr := tr) (pub := pub) htp
    (fun t ht hne i hi hb => by rw [hrecv t ht hne i hi hb]; simp)).filter (headIs (cv tr tp f Proc.tau))
  rw [List.filter_append] at hS
  have h1 := (recv_inst hH htp htab hf hk hc I).symm.trans (hR.symm.trans (hbal.symm.trans hS))
  have h2 := h1.trans ((send_inst hH htp htab hf hk hc I).append hinit)
  have h3 := h2.trans List.perm_append_comm
  rw [← List.map_append] at h3
  refine perm_of_map_pmMsg (cv tr tp f Proc.tau) (entries_ok tp f m) ?_ h3
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hinitOk p hp
  · exact pushRec_ok hL hHt I p hp

end

end ZkFormal.NearV3.Sched
