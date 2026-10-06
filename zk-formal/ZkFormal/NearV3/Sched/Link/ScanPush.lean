import ZkFormal.NearV3.Sched.Link.ScanPub

/-!
# ZkFormal.NearV3.Sched.Link.ScanPush — the initial pushes of an instance (`hinit`, `hinitOk`)

The converted request list of an instance is `reqsOf P = convRaw P.params P.n P.raw`; with
`ScanPubOk` it is `raw.map (⟨s·n + r, incsOf p bm⟩)` (`convRaw_eq`).

`ReadOk`: every `READ` of a link address `addrOf τ 0 l` at a time `1 ≤ t ≤ |reqs|` sent on `SOP`
returns `st.allowance[l]` (an obligation of the memory link: before the process times every link
address holds its `INIT` value, the post-link-pass allowance).

**`scan_init`**: the `SPUSH` messages of instance τ sent by the tables other than `sprV3` are,
as a multiset, `(initPushes (reqsOf P) st).map (pmMsg τ)`, and every initial push has fields
`< P` — the hypotheses `hinit`, `hinitOk` of `proc_link`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## The converted requests -/

/-- The converted request list of an instance. -/
def reqsOf (P : InstPub) : List Req := convRaw P.params P.n P.raw

theorem convRaw_eq (p : Params) (n : Nat) :
    ∀ raw : List RawReq, (∀ q ∈ raw, incsOf p q.bm ≠ []) →
      convRaw p n raw = raw.map fun q => (⟨q.s * n + q.r, incsOf p q.bm⟩ : Req)
  | [], _ => rfl
  | q :: raw, h => by
    have ih := convRaw_eq p n raw (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold convRaw at ih ⊢
    rw [List.filterMap_cons, List.map_cons, ← ih]
    have hq := h q (List.mem_cons_self ..)
    cases e : incsOf p q.bm with
    | nil => exact absurd e hq
    | cons a l => simp only [e]

theorem reqsOf_length {P : InstPub} (PO : ScanPubOk P) : (reqsOf P).length = P.raw.length := by
  rw [reqsOf, convRaw_eq _ _ _ (fun q hq => (PO.raw q hq).2.2), List.length_map]

theorem reqsOf_getD {P : InstPub} (PO : ScanPubOk P) {c : Nat} (hc : c < P.raw.length) :
    (reqsOf P).getD c ⟨0, []⟩ =
      ⟨(rawAt P c).s * P.n + (rawAt P c).r, incsOf P.params (rawAt P c).bm⟩ := by
  rw [reqsOf, convRaw_eq _ _ _ (fun q hq => (PO.raw q hq).2.2)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, rawAt, List.getElem?_eq_getElem hc,
    Option.map_some, Option.getD_some]

/-- `READ`s of link addresses before the process times return the given state's allowance. -/
def ReadOk (AP : AirP) (tr : Trace Fp) (pub : List Fp) (τ R : Nat) (st : St) : Prop :=
  ∀ l t v, v < 2013265921 → 1 ≤ t → t ≤ R →
    ([addrOf τ 0 l, t, OP_READ, v, v, 0, 0, 0].map Fp.ofNat) ∈ sopSent AP tr pub →
    v = st.allowance[l]!

/-! ## Sums with one nonzero term -/

theorem sum_single {α : Type} [DecidableEq α] (f : α → Nat) {a : α} :
    ∀ {l : List α}, l.Nodup → a ∈ l → (∀ x ∈ l, x ≠ a → f x = 0) → (l.map f).sum = f a
  | [], _, ha, _ => by simp at ha
  | x :: l, hnd, ha, h => by
    simp only [List.map_cons, List.sum_cons]
    have hnd' := List.nodup_cons.1 hnd
    by_cases e : x = a
    · subst e
      rw [sum_map_zero l f (fun y hy => h y (List.mem_cons_of_mem _ hy)
        (fun hy' => hnd'.1 (hy' ▸ hy)))]
      omega
    · rw [h x (List.mem_cons_self ..) e, sum_single f hnd'.2 (List.mem_cons.1 ha |>.resolve_left
        (Ne.symm e)) (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      omega

namespace Scan

theorem push_head {tr : Trace Fp} {t : Nat} {pub : List Fp} (w : Nat) :
    ((ScanDist.interactions[3]!).msgVal tr t w pub).head? = some (Fp.ofNat (cv tr t w tau)) := by
  rw [push_def]
  simp only [Interaction.msgVal, List.map_cons, List.head?_cons]
  rw [eval_ofNat (v := cv tr t w tau) (by simp only [zev_c, cur_cv])]

theorem row_push (tr : Trace Fp) (t w : Nat) (pub : List Fp) :
    rowTraffic ScanDist.interactions tr t w pub B_SPUSH true =
      if cv tr t w re = 1 then [(ScanDist.interactions[3]!).msgVal tr t w pub] else [] := by
  have e : rowTraffic ScanDist.interactions tr t w pub B_SPUSH true =
      List.replicate ((ScanDist.interactions[3]!).multNat tr t w pub)
        ((ScanDist.interactions[3]!).msgVal tr t w pub) := by
    rw [push_def]
    simp [rowTraffic, ScanDist.interactions, B_SPUSH, B_SPAR, B_SINC, B_SOP, B_SFIN, B_SCMP,
      B_SDLX, B_SDG]
  rw [e]
  apply Proc.replicate_bit
  exact Mem.multNat_c (by rw [push_def])

end Scan

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tsd tp : Nat}

/-- The `SPUSH` sends of the tables other than `sprV3` are those of `ssdV3`. -/
theorem pushOther_perm (O : ScanOwn AP tsd tp) :
    (pushOther AP tr pub tp).Perm (tabTraffic AP.tables tr pub B_SPUSH true tsd) := by
  refine List.perm_iff_count.2 fun M => ?_
  unfold pushOther
  rw [count_flatMap_rows]
  apply sum_single (fun t => (tabTraffic AP.tables tr pub B_SPUSH true t).count M)
    (List.nodup_range.sublist List.filter_sublist)
    (List.mem_filter.2 ⟨List.mem_range.2 O.lt, by simp [O.ne]⟩)
  intro t ht hne
  have ht' := List.mem_filter.1 ht
  have htl := List.mem_range.1 ht'.1
  have htp : t ≠ tp := by simpa using ht'.2
  unfold tabTraffic
  rw [count_flatMap_rows]
  apply sum_map_zero
  intro w _
  have : rowTraffic AP.tables[t]!.interactions tr t w pub B_SPUSH true = [] := by
    unfold rowTraffic
    apply List.flatMap_eq_nil_iff.2
    intro i hi
    rw [if_neg (fun h => O.pushOnly t htl htp hne i hi h.1)]
  rw [this]; rfl

theorem multNat_ne_one {t w : Nat} {i : Interaction} {e : Expr} (hi : i.mult = [e])
    (h : zev (tenv tr t w pub) e = (1 : Nat)) : i.multNat tr t w pub ≠ 0 :=
  Mem.multNat_ne_of hi (by rw [Scan.eval_ofNat h]; rfl)

/-- The end row of a request start of τ: its push is `(τ, key, [key = 0], cid, 64·cid)` and its
`READ` gives `key = st.allowance[link]`. -/
theorem blk_push (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub}
    (SP : ScanPub AP pub τ P) (PO : ScanPubOk P) {st : St}
    (hRd : ReadOk AP tr pub τ (reqsOf P).length st) {f : Nat} (hf : f < tr.height tsd)
    (hq : cv tr tsd f Scan.fQ = 1) (ht : cv tr tsd f Scan.tau = τ) :
    cv tr tsd f Scan.key = st.allowance[((reqsOf P).getD (cv tr tsd f Scan.cid) ⟨0, []⟩).link]! ∧
    (ScanDist.interactions[3]!).msgVal tr tsd (f + 19) pub =
      [τ, cv tr tsd f Scan.key, (if cv tr tsd f Scan.key = 0 then 1 else 0), cv tr tsd f Scan.cid,
        64 * cv tr tsd f Scan.cid].map Fp.ofNat := by
  have hL := sd_local hH O
  have hS := Scan.SLocal.of_sd hL
  have B := blk_ok hH O SP PO hf hq ht
  obtain ⟨-, -, -, -, hpush, hread⟩ := Scan.scan_request hS hf hq B.bm B.base B.dd PO.base24 PO.d24
  have hR := Scan.shape_all hS hf hq 19 (by omega)
  obtain ⟨hw, hk, hre, -⟩ := hR
  simp only [if_pos] at hre
  refine ⟨?_, by rw [hpush, ht]⟩
  -- the READ is sent
  have hm : (ScanDist.interactions[4]!).multNat tr tsd (f + 19) pub ≠ 0 := by
    have F := Scan.row_flags hS hw
    apply multNat_ne_one (e := .add (c Scan.re) (c Dist.kSh)) (by rw [Scan.read_def]; rfl)
    simp only [zev_add, zev_c, cur_cv]
    simp only [Scan.kSh] at F
    omega
  have hmem : (ScanDist.interactions[4]!).msgVal tr tsd (f + 19) pub ∈ sopSent AP tr pub := by
    apply List.count_pos_iff.1
    rw [sopSent_count]
    have h1 := tableBusCount_pos hw (Scan.sd_mem 4 (by decide)) hm
    have h2 := tsd_le (tr := tr) (pub := pub) O (ScanDist.interactions[4]!).bus
      (ScanDist.interactions[4]!).send ((ScanDist.interactions[4]!).msgVal tr tsd (f + 19) pub)
    exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h1) h2
  rw [hread, ht] at hmem
  have hc := B.lt
  have hlen := reqsOf_length PO
  have := hRd _ _ _ (cv_lt _ _) (by omega) (by omega) hmem
  rw [this, reqsOf_getD PO hc, B.link]

/-- **`hinit`, `hinitOk`: the initial pushes of instance τ.** -/
theorem scan_init (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub}
    (SP : ScanPub AP pub τ P) (PO : ScanPubOk P) (hτ : τ < 2013265921) (st : St)
    (hRd : ReadOk AP tr pub τ (reqsOf P).length st) :
    ((pushOther AP tr pub tp).filter (headIs τ)).Perm ((initPushes (reqsOf P) st).map (pmMsg τ)) ∧
      ∀ p ∈ initPushes (reqsOf P) st, PMOk p := by
  have hL := sd_local hH O
  have hS := Scan.SLocal.of_sd hL
  have hlen := reqsOf_length PO
  have l16 := PO.len16
  let key : Nat → Nat := fun c => st.allowance[((reqsOf P).getD c ⟨0, []⟩).link]!
  let H : Nat → List Fp := fun c =>
    [τ, key c, (if key c = 0 then 1 else 0), c, 64 * c].map Fp.ofNat
  let BR := (List.range (tr.height tsd)).filter fun f =>
    cv tr tsd f Scan.fQ == 1 && cv tr tsd f Scan.tau == τ
  have mBR : ∀ f, f ∈ BR ↔ f < tr.height tsd ∧ cv tr tsd f Scan.fQ = 1 ∧ cv tr tsd f Scan.tau = τ := by
    intro f; simp [BR]
  -- (1) the scan's pushes of τ
  have e1 : tabTraffic AP.tables tr pub B_SPUSH true tsd =
      (List.range (tr.height tsd)).flatMap fun w =>
        if (cv tr tsd w Scan.re == 1) then [(ScanDist.interactions[3]!).msgVal tr tsd w pub] else [] := by
    unfold tabTraffic
    apply flatMap_congr'
    intro w _
    rw [O.tab]
    show rowTraffic ScanDist.interactions tr tsd w pub B_SPUSH true = _
    rw [Scan.row_push]
    simp
  have e2 : ((List.range (tr.height tsd)).filter fun w =>
      (cv tr tsd w Scan.re == 1) && headIs τ ((ScanDist.interactions[3]!).msgVal tr tsd w pub)).Perm
      (BR.map (· + 19)) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.sublist List.filter_sublist)
      (nodup_map_on (fun x _ y _ h => by omega) (List.nodup_range.sublist List.filter_sublist))]
    intro w
    simp only [List.mem_filter, List.mem_range, List.mem_map, headIs, Scan.push_head,
      Option.some.injEq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Proc.ofNat_cv_eq (cv_lt _ _) hτ]
    constructor
    · rintro ⟨hw, hre, ht⟩
      obtain ⟨f, rfl, hq⟩ := Scan.re_block hL hw hre
      have hc := (Scan.shape_all hS (by omega) hq 19 (by omega)).2.2.2 Scan.tau (by simp [Scan.reqCols])
      exact ⟨f, ⟨by omega, hq, by rw [← hc, ht]⟩, rfl⟩
    · rintro ⟨f, ⟨hf, hq, ht⟩, rfl⟩
      obtain ⟨hw, -, hre, hc⟩ := Scan.shape_all hS hf hq 19 (by omega)
      simp only [if_pos] at hre
      exact ⟨hw, hre, by rw [hc Scan.tau (by simp [Scan.reqCols]), ht]⟩
  have e3 : (BR.map (· + 19)).map (fun w => (ScanDist.interactions[3]!).msgVal tr tsd w pub) =
      (BR.map fun f => cv tr tsd f Scan.cid).map H := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro f hfB
    obtain ⟨hf, hq, ht⟩ := (mBR f).1 hfB
    obtain ⟨hk, hp⟩ := blk_push hH O SP PO hRd hf hq ht
    simp only [Function.comp, hp, H, key, ← hk]
  -- (2) the cids of the request starts are `0 … |raw| − 1`
  have e4 : (BR.map fun f => cv tr tsd f Scan.cid).Perm (List.range (reqsOf P).length) := by
    rw [List.perm_ext_iff_of_nodup (nodup_map_on (fun x hx y hy h => by
        obtain ⟨a1, a2, a3⟩ := (mBR x).1 hx
        obtain ⟨b1, b2, b3⟩ := (mBR y).1 hy
        exact blk_unique hH O SP PO a1 a2 a3 b1 b2 b3 h)
      (List.nodup_range.sublist List.filter_sublist)) List.nodup_range]
    intro c
    rw [List.mem_map, List.mem_range, hlen]
    constructor
    · rintro ⟨f, hfB, rfl⟩
      obtain ⟨hf, hq, ht⟩ := (mBR f).1 hfB
      exact (blk_ok hH O SP PO hf hq ht).lt
    · intro hc
      obtain ⟨f, hf, hq, ht, hcid⟩ := blk_exists hH O SP PO hτ hc
      exact ⟨f, (mBR f).2 ⟨hf, hq, ht⟩, hcid⟩
  have hinit := initMsgs_eq τ (reqsOf P) st key (fun _ _ => rfl)
  refine ⟨?_, ?_⟩
  · refine ((pushOther_perm O).filter _).trans ?_
    rw [e1, filter_flatMap_single]
    refine (e2.map _).trans ?_
    rw [e3, ← hinit]
    exact e4.map H
  · intro p hp
    simp only [initPushes, List.mem_map, List.mem_range] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    obtain ⟨f, hf, hq, ht, hcid⟩ := blk_exists hH O SP PO hτ (show c < P.raw.length by omega)
    have hk := (blk_push hH O SP PO hRd hf hq ht).1
    rw [hcid] at hk
    refine ⟨by rw [← hk]; exact cv_lt _ _, ?_, by simp only; omega, by simp only; omega⟩
    simp only [zNext, Nat.one_ne_zero, if_false]
    split <;> omega

end

end ZkFormal.NearV3.Sched
