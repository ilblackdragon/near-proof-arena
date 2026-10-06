import ZkFormal.NearV3.Sched.Link.ScanRows
import ZkFormal.NearV3.Sched.Link.ProcLink
import ZkFormal.NearV3.Sched.Render
import ZkFormal.NearV3.Sched.Spec.Conv

/-!
# ZkFormal.NearV3.Sched.Link.ScanPub — the scan blocks of an instance are its public requests

The scan rows of `ssdV3` receive the public `SPAR` records of tags 1 (scan params) and 2 (raw
requests). With the bus ownership `ScanOwn` (no table sends on `SPAR`, every public `SPAR`
segment is a send, the other `SPAR` receivers have tag 0) and the public facts `ScanPub` (the
public tag-1/2 records of instance τ are `scanRecs τ P`, i.e. `Render.render`'s), and
`ScanPubOk P` (bounds of the prepared statement):

* **`blk_ok`**: a request-start row `f` of instance τ is request `c = cid_f < |raw|`: its
  register holds the bitmap bytes of `raw[c]`, `s, r` are `raw[c]`'s, `link = s·n + r`, and
  `base, D` are the instance's parameters (from the section's param row, `param_of`);
* **`blk_unique`**: two request-start rows of τ with the same `cid` are equal (the public record
  is sent once);
* **`blk_exists`**: every `c < |raw|` has a request-start row of τ with `cid = c`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## Public records -/

def rawD : RawReq := ⟨0, 0, []⟩

/-- Raw request `c` of an instance. -/
def rawAt (P : InstPub) (c : Nat) : RawReq := P.raw.getD c rawD

/-- The `SPAR` record of raw request `q` with index `c`. -/
def rawRec (τ : Nat) (q : RawReq) (c : Nat) : List Nat :=
  [τ, PT_RAW, (q.bm.getD 0 0).toNat, (q.bm.getD 1 0).toNat, (q.bm.getD 2 0).toNat,
    (q.bm.getD 3 0).toNat, (q.bm.getD 4 0).toNat, c % 256, c / 256 % 256, q.s, q.r]

theorem rawAt_mem {P : InstPub} {c : Nat} (hc : c < P.raw.length) : rawAt P c ∈ P.raw := by
  simp only [rawAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
  exact List.getElem_mem hc

theorem rawRecs_eq (τ : Nat) (P : InstPub) :
    rawRecs τ P = (List.range P.raw.length).map fun c => rawRec τ (rawAt P c) c := by
  apply List.ext_getElem
  · simp [rawRecs]
  · intro i h1 h2
    have hi : i < P.raw.length := by simpa [rawRecs] using h1
    simp only [rawRecs, List.getElem_map, List.getElem_zip, List.getElem_range]
    simp only [rawAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rfl

/-- The public tag-1/2 records of instance τ (`Render.render`'s `par` restricted to τ). -/
def scanRecs (τ : Nat) (P : InstPub) : List (List Nat) :=
  (if P.raw.isEmpty then [] else [parScan τ P]) ++ rawRecs τ P

def scanMsgs (τ : Nat) (P : InstPub) : List (List Fp) := (scanRecs τ P).map (List.map Fp.ofNat)

/-- Bounds of the prepared statement used by the scan link. -/
structure ScanPubOk (P : InstPub) : Prop where
  base24 : P.params.base < 2 ^ 24
  d24 : P.params.maxSingleGrant - P.params.base < 2 ^ 24
  n64 : P.n ≤ 64
  len16 : P.raw.length ≤ 2 ^ 16
  raw : ∀ q ∈ P.raw, q.s < P.n ∧ q.r < P.n ∧ incsOf P.params q.bm ≠ []

/-- The public `SPAR` messages of instance τ with tags 1 and 2 are `scanMsgs τ P`. -/
structure ScanPub (AP : AirP) (pub : List Fp) (τ : Nat) (P : InstPub) : Prop where
  par : ∀ M : List Fp, M.head? = some (Fp.ofNat τ) →
    (M[1]? = some (Fp.ofNat PT_SCAN) ∨ M[1]? = some (Fp.ofNat PT_RAW)) →
    pubCount AP pub B_SPAR true M = (scanMsgs τ P).count M

/-- Bus ownership used by the scan link (STATUS-V3-SCHED §6.1): `ssdV3` is table `tsd`; no table
sends on `SPAR` and no public segment receives on it; the other `SPAR` receivers (the codec) use
tag 0; only `ssdV3` and `sprV3` use `SPUSH`; only `ssdV3` sends on `SINC`. -/
structure ScanOwn (AP : AirP) (tsd tp : Nat) : Prop where
  lt : tsd < AP.tables.length
  tab : AP.tables[tsd]! = ScanDist.table
  ne : tsd ≠ tp
  parSend : ∀ t, t < AP.tables.length → ∀ i ∈ AP.tables[t]!.interactions, i.bus = B_SPAR →
    i.send = false
  parPub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SPAR → seg.send = true
  parTag : ∀ t, t < AP.tables.length → t ≠ tsd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SPAR → i.msg[1]? = some (k 0)
  pushOnly : ∀ t, t < AP.tables.length → t ≠ tp → t ≠ tsd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus ≠ B_SPUSH
  incOnly : ∀ t, t < AP.tables.length → t ≠ tsd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SINC → i.send = false

/-! ## Field lists -/

theorem ofNat_list_inj : ∀ {A B : List Nat}, (∀ x ∈ A, x < 2013265921) → (∀ x ∈ B, x < 2013265921) →
    A.map Fp.ofNat = B.map Fp.ofNat → A = B
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: A, b :: B, hA, hB, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [(Proc.ofNat_cv_eq (hA a (List.mem_cons_self ..)) (hB b (List.mem_cons_self ..))).1 h.1,
      ofNat_list_inj (fun x hx => hA x (List.mem_cons_of_mem _ hx))
        (fun x hx => hB x (List.mem_cons_of_mem _ hx)) h.2]

theorem eval_one_of_mult {tr : Trace Fp} {t w : Nat} {pub : List Fp} {i : Interaction} {e : Expr}
    (hm : i.mult = [e]) (h : i.multNat tr t w pub ≠ 0) : e.eval tr t w pub = 1 := by
  unfold Interaction.multNat at h
  rw [hm] at h
  simp only [Interaction.multNat.go] at h
  split at h
  · assumption
  · simp at h

theorem ofNat_eq_one {v : Nat} (hv : v < 2013265921) (h : Fp.ofNat v = 1) : v = 1 :=
  (Proc.ofNat_cv_eq hv (by decide)).1 h

/-! ## The `SPAR` receive of `ssdV3` -/

namespace Scan

theorem par_def : ScanDist.interactions[0]! = Interaction.mk B_SPAR
    [.add (c Scan.kP) (.add (c Scan.fQ) (.add (c Dist.kSh) (c Dist.kC)))]
    ([c Dist.tau, ScanDist.tagE] ++ (List.range 9).map fun i => c (Dist.fw i)) false := rfl

theorem par_mem : ScanDist.interactions[0]! ∈ ScanDist.interactions := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ScanDist.interactions])]
  exact List.getElem_mem _

theorem sd_mem (k : Nat) (hk : k < 10) : ScanDist.interactions[k]! ∈ ScanDist.interactions := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ScanDist.interactions]; omega)]
  exact List.getElem_mem _

theorem par_cases : ∀ i ∈ ScanDist.interactions, i.bus = B_SPAR → i = ScanDist.interactions[0]! := by
  decide

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- The `SPAR` message of a row, as naturals: `(τ, tag, f₀ … f₈)`. -/
def parV (tr : Trace Fp) (t w : Nat) : List Nat :=
  [cv tr t w tau, cv tr t w kP + 2 * cv tr t w kS + 3 * cv tr t w kSh + 4 * cv tr t w kC,
    cv tr t w (q 0), cv tr t w (q 1), cv tr t w (q 2), cv tr t w (q 3), cv tr t w (q 4),
    cv tr t w clo, cv tr t w chi, cv tr t w s, cv tr t w r]

theorem par_msg (w : Nat) : (ScanDist.interactions[0]!).msgVal tr t w pub = (parV tr t w).map Fp.ofNat := by
  rw [par_def]
  have ec : ∀ x, (c x).eval tr t w pub = Fp.ofNat (cv tr t w x) := fun x =>
    eval_ofNat (by simp only [zev_c, cur_cv])
  have et : ScanDist.tagE.eval tr t w pub = Fp.ofNat (cv tr t w kP + 2 * cv tr t w kS +
      3 * cv tr t w kSh + 4 * cv tr t w kC) :=
    eval_ofNat (by simp only [ScanDist.tagE, zev_add, zev_smul, zev_c, cur_cv, kP, kS, kSh, kC]; omega)
  show [(c Dist.tau).eval tr t w pub, ScanDist.tagE.eval tr t w pub, (c (Dist.fw 0)).eval tr t w pub,
    (c (Dist.fw 1)).eval tr t w pub, (c (Dist.fw 2)).eval tr t w pub, (c (Dist.fw 3)).eval tr t w pub,
    (c (Dist.fw 4)).eval tr t w pub, (c (Dist.fw 5)).eval tr t w pub, (c (Dist.fw 6)).eval tr t w pub,
    (c (Dist.fw 7)).eval tr t w pub, (c (Dist.fw 8)).eval tr t w pub] = _
  simp only [ec, et]
  rfl

theorem parV_lt (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) :
    ∀ x ∈ parV tr t w, x < 2013265921 := by
  have F := row_flags hL hw
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  intro x hx
  simp only [parV, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> first | exact lt _ | omega

/-- The tag of a request row is 2, of a param row 1. -/
theorem tag_kS (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1) :
    cv tr t w kP + 2 * cv tr t w kS + 3 * cv tr t w kSh + 4 * cv tr t w kC = 2 := by
  have F := row_flags hL hw; omega

theorem tag_kP (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kP = 1) :
    cv tr t w kP + 2 * cv tr t w kS + 3 * cv tr t w kSh + 4 * cv tr t w kC = 1 := by
  have F := row_flags hL hw; omega

theorem par_mult (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (h : cv tr t w fQ = 1 ∨ cv tr t w kP = 1) : (ScanDist.interactions[0]!).multNat tr t w pub ≠ 0 := by
  have F := row_flags hL hw
  have hf := bool_of hL hw (x := fQ) (by simp [boolCols, ownBool])
  apply Mem.multNat_ne_of (e := .add (c Scan.kP) (.add (c Scan.fQ) (.add (c Dist.kSh) (c Dist.kC)))) rfl
  rw [eval_ofNat (v := 1) (by simp only [zev_add, zev_c, cur_cv]; simp only [kSh, kC] at F; omega)]
  rfl

/-- An active `SPAR` receive of a row with tag 2 is a request start. -/
theorem fQ_of_par (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (hm : (ScanDist.interactions[0]!).multNat tr t w pub ≠ 0)
    (ht : cv tr t w kP + 2 * cv tr t w kS + 3 * cv tr t w kSh + 4 * cv tr t w kC = 2) :
    cv tr t w fQ = 1 := by
  have F := row_flags hL hw
  have hf := bool_of hL hw (x := fQ) (by simp [boolCols, ownBool])
  have he := eval_one_of_mult (by rw [par_def]) hm
  rw [eval_ofNat (v := cv tr t w kP + cv tr t w fQ + cv tr t w kSh + cv tr t w kC)
    (by simp only [zev_add, zev_c, cur_cv, kSh, kC]; omega)] at he
  have := ofNat_eq_one (by omega) he
  omega

end

end Scan

/-! ## Counting on `SPAR` -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tsd tp : Nat}

theorem sd_local (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) :
    Local ScanDist.constraints tr tsd pub := by
  have := local_of_holdsP hH O.lt; rw [O.tab] at this; exact this

theorem par_count (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) (M : List Fp) :
    pubCount AP pub B_SPAR true M = busCount AP.toAir tr pub B_SPAR false M := by
  have hb := hH.balance B_SPAR M
  have h1 : busCount AP.toAir tr pub B_SPAR true M = 0 := by
    unfold busCount
    exact busCount_go_zero tr pub _ _ M AP.tables 0 (fun t ht => by
      rw [Nat.zero_add]; exact tableBusCount_zero (fun i hi hb => by rw [O.parSend t ht i hi hb]; simp))
  have h2 : pubCount AP pub B_SPAR false M = 0 :=
    pubCount_zero (fun seg h1 h2 => by rw [O.parPub seg h1 h2]; simp) M
  omega

theorem tsd_le (O : ScanOwn AP tsd tp) (b : Nat) (s : Bool) (M : List Fp) :
    tableBusCount ScanDist.interactions tr tsd pub b s M ≤ busCount AP.toAir tr pub b s M := by
  have := busCount_go_ge tr pub b s M AP.tables 0 tsd O.lt
  rw [O.tab, Nat.zero_add] at this
  exact this

/-- A row of `ssdV3` receiving `M` on `SPAR` makes `M` a public message. -/
theorem pub_of_row (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {w : Nat} (hw : w < tr.height tsd)
    (hm : (ScanDist.interactions[0]!).multNat tr tsd w pub ≠ 0) :
    1 ≤ pubCount AP pub B_SPAR true ((ScanDist.interactions[0]!).msgVal tr tsd w pub) := by
  have h := tableBusCount_pos hw Scan.par_mem hm
  have h2 := tsd_le (tr := tr) (pub := pub) O B_SPAR false ((ScanDist.interactions[0]!).msgVal tr tsd w pub)
  rw [par_count hH O]
  exact Nat.le_trans (Nat.pos_of_ne_zero h) h2

theorem count_le_one_of_nodup {α : Type} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) (a : α) :
    l.count a ≤ 1 := List.nodup_iff_count.1 h a

/-- Two distinct rows of `ssdV3` receiving `M` on `SPAR` give a public count `≥ 2`. -/
theorem pub_two (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {w1 w2 : Nat}
    (hw1 : w1 < tr.height tsd) (hw2 : w2 < tr.height tsd) (hne : w1 ≠ w2)
    (hm1 : (ScanDist.interactions[0]!).multNat tr tsd w1 pub ≠ 0)
    (hm2 : (ScanDist.interactions[0]!).multNat tr tsd w2 pub ≠ 0)
    (he : (ScanDist.interactions[0]!).msgVal tr tsd w1 pub = (ScanDist.interactions[0]!).msgVal tr tsd w2 pub) :
    2 ≤ pubCount AP pub B_SPAR true ((ScanDist.interactions[0]!).msgVal tr tsd w1 pub) := by
  rw [par_count hH O]
  refine Nat.le_trans ?_ (tsd_le O _ _ _)
  rw [tableBusCount_eq, count_flatMap_rows]
  have row : ∀ w, w < tr.height tsd → (ScanDist.interactions[0]!).multNat tr tsd w pub ≠ 0 →
      (ScanDist.interactions[0]!).msgVal tr tsd w pub = (ScanDist.interactions[0]!).msgVal tr tsd w1 pub →
      1 ≤ (rowTraffic ScanDist.interactions tr tsd w pub B_SPAR false).count
        ((ScanDist.interactions[0]!).msgVal tr tsd w1 pub) := by
    intro w _ hm hmsg
    apply List.count_pos_iff.2
    apply List.mem_flatMap.2 ⟨_, Scan.par_mem, ?_⟩
    rw [if_pos ⟨rfl, rfl⟩, ← hmsg]
    exact List.mem_replicate.2 ⟨hm, rfl⟩
  exact sum_ge_two _ _ (List.mem_range.2 hw1) (List.mem_range.2 hw2) hne List.nodup_range
    (row w1 hw1 hm1 rfl) (row w2 hw2 hm2 he.symm)

end


/-! ## Request blocks of an instance -/

theorem b3_sum (b : Nat) (hb : b < 2 ^ 24) :
    b % 256 + 256 * (b / 256 % 256) + 65536 * (b / 65536 % 256) = b := by omega

theorem b2_sum (c : Nat) (hc : c < 2 ^ 16) : c % 256 + 256 * (c / 256 % 256) = c := by omega

theorem nodup_map_on {α β : Type} {f : α → β} {l : List α}
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (hl : l.Nodup) : (l.map f).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  exact hl.imp_of_mem fun ha hb hne he => hne (hf _ ha _ hb he)

theorem rawRec_lt {P : InstPub} (PO : ScanPubOk P) {τ c : Nat} (hτ : τ < 2013265921)
    (hc : c < P.raw.length) : ∀ x ∈ rawRec τ (rawAt P c) c, x < 2013265921 := by
  obtain ⟨hs, hr, -⟩ := PO.raw _ (rawAt_mem hc)
  have := PO.n64
  intro x hx
  simp only [rawRec, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first | omega | (simp only [PT_RAW]; omega) | exact Nat.lt_trans (UInt8.toNat_lt _) (by decide)

theorem parScan_lt {P : InstPub} (PO : ScanPubOk P) {τ : Nat} (hτ : τ < 2013265921) :
    ∀ x ∈ parScan τ P, x < 2013265921 := by
  have := PO.n64
  intro x hx
  simp only [parScan, b3, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first | omega | (simp only [PT_SCAN]; omega)

theorem scanRecs_lt {P : InstPub} (PO : ScanPubOk P) {τ : Nat} (hτ : τ < 2013265921) :
    ∀ R ∈ scanRecs τ P, ∀ x ∈ R, x < 2013265921 := by
  intro R hR
  simp only [scanRecs, List.mem_append] at hR
  rcases hR with hR | hR
  · split at hR
    · simp at hR
    · rw [List.mem_singleton.1 hR]; exact parScan_lt PO hτ
  · rw [rawRecs_eq] at hR
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hR
    exact rawRec_lt PO hτ (List.mem_range.1 hc)

theorem scanMsgs_nodup {P : InstPub} (PO : ScanPubOk P) {τ : Nat} (hτ : τ < 2013265921) :
    (scanMsgs τ P).Nodup := by
  refine nodup_map_on (fun x hx y hy he => ofNat_list_inj (scanRecs_lt PO hτ x hx)
    (scanRecs_lt PO hτ y hy) he) ?_
  have hraw : (rawRecs τ P).Nodup := by
    rw [rawRecs_eq]
    refine nodup_map_on (fun x hx y hy he => ?_) List.nodup_range
    have hx' := List.mem_range.1 hx; have hy' := List.mem_range.1 hy
    have := PO.len16
    simp only [rawRec, List.cons.injEq] at he
    omega
  unfold scanRecs
  rw [List.nodup_append]
  refine ⟨by split <;> simp, hraw, fun a ha b hb => ?_⟩
  split at ha
  · simp at ha
  · rw [List.mem_singleton.1 ha]
    rw [rawRecs_eq] at hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
    intro e
    have := congrArg (·[1]?) e
    simp [parScan, rawRec, PT_SCAN, PT_RAW] at this

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tsd tp : Nat}

theorem parV_raw {t w τ c : Nat} {q : RawReq} (h : Scan.parV tr t w = rawRec τ q c) :
    cv tr t w Scan.tau = τ ∧ (∀ i, i < 5 → (q.bm.getD i 0).toNat = cv tr t w (Scan.q i)) ∧
      cv tr t w Scan.clo = c % 256 ∧ cv tr t w Scan.chi = c / 256 % 256 ∧
      cv tr t w Scan.s = q.s ∧ cv tr t w Scan.r = q.r := by
  simp only [Scan.parV, rawRec, List.cons.injEq] at h
  obtain ⟨h0, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := h
  refine ⟨h0, fun i hi => ?_, h7, h8, h9, h10⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm
  · exact h5.symm
  · exact h6.symm

/-- **A request start of τ is a public raw request.** -/
theorem blk_rec (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub}
    (SP : ScanPub AP pub τ P) (PO : ScanPubOk P) {f : Nat} (hf : f < tr.height tsd)
    (hq : cv tr tsd f Scan.fQ = 1) (ht : cv tr tsd f Scan.tau = τ) :
    cv tr tsd f Scan.cid < P.raw.length ∧
      Scan.parV tr tsd f = rawRec τ (rawAt P (cv tr tsd f Scan.cid)) (cv tr tsd f Scan.cid) := by
  have hL := sd_local hH O
  have hS := Scan.SLocal.of_sd hL
  have hm := Scan.par_mult hS hf (Or.inl hq)
  have h1 := pub_of_row hH O hf hm
  have hk := Scan.fQ_le_kS hS hf hq
  have htag := Scan.tag_kS hS hf hk
  have hτ : τ < 2013265921 := ht ▸ cv_lt _ _
  rw [Scan.par_msg] at h1
  rw [SP.par _ (by simp [Scan.parV, ht]) (Or.inr (by simp [Scan.parV, htag, PT_RAW]))] at h1
  obtain ⟨R, hR, hRe⟩ := List.mem_map.1 (List.count_pos_iff.1 h1)
  have hlt := Scan.parV_lt hS hf
  simp only [scanRecs, List.mem_append] at hR
  rcases hR with hR | hR
  · split at hR
    · simp at hR
    · rw [List.mem_singleton.1 hR] at hRe
      have := ofNat_list_inj (parScan_lt PO hτ) hlt hRe
      have e := congrArg (·[1]?) this
      simp [parScan, Scan.parV, htag, PT_SCAN] at e
  · rw [rawRecs_eq] at hR
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hR
    have hc' := List.mem_range.1 hc
    have he := (ofNat_list_inj (rawRec_lt PO hτ hc') hlt hRe).symm
    obtain ⟨-, -, hlo, hhi, -, -⟩ := parV_raw he
    have hcid := (Scan.row_start hS hf hq).2.2.2.2.2.2.1
    have := PO.len16
    have e : cv tr tsd f Scan.cid = c := by
      rw [hcid, hlo, hhi, b2_sum c (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e]
    exact ⟨hc', he⟩

/-- What a request start of τ holds. -/
structure BlkOk (tr : Trace Fp) (tsd f : Nat) (P : InstPub) : Prop where
  lt : cv tr tsd f Scan.cid < P.raw.length
  bm : ∀ i, i < 5 → ((rawAt P (cv tr tsd f Scan.cid)).bm.getD i 0).toNat = cv tr tsd f (Scan.q i)
  s : cv tr tsd f Scan.s = (rawAt P (cv tr tsd f Scan.cid)).s
  r : cv tr tsd f Scan.r = (rawAt P (cv tr tsd f Scan.cid)).r
  nn : cv tr tsd f Scan.nn = P.n
  link : cv tr tsd f Scan.link =
    (rawAt P (cv tr tsd f Scan.cid)).s * P.n + (rawAt P (cv tr tsd f Scan.cid)).r
  base : cv tr tsd f Scan.base = P.params.base
  dd : cv tr tsd f Scan.dd = P.params.maxSingleGrant - P.params.base

/-- **The data of a request start of τ.** -/
theorem blk_ok (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub}
    (SP : ScanPub AP pub τ P) (PO : ScanPubOk P) {f : Nat} (hf : f < tr.height tsd)
    (hq : cv tr tsd f Scan.fQ = 1) (ht : cv tr tsd f Scan.tau = τ) : BlkOk tr tsd f P := by
  have hL := sd_local hH O
  have hS := Scan.SLocal.of_sd hL
  have hτ : τ < 2013265921 := ht ▸ cv_lt _ _
  obtain ⟨hc, he⟩ := blk_rec hH O SP PO hf hq ht
  obtain ⟨-, hbm, -, -, hs, hr⟩ := parV_raw he
  -- the section's param row
  obtain ⟨p, hp, hpk, hpc⟩ := Scan.param_of hL f hf hq
  have hpf : p < tr.height tsd := by omega
  have hpt : cv tr tsd p Scan.tau = τ := by rw [← hpc Scan.tau (by simp [Scan.instCols]), ht]
  have hm := Scan.par_mult hS hpf (Or.inr hpk)
  have h1 := pub_of_row hH O hpf hm
  have htag := Scan.tag_kP hS hpf hpk
  rw [Scan.par_msg] at h1
  rw [SP.par _ (by simp [Scan.parV, hpt]) (Or.inl (by simp [Scan.parV, htag, PT_SCAN]))] at h1
  obtain ⟨R, hR, hRe⟩ := List.mem_map.1 (List.count_pos_iff.1 h1)
  have hlt := Scan.parV_lt hS hpf
  have hpar : Scan.parV tr tsd p = parScan τ P := by
    simp only [scanRecs, List.mem_append] at hR
    rcases hR with hR | hR
    · split at hR
      · simp at hR
      · rw [List.mem_singleton.1 hR] at hRe
        exact (ofNat_list_inj (parScan_lt PO hτ) hlt hRe).symm
    · rw [rawRecs_eq] at hR
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hR
      have := ofNat_list_inj (rawRec_lt PO hτ (List.mem_range.1 hc)) hlt hRe
      have e := congrArg (·[1]?) this
      simp [rawRec, Scan.parV, htag, PT_RAW] at e
  simp only [Scan.parV, parScan, b3, List.cons_append, List.nil_append, List.cons.injEq] at hpar
  obtain ⟨-, -, q0, q1, q2, q3, q4, qlo, qhi, -, -, -⟩ := hpar
  obtain ⟨hb, hd, -⟩ := Scan.row_param hS hpf hpk
  have hnn : cv tr tsd p Scan.chi = cv tr tsd p Scan.nn :=
    Scan.eq_of_gate hS hpf (by simp [Scan.constraints, Scan.shared, Scan.own, Scan.body]) hpk
  have b24 := PO.base24; have d24 := PO.d24
  have ebase : cv tr tsd f Scan.base = P.params.base := by
    rw [hpc Scan.base (by simp [Scan.instCols]), hb, q0, q1, q2, b3_sum _ b24,
      Nat.mod_eq_of_lt (by omega)]
  have edd : cv tr tsd f Scan.dd = P.params.maxSingleGrant - P.params.base := by
    rw [hpc Scan.dd (by simp [Scan.instCols]), hd, q3, q4, qlo, b3_sum _ d24,
      Nat.mod_eq_of_lt (by omega)]
  have enn : cv tr tsd f Scan.nn = P.n := by
    rw [hpc Scan.nn (by simp [Scan.instCols]), ← hnn, qhi]
  obtain ⟨hs', hr', -⟩ := PO.raw _ (rawAt_mem hc)
  have hn := PO.n64
  have hlink := (Scan.row_start hS hf hq).2.2.2.2.2.2.2
  refine ⟨hc, hbm, hs, hr, enn, ?_, ebase, edd⟩
  rw [hlink, hs, hr, enn]
  have : (rawAt P (cv tr tsd f Scan.cid)).s * P.n ≤ 64 * 64 := Nat.mul_le_mul (by omega) hn
  exact Nat.mod_eq_of_lt (by omega)

/-- **Request starts of τ have distinct `cid`s.** -/
theorem blk_unique (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub}
    (SP : ScanPub AP pub τ P) (PO : ScanPubOk P) {f1 f2 : Nat}
    (hf1 : f1 < tr.height tsd) (hq1 : cv tr tsd f1 Scan.fQ = 1) (ht1 : cv tr tsd f1 Scan.tau = τ)
    (hf2 : f2 < tr.height tsd) (hq2 : cv tr tsd f2 Scan.fQ = 1) (ht2 : cv tr tsd f2 Scan.tau = τ)
    (hc : cv tr tsd f1 Scan.cid = cv tr tsd f2 Scan.cid) : f1 = f2 := by
  have hL := sd_local hH O
  have hS := Scan.SLocal.of_sd hL
  have hτ : τ < 2013265921 := ht1 ▸ cv_lt _ _
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨-, he1⟩ := blk_rec hH O SP PO hf1 hq1 ht1
  obtain ⟨-, he2⟩ := blk_rec hH O SP PO hf2 hq2 ht2
  have hM : (ScanDist.interactions[0]!).msgVal tr tsd f1 pub =
      (ScanDist.interactions[0]!).msgVal tr tsd f2 pub := by
    rw [Scan.par_msg, Scan.par_msg, he1, he2, hc]
  have h2 := pub_two hH O hf1 hf2 hne (Scan.par_mult hS hf1 (Or.inl hq1))
    (Scan.par_mult hS hf2 (Or.inl hq2)) hM
  have htag := Scan.tag_kS hS hf1 (Scan.fQ_le_kS hS hf1 hq1)
  rw [Scan.par_msg] at h2
  rw [SP.par _ (by simp [Scan.parV, ht1]) (Or.inr (by simp [Scan.parV, htag, PT_RAW]))] at h2
  have := List.nodup_iff_count.1 (scanMsgs_nodup PO hτ) ((Scan.parV tr tsd f1).map Fp.ofNat)
  omega

/-- **Every public raw request of τ has a request start.** -/
theorem blk_exists (hH : HoldsP AP pub tr) (O : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub}
    (SP : ScanPub AP pub τ P) (PO : ScanPubOk P) (hτ : τ < 2013265921) {c : Nat}
    (hc : c < P.raw.length) :
    ∃ f, f < tr.height tsd ∧ cv tr tsd f Scan.fQ = 1 ∧ cv tr tsd f Scan.tau = τ ∧
      cv tr tsd f Scan.cid = c := by
  have hL := sd_local hH O
  have hS := Scan.SLocal.of_sd hL
  obtain ⟨M, hMd⟩ : ∃ M, M = (rawRec τ (rawAt P c) c).map Fp.ofNat := ⟨_, rfl⟩
  have hmem : M ∈ scanMsgs τ P := by
    refine List.mem_map.2 ⟨_, ?_, hMd.symm⟩
    simp only [scanRecs, List.mem_append]
    right; rw [rawRecs_eq]; exact List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩
  have hpc : 1 ≤ pubCount AP pub B_SPAR true M := by
    rw [SP.par M (by simp [hMd, rawRec]) (Or.inr (by simp [hMd, rawRec]))]
    exact List.count_pos_iff.2 hmem
  rw [par_count hH O] at hpc
  unfold busCount at hpc
  obtain ⟨t, ht, htc⟩ := busCount_go_pos tr pub _ _ M AP.tables 0 (Nat.pos_iff_ne_zero.1 hpc)
  rw [Nat.zero_add] at htc
  obtain ⟨w, hw, i, hi, hb, hs, hmsg, hm⟩ := exists_of_tableBusCount htc
  by_cases htd : t = tsd
  · subst htd
    rw [O.tab] at hi
    have hi0 := Scan.par_cases i hi hb
    subst hi0
    rw [Scan.par_msg] at hmsg
    have hlt := Scan.parV_lt hS hw
    have he := ofNat_list_inj hlt (rawRec_lt PO hτ hc) (hmsg.trans hMd)
    have htag : cv tr t w Scan.kP + 2 * cv tr t w Scan.kS + 3 * cv tr t w Scan.kSh +
        4 * cv tr t w Scan.kC = 2 := by
      have := congrArg (·[1]?) he
      simpa [Scan.parV, rawRec, PT_RAW] using this
    have hq := Scan.fQ_of_par hS hw hm htag
    obtain ⟨ht', -, hlo, hhi, -, -⟩ := parV_raw he
    have hcid := (Scan.row_start hS hw hq).2.2.2.2.2.2.1
    have := PO.len16
    exact ⟨w, hw, hq, ht', by rw [hcid, hlo, hhi, b2_sum c (by omega), Nat.mod_eq_of_lt (by omega)]⟩
  · have h1 := O.parTag t ht htd i hi hb
    have e := congrArg (·[1]?) hmsg
    rw [hMd] at e
    simp only [Interaction.msgVal, List.getElem?_map, h1, rawRec, List.map_cons,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at e
    have : (k 0).eval tr t w pub = Fp.ofNat 0 := Scan.eval_ofNat (by simp [zev_k])
    rw [this] at e
    exact absurd ((Proc.ofNat_cv_eq (by decide) (by decide)).1 e) (by simp [PT_RAW])

end

end ZkFormal.NearV3.Sched
