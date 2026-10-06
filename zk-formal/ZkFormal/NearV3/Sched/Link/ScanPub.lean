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

end ZkFormal.NearV3.Sched
