import StateM5a.VerRead

/-!
# StateM5a.VerStore — `OldOK` / `NewOK` of the `BR` rows from `VER` balance

The version store is `σ = storeOf vers` for any list `vers` of `(id, record)` with distinct ids that
contains every `BR` row publishing its new node under a version id (`(brVid r, brNew r)`; the `SN`
rows' entries are added by the `SN` side — `brVers` is the `BR` part, `brVers_nodup`).  With the
SHA-256 facts of the hashing rows as premises (`BrHashed`: a row that hashes its old / new node
— `gsha`, resp. `gnew` with `nref = 0` — publishes a record `Hashed` to its digest):

* **`br_oldOK`**: every active `BR` row's old record is `OldOK σ brIn brOld` — hashed here, or
  read on `VER` (`VerRead.br_rd_part`): under a version id all 17 parts come from the one row with
  that id (`br_vid`, `br_rid`), so the record is that row's new record; under a digest every part
  comes from a publisher whose record is hashed to it, all equal by `Sha256CR`
  (`hashed_agree`), so the parts assemble to that record (`VerDec.dec_of_parts`);
* **`br_newOK`**: a row with a new node publishes `NewOK σ brOut brNew`.
-/

namespace StateM5a.VerStore

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.VerBus StateM5a.VerDec StateM5a.VerRead
open StateM5a.KeyDecode StateM5a.FieldRows

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem split3 {f g : Expr → Fp} {a1 b1 a2 b2 a3 b3 : List Expr} (h1 : a1.length = b1.length)
    (h2 : a2.length = b2.length) (h : (a1 ++ a2 ++ a3).map f = (b1 ++ b2 ++ b3).map g) :
    a1.map f = b1.map g ∧ a2.map f = b2.map g ∧ a3.map f = b3.map g := by
  simp only [List.map_append] at h
  obtain ⟨e12, e3⟩ := List.append_inj h (by simp [h1, h2])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp [h1])
  exact ⟨e1, e2, e3⟩

theorem refOf_dig (fl : Fp) (ls : List Fp) (hl : ls.length = 16) (h : fl.toNat = 0) :
    refOf fl ls = .dig (bytesOf ls) := by
  simp only [refOf, Tape.refDec, List.getD_cons_zero, h, ↓reduceIte, List.drop_succ_cons, List.drop_zero,
    List.take_of_length_le (show ls.length ≤ 16 by omega), bytesOf]

theorem refOf_vid (fl : Fp) (ls : List Fp) (h : fl.toNat ≠ 0) :
    refOf fl ls = .vid (ls.getD 0 0).toNat := by
  simp only [refOf, Tape.refDec, List.getD_cons_zero, h, ↓reduceIte, List.getD_cons_succ]

theorem pack2_len (f : Nat → Expr) : (pack2 f).length = 16 := by simp [pack2]

section
variable {tr : Trace Fp} {pub : List Fp}

/-- The version id of `BR` row `r`'s new node: limb 0 of its ref `hn`. -/
def brVid (tr : Trace Fp) (pub : List Fp) (r : Nat) : Nat :=
  (((pack2 fun b => Br.c "hn" b).map (E tr 2 r pub)).getD 0 0).toNat

/-- **Hashing rows** (premise: the SHA-256 table and the serialization layout): a row hashing its
old node, or its new node under a digest, publishes a record hashed to that digest. -/
structure BrHashed (tr : Trace Fp) (pub : List Fp) : Prop where
  old : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "gsha") = 1 →
    Hashed (brOld tr pub r) (bytesOf ((pack2 fun b => Br.c "ho" b).map (E tr 2 r pub)))
  new : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "gnew") = 1 → ev tr 2 r pub (Br.c "nref") = 0 →
    Hashed (brNew tr pub r) (bytesOf ((pack2 fun b => Br.c "hn" b).map (E tr 2 r pub)))

theorem brVid_val {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    {r : Nat} (hr : r < tr.height 2) (hn : ev tr 2 r pub (Br.c "nref") = 1) :
    brVid tr pub r = (256 * (2 ^ 25 + 2 * r + 1)) % P := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨h0, h1⟩ := FieldVer.br_vid hc hn
  have hrid := KeyDigest.br_rid hH r hr
  have hlog : tr.log 2 ≤ 20 := (hH.logBound 2 (by simp [fullAir, m5aAir])).2
  have hH2 : tr.height 2 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hN : ev tr 2 r pub Br.nidN = 2 ^ 25 + 2 * r + 1 := by
    unfold Br.nidN
    rw [ev_hadd, ev_hadd, ev_one, show K ID_BR = Expr.const ID_BR from rfl, ev_const,
      show sm 2 (Br.c "rid") = Expr.mul (Expr.const 2) (Br.c "rid") from rfl, ev_mul, ev_const, hrid]
    simp only [ID_BR]
    omega
  have hb1 := h1 0 (by decide)
  unfold brVid
  simp only [pack2, List.map_map, List.range, List.range.loop, List.map_cons, List.getD_cons_zero, Function.comp]
  show ev tr 2 r pub (K 256 * Br.c "hn" (2 * 0) + Br.c "hn" (2 * 0 + 1)) = _
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const]
  simp only [Nat.mul_zero, Nat.zero_add] at hb1 ⊢
  rw [h0, hb1, hN]
  simp only [Nat.reduceMod]; omega

/-- The pieces of a read part equal to an old publication. -/
theorem rd_old {r r' p : Nat} (h : (rdE p).map (E tr 2 r pub) = (oldE p).map (E tr 2 r' pub)) :
    E tr 2 r pub (Br.c "oref") = E tr 2 r' pub 0 ∧
    (pack2 fun b => Br.c "ho" b).map (E tr 2 r pub) = (pack2 fun b => Br.c "ho" b).map (E tr 2 r' pub) ∧
    brOldPay tr pub r p = brOldPay tr pub r' p := by
  obtain ⟨e1, e2, e3⟩ := split3 (by rfl) (by simp [pack2]) h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at e1
  exact ⟨e1.2.2.1, e2, e3⟩

theorem rd_new {r r' p : Nat} (h : (rdE p).map (E tr 2 r pub) = (newE p).map (E tr 2 r' pub)) :
    E tr 2 r pub (Br.c "oref") = E tr 2 r' pub (Br.c "nref") ∧
    (pack2 fun b => Br.c "ho" b).map (E tr 2 r pub) = (pack2 fun b => Br.c "hn" b).map (E tr 2 r' pub) ∧
    brOldPay tr pub r p = brNewPay tr pub r' p := by
  obtain ⟨e1, e2, e3⟩ := split3 (by rfl) (by simp [pack2]) h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at e1
  exact ⟨e1.2.2.1, e2, e3⟩

set_option maxHeartbeats 4000000 in
theorem flag_le {r : Nat} (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (s : String)
    (hs : s = "oref" ∨ s = "nref" ∨ s = "gsha") : ev tr 2 r pub (Br.c s) ≤ 1 := by
  apply bool_le
  apply FieldRows.hold (L := Br.constraints) rfl hc
  unfold Br.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  refine ⟨s, ?_, rfl⟩
  rcases hs with rfl | rfl | rfl <;> simp

theorem toNat_zero_expr {r : Nat} : (E tr 2 r pub (0 : Expr)).toNat = 0 := rfl

/-- `Hashed` as the digest case of `OldOK`. -/
theorem oldOK_dig {σ : Store} {h : Bytes} {R : Rec} (hR : Hashed R h) : OldOK σ (.dig h) R :=
  Or.inr ⟨h, rfl, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2⟩

set_option maxHeartbeats 16000000 in
/-- **The old record of every active `BR` row is `OldOK`.** -/
theorem br_oldOK {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) (hCR : Walk.Sha256CR) (hHs : BrHashed tr pub)
    (vers : List (Nat × Rec))
    (hv : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "nref") = 1 → ev tr 2 r pub (Br.c "gnew") = 1 →
      storeOf vers (brVid tr pub r) = some (brNew tr pub r))
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1) :
    OldOK (storeOf vers) (brIn tr pub r) (brOld tr pub r) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hlog : tr.log 2 ≤ 20 := (hH.logBound 2 (by simp [fullAir, m5aAir])).2
  have hH2 : tr.height 2 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hsb := flag_le hc "gsha" (Or.inr (Or.inr rfl))
  by_cases hs : ev tr 2 r pub (Br.c "gsha") = 1
  · -- hashed by this row
    have ho := FieldVer.br_gsha_dig hc hs
    unfold brIn
    rw [refOf_dig _ _ (pack2_len fun b => Br.c "ho" b) ho]
    exact oldOK_dig (hHs.old r hr hs)
  · have hs0 : ev tr 2 r pub (Br.c "gsha") = 0 := by omega
    have hrd : (Br.gold - Br.c "gsha").eval tr 2 r pub = 1 := by
      apply fp_of_ev1; rw [ev_sub, hg, hs0]
    have hex := fun p (hp : p < 17) => br_rd_part hH hxV hr hrd p hp
    have hob := flag_le hc "oref" (Or.inl rfl)
    rcases (by omega : ev tr 2 r pub (Br.c "oref") = 0 ∨ ev tr 2 r pub (Br.c "oref") = 1) with ho | ho
    · -- under a digest: every part comes from a record hashed to it
      have hdig : brIn tr pub r = .dig (bytesOf ((pack2 fun b => Br.c "ho" b).map (E tr 2 r pub))) := by
        unfold brIn; exact refOf_dig _ _ (pack2_len fun b => Br.c "ho" b) ho
      have hpart : ∀ p, p < 17 → ∃ Q : Nat → List Fp, ∃ R : Rec, brDec.dec Q = R ∧
          Hashed R (bytesOf ((pack2 fun b => Br.c "ho" b).map (E tr 2 r pub))) ∧
          brOldPay tr pub r p = Q p := by
        intro p hp
        obtain ⟨r', hr', hc'⟩ := hex p hp
        rcases hc' with ⟨hgs, hm⟩ | ⟨hgn, hm⟩
        · obtain ⟨-, el, ep⟩ := rd_old hm
          refine ⟨brOldPay tr pub r', brOld tr pub r', brOld_dec.symm, ?_, ep⟩
          rw [el]; exact hHs.old r' hr' hgs
        · obtain ⟨ef, el, ep⟩ := rd_new hm
          have hn0 : ev tr 2 r' pub (Br.c "nref") = 0 := by
            have := congrArg Fp.toNat ef
            show (E tr 2 r' pub (Br.c "nref")).toNat = 0
            rw [← this]; exact ho
          refine ⟨brNewPay tr pub r', brNew tr pub r', brNew_dec.symm, ?_, ep⟩
          rw [el]; exact hHs.new r' hr' hgn hn0
      let Qf : Nat → Nat → List Fp := fun p => if h : p < 17 then Classical.choose (hpart p h) else fun _ => []
      have hQ : ∀ p (hp : p < 17), ∃ R : Rec, brDec.dec (Qf p) = R ∧
          Hashed R (bytesOf ((pack2 fun b => Br.c "ho" b).map (E tr 2 r pub))) ∧
          brOldPay tr pub r p = Qf p p := by
        intro p hp
        simp only [Qf, dif_pos hp]
        exact Classical.choose_spec (hpart p hp)
      obtain ⟨R0, hR0, hH0, -⟩ := hQ 0 (by decide)
      have hall : ∀ p, p < 17 → brDec.dec (Qf p) = R0 := by
        intro p hp
        obtain ⟨R, hR, hHR, -⟩ := hQ p hp
        rw [hR]; exact hashed_agree hCR hHR hH0
      have hrec : brOld tr pub r = R0 := by
        rw [brOld_dec]
        exact dec_of_parts brDec Qf hall (fun p hp => by rw [(hQ p hp).choose_spec.2.2])
      rw [hdig, hrec]
      exact oldOK_dig hH0
    · -- under a version id: every part comes from the one row with that id
      have hvid : brIn tr pub r = .vid (((pack2 fun b => Br.c "ho" b).map (E tr 2 r pub)).getD 0 0).toNat := by
        unfold brIn; exact refOf_vid _ _ (by show ev tr 2 r pub (Br.c "oref") ≠ 0; omega)
      have hpart : ∀ p, p < 17 → ∃ r', r' < tr.height 2 ∧ ev tr 2 r' pub (Br.c "nref") = 1 ∧
          ev tr 2 r' pub (Br.c "gnew") = 1 ∧
          (pack2 fun b => Br.c "ho" b).map (E tr 2 r pub) = (pack2 fun b => Br.c "hn" b).map (E tr 2 r' pub) ∧
          brOldPay tr pub r p = brNewPay tr pub r' p := by
        intro p hp
        obtain ⟨r', hr', hc'⟩ := hex p hp
        rcases hc' with ⟨hgs, hm⟩ | ⟨hgn, hm⟩
        · exfalso
          obtain ⟨ef, -, -⟩ := rd_old hm
          have := congrArg Fp.toNat ef
          rw [toNat_zero_expr] at this
          have : ev tr 2 r pub (Br.c "oref") = 0 := this
          omega
        · obtain ⟨ef, el, ep⟩ := rd_new hm
          have hn1 : ev tr 2 r' pub (Br.c "nref") = 1 := by
            have := congrArg Fp.toNat ef
            show (E tr 2 r' pub (Br.c "nref")).toNat = 1
            rw [← this]; exact ho
          exact ⟨r', hr', hn1, hgn, el, ep⟩
      obtain ⟨r0, hr0, hn0, hg0, hl0, -⟩ := hpart 0 (by decide)
      have hsame : ∀ p, p < 17 → brOldPay tr pub r p = brNewPay tr pub r0 p := by
        intro p hp
        obtain ⟨r', hr', hn', hg', hl', hp'⟩ := hpart p hp
        have v1 := brVid_val hH hr' hn'
        have v0 := brVid_val hH hr0 hn0
        have e : brVid tr pub r' = brVid tr pub r0 := by unfold brVid; rw [← hl', ← hl0]
        rw [v1, v0] at e
        have : r' = r0 := by omega
        rw [hp', this]
      have hrec : brOld tr pub r = brNew tr pub r0 := by
        rw [brOld_dec, brNew_dec]
        exact dec_of_parts brDec (fun _ => brNewPay tr pub r0) (fun _ _ => rfl)
          (fun p hp => by rw [hsame p hp])
      left
      refine ⟨brVid tr pub r0, ?_, ?_⟩
      · rw [hvid]; unfold brVid; rw [hl0]
      · rw [hrec]; exact hv r0 hr0 hn0 hg0

/-- **A row's new record is `NewOK`.** -/
theorem br_newOK {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hHs : BrHashed tr pub) (vers : List (Nat × Rec))
    (hv : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "nref") = 1 → ev tr 2 r pub (Br.c "gnew") = 1 →
      storeOf vers (brVid tr pub r) = some (brNew tr pub r))
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub (Br.c "gnew") = 1) :
    NewOK (storeOf vers) (brOut tr pub r) (brNew tr pub r) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hnb := flag_le hc "nref" (Or.inr (Or.inl rfl))
  rcases (by omega : ev tr 2 r pub (Br.c "nref") = 0 ∨ ev tr 2 r pub (Br.c "nref") = 1) with hn | hn
  · have hR := hHs.new r hr hg hn
    right
    refine ⟨_, ?_, hR.1, hR.2.2.2⟩
    unfold brOut; exact refOf_dig _ _ (pack2_len fun b => Br.c "hn" b) hn
  · left
    refine ⟨brVid tr pub r, ?_, hv r hr hn hg⟩
    unfold brOut; exact refOf_vid _ _ (by show ev tr 2 r pub (Br.c "nref") ≠ 0; omega)

/-! ## The `BR` part of the store -/

/-- The `BR` rows' version-id publications `(id, new record)`. -/
def brVers (tr : Trace Fp) (pub : List Fp) : List (Nat × Rec) :=
  ((List.range (tr.height 2)).filter fun r =>
      decide (ev tr 2 r pub (Br.c "nref") = 1 ∧ ev tr 2 r pub (Br.c "gnew") = 1)).map
    fun r => (brVid tr pub r, brNew tr pub r)

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α), (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) →
    l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hn => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hn
    refine ⟨fun hm => ?_, nodup_map_on f l (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)) hn.2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    have := h b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e
    subst this; exact hn.1 hb

/-- The `BR` version ids are distinct (`ID_BR + 2·rid + 1`, `rid = r`). -/
theorem brVers_nodup {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr) :
    ((brVers tr pub).map (·.1)).Nodup := by
  have hlog : tr.log 2 ≤ 20 := (hH.logBound 2 (by simp [fullAir, m5aAir])).2
  have hH2 : tr.height 2 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  unfold brVers
  rw [List.map_map]
  refine nodup_map_on _ _ (fun a ha b hb e => ?_) (List.nodup_range.filter _)
  obtain ⟨ha1, ha2⟩ := List.mem_filter.1 ha
  obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
  simp only [decide_eq_true_eq] at ha2 hb2
  have ha0 := List.mem_range.1 ha1; have hb0 := List.mem_range.1 hb1
  simp only [Function.comp] at e
  rw [brVid_val hH ha0 ha2.1, brVid_val hH hb0 hb2.1] at e
  omega

/-- **The store premise** for `vers = brVers ++ rest` with distinct ids (`rest`: the `SN` rows'
publications). -/
theorem brVers_hv {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (rest : List (Nat × Rec)) (hnd : ((brVers tr pub ++ rest).map (·.1)).Nodup) :
    ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "nref") = 1 → ev tr 2 r pub (Br.c "gnew") = 1 →
      storeOf (brVers tr pub ++ rest) (brVid tr pub r) = some (brNew tr pub r) := by
  intro r hr hn hg
  apply storeOf_mem hnd
  apply List.mem_append_left
  exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨List.mem_range.2 hr, by simp [hn, hg]⟩, rfl⟩

end

end StateM5a.VerStore
