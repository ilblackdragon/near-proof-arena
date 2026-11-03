import StateM5a.M5bFinal

/-!
# StateM5a.StHost — the producer premise `HostReqs` is met by the T1 tape (M5a-8)

`M5bFinal.m5b_final` takes the producer premise `StSound.HostReqs` (the execution side's `SREQ` /
`HB` sends are the request list `reqs`, memory a function of `(ts, pos)`, bounds, `(seg, ts)`
order).  On T1 the execution side is the public tape `host`; `tracegen.py` (`st_tape`) writes, per
request, its `SREQ(ts, pr, seg, klen, kptr, vlen, vptr)` and the `HB(ts, pos, byte)` entries of its
key and (`storage_write`) value bytes: **`hostOf reqs`**.

**`hostReqs_of_tape`**: for *every* trace, `HostReqs (fullAir D (m5bX (hostOf reqs) …)) tr pub
(hostOf reqs) reqs` holds as soon as the request list itself satisfies three checks on public data:
`MemAgree` (two `HB` entries at the same `(ts, pos)` carry the same byte — true when each call's
key and value regions do not overlap with different bytes), the bounds (`< p`), and the
`(seg, ts)` order.  So the premise is not vacuous: on T1 it reduces to a check of the tape
(and `HostOK (hostOf reqs)` holds by construction, `hostOK_of`).
-/

namespace StateM5a.StHost

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.KeyDecode StateM5a.Tape
open StateM5a.M5b StateM5a.StSound StateM5a.FieldRows StateM5a.DecodeM5a NearSpec

local notation "P" => 2013265921

/-- The `HB` entries of the bytes `bs` read at `ptr, ptr + 1, …` by call `ts`. -/
def hbE (ts ptr : Nat) (bs : Bytes) : List (Nat × Bool × List Nat) :=
  (List.range bs.length).map fun j => (B_HB, true, [ts, ptr + j, (bs.getD j 0).toNat])

/-- A request's `SREQ` entry. -/
def sreqE (q : Req) : Nat × Bool × List Nat :=
  (B_SREQ, true, [q.ts, if q.pr then 1 else 0, q.seg, q.key.length, q.kptr,
    if q.pr then q.val.length else 0, q.vptr])

/-- One request's tape entries: its `SREQ`, its key bytes, its value bytes (`storage_write`). -/
def reqTape (q : Req) : List (Nat × Bool × List Nat) :=
  sreqE q :: (hbE q.ts q.kptr q.key ++ if q.pr then hbE q.ts q.vptr q.val else [])

/-- **The T1 host tape** of a request list (`tracegen.py`, `st_tape`). -/
def hostOf (reqs : List Req) : List (Nat × Bool × List Nat) := reqs.flatMap reqTape

/-- The `HB` messages of the tape, as field elements. -/
def hbMsgs (reqs : List Req) : List (List Fp) :=
  ((hostOf reqs).filter fun e => decide (e.1 = B_HB)).map fun e => e.2.2.map Fp.ofNat

/-- **The reads agree**: two `HB` messages with the same `(ts, pos)` are equal. -/
def MemAgree (reqs : List Req) : Prop :=
  ∀ m₁ ∈ hbMsgs reqs, ∀ m₂ ∈ hbMsgs reqs, m₁.take 2 = m₂.take 2 → m₁ = m₂

theorem mem_hbE {ts ptr : Nat} {bs : Bytes} {e : Nat × Bool × List Nat} (h : e ∈ hbE ts ptr bs) :
    e.1 = B_HB ∧ e.2.1 = true := by
  simp only [hbE, List.mem_map] at h
  obtain ⟨j, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem mem_reqTape {q : Req} {e : Nat × Bool × List Nat} (h : e ∈ reqTape q) :
    e = sreqE q ∨ (e.1 = B_HB ∧ e.2.1 = true) := by
  simp only [reqTape, List.mem_cons, List.mem_append] at h
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (mem_hbE h)
  · split at h
    · exact .inr (mem_hbE h)
    · exact absurd h List.not_mem_nil

theorem mem_hostOf {reqs : List Req} {e : Nat × Bool × List Nat} (h : e ∈ hostOf reqs) :
    (∃ q ∈ reqs, e = sreqE q) ∨ (e.1 = B_HB ∧ e.2.1 = true) := by
  simp only [hostOf, List.mem_flatMap] at h
  obtain ⟨q, hq, he⟩ := h
  rcases mem_reqTape he with h | h
  · exact .inl ⟨q, hq, h⟩
  · exact .inr h

/-- The tape only sends on `SREQ` and `HB`. -/
theorem hostOK_of (reqs : List Req) : HostOK (hostOf reqs) := by
  intro e he
  rcases mem_hostOf he with ⟨q, -, rfl⟩ | h
  · exact .inl rfl
  · exact .inr h.1

theorem host_sends (reqs : List Req) : ∀ e ∈ hostOf reqs, e.2.1 = true := by
  intro e he
  rcases mem_hostOf he with ⟨q, -, rfl⟩ | h
  · rfl
  · exact h.2

section
variable {tr : Trace Fp} {pub : List Fp}

theorem eval_const (c : Nat) {t r : Nat} : (Expr.const c).eval tr t r pub = Fp.ofNat c :=
  Fp.ext (by
    show ev tr t r pub (Expr.const c) = (Fp.ofNat c).toNat
    rw [ev_const, KeyDigest.ofNat_toNat'])

theorem stb_no_host (b : Nat) (hb : b = B_SREQ ∨ b = B_HB) :
    Stb.interactions.filter (fun i => decide (i.bus = b ∧ i.send = true)) = [] := by
  rcases hb with rfl | rfl <;> decide

theorem stw_no_host (b : Nat) (hb : b = B_SREQ ∨ b = B_HB) :
    Stw.interactions.filter (fun i => decide (i.bus = b ∧ i.send = true)) = [] := by
  rcases hb with rfl | rfl <;> decide

theorem host_bus_ge {b : Nat} (hb : b = B_SREQ ∨ b = B_HB) : ¬ b < NUM_BUSES_WS := by
  rcases hb with rfl | rfl <;> decide

/-- **On `SREQ` / `HB` only the host tape sends** (row 0 of table 15). -/
theorem sent_host {D nb np : Nat} {host : List (Nat × Bool × List Nat)} (hh : HostOK host)
    {prev post : Bytes} {n b : Nat} (hb : b = B_SREQ ∨ b = B_HB) {m : List Fp} :
    m ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub b true ↔
      m ∈ tapeMsgs tr 15 pub host b true := by
  have h15 : (fullAir D (m5bX host prev post n) nb np).tables[15]'(by rw [bx_len]; omega) = tapeTable host :=
    x_get (t := 15) (k := 3) rfl _ (by rw [m5bX_len]; omega)
  constructor
  · intro hm
    rcases bus_split hm with ⟨t, ht, r, hr, i, hi, hib, -, -, -⟩ | ⟨k, hk, r, hr, i, hi, hib, hs, hp, he⟩
    · have := of_decide_eq_true (List.all_eq_true.1 (m5a_busesLt D t ht) i hi)
      rw [hib] at this
      exact absurd this (host_bus_ge hb)
    · rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, -⟩
      · rcases hb with rfl | rfl <;> exact absurd (hib.symm.trans h) (by decide)
      · exact (filter_none (stb_no_host b hb) h hib hs).elim
      · exact (filter_none (stw_no_host b hb) h hib hs).elim
      · have hrow : m ∈ rowBusList (tapeTable host).interactions tr 15 r pub b true :=
          mem_rowBusList.2 ⟨i, hi, hib, hs, hp, he⟩
        rw [tape_row] at hrow
        split at hrow
        · exact hrow
        · exact absurd hrow List.not_mem_nil
  · intro hm
    rw [← tape_table (tr := tr) (pub := pub) host 15 b true] at hm
    obtain ⟨r, hr, hrow⟩ := mem_tableBusList.1 hm
    obtain ⟨i, hi, hib, hs, hp, he⟩ := mem_rowBusList.1 hrow
    exact mem_busList.2 ⟨15, by rw [bx_len]; omega, r, hr, i, by rw [h15]; exact hi, hib, hs, hp, he⟩

theorem tapeMsgs_mem {host : List (Nat × Bool × List Nat)} {t b : Nat} {s : Bool} {m : List Fp} :
    m ∈ tapeMsgs tr t pub host b s ↔ ∃ e ∈ host, e.1 = b ∧ e.2.1 = s ∧ m = e.2.2.map Fp.ofNat := by
  simp only [tapeMsgs, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, h1, h2⟩, rfl⟩
    exact ⟨e, he, h1, h2, List.map_congr_left fun c _ => eval_const (tr := tr) (pub := pub) (t := t) (r := 0) c⟩
  · rintro ⟨e, he, h1, h2, rfl⟩
    exact ⟨e, ⟨he, h1, h2⟩, List.map_congr_left fun c _ => (eval_const (tr := tr) (pub := pub) (t := t) (r := 0) c).symm⟩

theorem hb_msgs {reqs : List Req} {m : List Fp} :
    m ∈ tapeMsgs tr 15 pub (hostOf reqs) B_HB true ↔ m ∈ hbMsgs reqs := by
  rw [tapeMsgs_mem]
  simp only [hbMsgs, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, h1, -, rfl⟩
    exact ⟨e, ⟨he, h1⟩, rfl⟩
  · rintro ⟨e, ⟨he, h1⟩, rfl⟩
    exact ⟨e, he, h1, host_sends reqs e he, rfl⟩

theorem ofNat_add' (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b :=
  Fp.ext (by
    rw [KeyDigest.ofNat_toNat']
    show (a + b) % P = (Fp.add (Fp.ofNat a) (Fp.ofNat b)).toNat
    rw [Fp.toNat_add, KeyDigest.ofNat_toNat', KeyDigest.ofNat_toNat', Nat.add_mod]
    rfl)

/-- The memory the tape reads: the byte of the first `HB` message at `(ts, pos)`. -/
def memOf (reqs : List Req) (ts p : Fp) : Fp :=
  (((hbMsgs reqs).find? fun m => decide (m.take 2 = [ts, p])).map fun m => m.getD 2 0).getD 0

theorem memOf_eq {reqs : List Req} (hM : MemAgree reqs) {ts p b : Fp} (h : [ts, p, b] ∈ hbMsgs reqs) :
    b = memOf reqs ts p := by
  unfold memOf
  cases hf : (hbMsgs reqs).find? (fun m => decide (m.take 2 = [ts, p])) with
  | none =>
    have := List.find?_eq_none.1 hf [ts, p, b] h
    simp at this
  | some m' =>
    have hm' := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have e := hM _ h _ hm' (by rw [hp]; rfl)
    subst e
    rfl

theorem hbE_mem {reqs : List Req} {ts ptr : Nat} {bs : Bytes}
    (hq : ∀ e ∈ hbE ts ptr bs, e ∈ hostOf reqs) {j : Nat} (hj : j < bs.length) :
    [Fp.ofNat ts, Fp.ofNat ptr + Fp.ofNat j, Fp.ofNat (bs[j]).toNat] ∈ hbMsgs reqs := by
  have he : (B_HB, true, [ts, ptr + j, (bs.getD j 0).toNat]) ∈ hostOf reqs :=
    hq _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  simp only [hbMsgs, List.mem_map, List.mem_filter, decide_eq_true_eq]
  refine ⟨_, ⟨he, rfl⟩, ?_⟩
  simp only [List.map_cons, List.map_nil, ofNat_add', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]

/-- **`HostReqs` from the T1 tape**: checks on the request list alone. -/
theorem hostReqs_of_tape {D nb np : Nat} {prev post : Bytes} {n : Nat} {reqs : List Req}
    (hM : MemAgree reqs)
    (hb : ∀ q ∈ reqs, q.ts < P ∧ q.seg < P ∧ q.key.length < P ∧ q.val.length < P)
    (ho : reqs.Pairwise (fun a b => a.seg < b.seg ∨ (a.seg = b.seg ∧ a.ts < b.ts))) :
    HostReqs (fullAir D (m5bX (hostOf reqs) prev post n) nb np) tr pub (hostOf reqs) reqs where
  send := host_sends reqs
  sreq := by
    intro m
    rw [sent_host (hostOK_of reqs) (.inl rfl), tapeMsgs_mem]
    constructor
    · rintro ⟨e, he, h1, -, rfl⟩
      rcases mem_hostOf he with ⟨q, hq, rfl⟩ | h
      · refine ⟨q, hq, ?_⟩
        simp only [sreqE, Req.msg, List.map_cons, List.map_nil]
      · exact absurd (h1.symm.trans h.1) (by decide)
    · rintro ⟨q, hq, rfl⟩
      refine ⟨sreqE q, List.mem_flatMap.2 ⟨q, hq, List.mem_cons_self ..⟩, rfl, rfl, ?_⟩
      simp only [sreqE, Req.msg, List.map_cons, List.map_nil]
  hb := by
    refine ⟨memOf reqs, fun ts p b h => ?_, fun q hq => ⟨?_, ?_⟩⟩
    · rw [sent_host (hostOK_of reqs) (.inr rfl), hb_msgs] at h
      exact memOf_eq hM h
    · intro j hj
      have hin : ∀ e ∈ hbE q.ts q.kptr q.key, e ∈ hostOf reqs := fun e he =>
        List.mem_flatMap.2 ⟨q, hq, List.mem_cons_of_mem _ (List.mem_append_left _ he)⟩
      exact (memOf_eq hM (hbE_mem hin hj)).symm
    · intro hpr j hj
      have hin : ∀ e ∈ hbE q.ts q.vptr q.val, e ∈ hostOf reqs := fun e he =>
        List.mem_flatMap.2 ⟨q, hq, List.mem_cons_of_mem _ (List.mem_append_right _ (by rw [if_pos hpr]; exact he))⟩
      exact (memOf_eq hM (hbE_mem hin hj)).symm
  bound := hb
  order := ho

end

open StateM5a.Tape StateM5a.M5bFinal StateM5a.Store NearSpecV3.D2 in
/-- **M5b end to end on a T1-form tape**: `m5b_final` with the producer premise replaced by the
checks on the public request list (`MemAgree`, bounds, `(seg, ts)` order). -/
theorem m5b_final_tape {tr : Trace Fp} {pub : List Fp} {D nb np : Nat}
    {compress : List Nat → List Nat → List Nat} {reqs : List Req} {prev post : Bytes} {n : Nat}
    (hH : Holds (fullAir D (m5bX (hostOf reqs) prev post n) nb np) pub tr)
    (hcomp : Sha512If.CompressOK compress)
    (hC : Sha512If.Sha512IfContract compress
      ((busList (fullAir D (m5bX (hostOf reqs) prev post n) nb np) tr pub B_IF384 true).map WsDecode.decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hNCR : Sha512If.NodeCR compress) (hLCR : WsKey.LeafCR compress)
    (hCR : Walk.Sha256CR)
    (hM : MemAgree reqs)
    (hb : ∀ q ∈ reqs, q.ts < P ∧ q.seg < P ∧ q.key.length < P ∧ q.val.length < P)
    (ho : reqs.Pairwise (fun a b => a.seg < b.seg ∨ (a.seg = b.seg ∧ a.ts < b.ts)))
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV (committedOf T reqs)) = some (some T') ∧ rootHash (some T') = post :=
  m5b_final (hostOK_of reqs) hH hcomp hC hD1 hD hNCR hLCR hCR (hostReqs_of_tape hM hb ho) hn hprev hpost T hT0 hF

end StateM5a.StHost
