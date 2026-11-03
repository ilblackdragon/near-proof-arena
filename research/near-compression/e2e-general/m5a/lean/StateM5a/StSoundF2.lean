import StateM5a.StSoundW
import StateM5a.StSoundF1

/-!
# StateM5a.StSoundF2 — the working-set accesses are exactly the execution's requests

**Producer premise `HostReqs A tr pub host reqs`** (named; the execution side's contract, lane A's
memory argument on the full AIR, the public tape on T1):

* `send`: the host tape only sends;
* `sreq`: the `SREQ` messages sent are exactly the requests' `Req.msg`
  `(ts, pr, seg, |key|, kptr, |val| or 0, vptr)`;
* `hb`: there is a memory function `mem : ts → pos → byte` (field-valued) such that every `HB`
  message sent is `(ts, pos, mem ts pos)`, and each request's key / value bytes are
  `mem ts (kptr + j)` / `mem ts (vptr + j)`;
* `bound`: `ts`, `seg` and the lengths are `< p`;
* `order`: the requests are listed in strictly increasing `(seg, ts)` order (execution order).

**Honest T1 satisfies it**: `htape.json` holds one `SREQ` entry per executed request (`send`,
`sreq`) and, for each request, the `HB` entries of its key and value bytes read from the call's
linear memory at time `ts` (`hb`: `mem ts pos` = that memory's byte at `pos`; one byte per
address of a call, and NEAR's memory is ≤ 64 MiB `< p` so addresses do not wrap); `ts` is the
Wasm step counter (`< 2^24`), segments are consecutive chunks of execution, so `(seg, ts)`
increases along the execution (`order`).  On the full AIR the same holds of lane A's `HOST` rows.

Under it:
* **`acc_req`**: every access `a ∈ wsa` is some request's: `a.t = q.ts`, `a.seg = q.seg`,
  `a.kd = pairs (sha256 q.key)`, `a.new = q.newV`;
* **`req_acc`**: every request has an access with its `(seg, ts)` (the request is consumed by an
  `STW` row — the only `SREQ` receiver — whose `WRITE` is consumed by a `WSA` row, the only `WRITE`
  receiver).
-/

namespace StateM5a.StSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.FieldRows
open StateM5a.KeyDecode StateM5a.DecodeM5a StateM5a.KcChain StateM5a.Tape StateM5a.M5b StateM5a.WsDecode2
open StateM5a.WsBus NearSpec

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The request's `SREQ` message. -/
def Req.msg (q : Req) : List Fp :=
  [Fp.ofNat q.ts, Fp.ofNat (if q.pr then 1 else 0), Fp.ofNat q.seg, Fp.ofNat q.key.length,
   Fp.ofNat q.kptr, Fp.ofNat (if q.pr then q.val.length else 0), Fp.ofNat q.vptr]

/-- The working-set value the request writes (`(cp, cl, cv16, wr = 1)`). -/
def Req.newV (q : Req) : List Nat :=
  [if q.pr then 1 else 0, if q.pr then q.val.length else 0] ++
    (if q.pr then pairs (sha256 q.val) else List.replicate 16 0) ++ [1]

/-- **Producer premise**: the execution side's `SREQ`/`HB` traffic is the request list `reqs`. -/
structure HostReqs (A : Air) (tr : Trace Fp) (pub : List Fp) (host : List (Nat × Bool × List Nat))
    (reqs : List Req) : Prop where
  send : ∀ e ∈ host, e.2.1 = true
  sreq : ∀ m, m ∈ busList A tr pub B_SREQ true ↔ ∃ q ∈ reqs, m = q.msg
  hb : ∃ mem : Fp → Fp → Fp, (∀ ts p b, [ts, p, b] ∈ busList A tr pub B_HB true → b = mem ts p) ∧
    ∀ q ∈ reqs, (∀ j (h : j < q.key.length),
        mem (Fp.ofNat q.ts) (Fp.ofNat q.kptr + Fp.ofNat j) = Fp.ofNat (q.key[j]).toNat) ∧
      (q.pr = true → ∀ j (h : j < q.val.length),
        mem (Fp.ofNat q.ts) (Fp.ofNat q.vptr + Fp.ofNat j) = Fp.ofNat (q.val[j]).toNat)
  bound : ∀ q ∈ reqs, q.ts < P ∧ q.seg < P ∧ q.key.length < P ∧ q.val.length < P
  order : reqs.Pairwise (fun a b => a.seg < b.seg ∨ (a.seg = b.seg ∧ a.ts < b.ts))

/-! ## Bytes -/

theorem hbytes_eq {A : Air} {tr : Trace Fp} {pub : List Fp} {mem : Fp → Fp → Fp}
    (hmem : ∀ ts p b, [ts, p, b] ∈ busList A tr pub B_HB true → b = mem ts p) {ts ptr : Fp}
    {bs bs' : Bytes} (h : HBytes A tr pub ts ptr bs) (hl : bs.length = bs'.length)
    (h' : ∀ j (hj : j < bs'.length), mem ts (ptr + Fp.ofNat j) = Fp.ofNat (bs'[j]).toNat) : bs = bs' := by
  apply List.ext_getElem hl
  intro j h1 h2
  have e := hmem _ _ _ (h j h1)
  rw [h' j h2] at e
  have e2 := congrArg Fp.toNat e
  have l1 := UInt8.toNat_lt bs[j]
  have l2 := UInt8.toNat_lt bs'[j]
  rw [KeyDigest.ofNat_toNat', KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at e2
  exact UInt8.toNat_inj.1 e2

theorem ofNat_inj {a b : Nat} (ha : a < P) (hb : b < P) (h : Fp.ofNat a = Fp.ofNat b) : a = b := by
  have := congrArg Fp.toNat h
  rwa [KeyDigest.ofNat_toNat', KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Two requests with the same `(seg, ts)` are equal. -/
theorem req_uniq {reqs : List Req} (ho : reqs.Pairwise (fun a b => a.seg < b.seg ∨ (a.seg = b.seg ∧ a.ts < b.ts)))
    {q q' : Req} (hq : q ∈ reqs) (hq' : q' ∈ reqs) (hs : q.seg = q'.seg) (ht : q.ts = q'.ts) : q = q' := by
  refine Classical.byContradiction fun hne => ?_
  rcases pairwise_two ho hq hq' hne with h | h <;> omega

/-! ## Accesses are requests -/

section
variable {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {host : List (Nat × Bool × List Nat)}
  {prev post : NearSpec.Bytes} {n : Nat} {reqs : List Req}

theorem acc_req (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    (hR : HostReqs (fullAir D (m5bX host prev post n) nb np) tr pub host reqs)
    {a : WsaRow (List Nat) (List Nat)} (ha : a ∈ wsa tr pub) :
    ∃ q ∈ reqs, a.t = q.ts ∧ a.seg = q.seg ∧ a.kd = pairs (sha256 q.key) ∧ a.new = q.newV := by
  obtain ⟨ts, pr, seg, klen, kptr, vlen, vptr, et, es, hq, key, dv, hkl, hkb, hcase, hkd, hnew⟩ :=
    wsa_mem_write hh hH ha
  obtain ⟨q, hqr, hqm⟩ := (hR.sreq _).1 hq
  obtain ⟨mem, hmem, hqb⟩ := hR.hb
  obtain ⟨b1, b2, b3, b4⟩ := hR.bound q hqr
  simp only [Req.msg, List.cons.injEq, and_true] at hqm
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hqm
  subst e1 e2 e3 e4 e5 e6 e7
  have hkey : key = q.key := hbytes_eq hmem hkb
    (by rw [hkl, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt b3]) (hqb q hqr).1
  subst hkey
  refine ⟨q, hqr, by rw [← et, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt b1],
    by rw [← es, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt b2], hkd, ?_⟩
  rw [hnew]
  rcases hcase with ⟨hp, val, hvl, hvb, hdv⟩ | ⟨hp, hvl, hdv⟩
  · have hpr : q.pr = true := by
      cases e : q.pr
      · rw [e] at hp
        exact absurd hp (by decide +kernel)
      · rfl
    simp only [hpr, ↓reduceIte] at hvl
    have hval : val = q.val := hbytes_eq hmem hvb
      (by rw [hvl, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt b4]) ((hqb q hqr).2 hpr)
    subst hval
    simp [Req.newV, hpr, hdv, KeyDigest.ofNat_toNat']
    exact ⟨by decide, Nat.mod_eq_of_lt b4⟩
  · have hpr : q.pr = false := by
      cases e : q.pr
      · rfl
      · rw [e] at hp
        exact absurd hp (by decide +kernel)
    simp [Req.newV, hpr, hdv, hvl, KeyDigest.ofNat_toNat']

/-! ## Requests are accesses -/

/-- All buses of the `m5aAir` tables are below `NUM_BUSES_WS`. -/
def busesLt (is : List Interaction) : Bool := is.all fun i => decide (i.bus < NUM_BUSES_WS)
/-- No interaction on bus `b`. -/
def noBus (b : Nat) (is : List Interaction) : Bool := is.all fun i => decide (i.bus ≠ b)

theorem m5a_busesLt (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length),
    busesLt ((m5aAir D).tables[t]).interactions = true
  | 0, _ => by show busesLt shaTable.interactions = true; decide
  | 1, _ => by show busesLt Key.interactions = true; decide
  | 2, _ => by show busesLt Br.interactions = true; decide
  | 3, _ => by show busesLt Sn.interactions = true; decide
  | 4, _ => by show busesLt Kcmp.interactions = true; decide
  | 5, _ => by show busesLt Wsb.interactions = true; decide
  | 6, _ => by show busesLt Wsn.interactions = true; decide
  | 7, _ => by show busesLt Wsa.interactions = true; decide
  | 8, _ => by show busesLt Snc.interactions = true; decide
  | 9, _ => by show busesLt Rng.interactions = true; decide
  | 10, _ => by show busesLt Wsl.interactions = true; decide
  | 11, _ => by show busesLt Wsp.interactions = true; decide
  | n + 12, h => absurd h (by simp [m5aAir])

theorem m5a_noWrite (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 7 →
    noBus B_WRITE ((m5aAir D).tables[t]).interactions = true
  | 0, _, _ => by show noBus B_WRITE shaTable.interactions = true; decide
  | 1, _, _ => by show noBus B_WRITE Key.interactions = true; decide
  | 2, _, _ => by show noBus B_WRITE Br.interactions = true; decide
  | 3, _, _ => by show noBus B_WRITE Sn.interactions = true; decide
  | 4, _, _ => by show noBus B_WRITE Kcmp.interactions = true; decide
  | 5, _, _ => by show noBus B_WRITE Wsb.interactions = true; decide
  | 6, _, _ => by show noBus B_WRITE Wsn.interactions = true; decide
  | 7, _, h => absurd rfl h
  | 8, _, _ => by show noBus B_WRITE Snc.interactions = true; decide
  | 9, _, _ => by show noBus B_WRITE Rng.interactions = true; decide
  | 10, _, _ => by show noBus B_WRITE Wsl.interactions = true; decide
  | 11, _, _ => by show noBus B_WRITE Wsp.interactions = true; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem noBus_ne {b : Nat} {is : List Interaction} (h : noBus b is = true) {i : Interaction} (hi : i ∈ is) :
    i.bus ≠ b := of_decide_eq_true (List.all_eq_true.1 h i hi)

theorem shas_noSREQ : noBus B_SREQ shaTableS.interactions = true := by decide
theorem stb_noSREQ : noBus B_SREQ Stb.interactions = true := by decide
theorem shas_noWrite : noBus B_WRITE shaTableS.interactions = true := by decide
theorem stb_noWrite : noBus B_WRITE Stb.interactions = true := by decide
theorem stw_sreq_r : Stw.interactions.filter (fun i => decide (i.bus = B_SREQ ∧ i.send = false)) =
    [rcv B_SREQ (Stw.c "act") [Stw.c "ts", Stw.c "pr", Stw.c "seg", Stw.c "klen", Stw.c "kptr", Stw.c "vlen",
      Stw.c "vptr"]] := by decide
theorem stw_write_r : Stw.interactions.filter (fun i => decide (i.bus = B_WRITE ∧ i.send = false)) = [] := by
  decide
theorem wsa_write_r : Wsa.interactions.filter (fun i => decide (i.bus = B_WRITE ∧ i.send = false)) =
    [rcv B_WRITE (Wsa.c "act") ([Wsa.c "seg", Wsa.c "t"] ++ Wsa.vec "kd" 16 ++ [Wsa.c "ncp", Wsa.c "ncl"] ++
      Wsa.vec "ncv" 16)] := by decide
theorem stw_write_mem : snd B_WRITE (Stw.c "act") ([Stw.c "seg", Stw.c "ts"] ++ pack2 (fun b => Stw.c "dk" b) ++
    [Stw.c "pr", Stw.c "vlen"] ++ pack2 (fun b => Stw.c "dv" b)) ∈ Stw.interactions := memD_mem (by decide)

theorem filter_none {is : List Interaction} {b : Nat} {s : Bool}
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = []) {i : Interaction} (hi : i ∈ is)
    (hb : i.bus = b) (hs : i.send = s) : False := by
  have : i ∈ is.filter (fun i => decide (i.bus = b ∧ i.send = s)) := List.mem_filter.2 ⟨hi, by simp [hb, hs]⟩
  rw [h] at this
  exact List.not_mem_nil this

/-- A message on a bus of the M5b AIR is a row message of an `m5aAir` table or of an extra table. -/
theorem bus_split {D : Nat} {extra : List Table} {nb np b : Nat} {s : Bool} {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub b s) :
    (∃ t, ∃ ht : t < (m5aAir D).tables.length, ∃ r, r < tr.height t ∧
      ∃ i ∈ ((m5aAir D).tables[t]).interactions, i.bus = b ∧ i.send = s ∧ 0 < i.multNat tr t r pub ∧
        m = i.msgVal tr t r pub) ∨
    (∃ k, ∃ hk : k < extra.length, ∃ r, r < tr.height (12 + k) ∧ ∃ i ∈ (extra[k]).interactions,
      i.bus = b ∧ i.send = s ∧ 0 < i.multNat tr (12 + k) r pub ∧ m = i.msgVal tr (12 + k) r pub) := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hp, rfl⟩ := mem_busList.1 hm
  by_cases hlt : t < (m5aAir D).tables.length
  · rw [fullAir_get hlt ht] at hi
    exact .inl ⟨t, hlt, r, hr, i, hi, hb, hs, hp, rfl⟩
  · rw [m5a_len] at hlt
    have hk : t - 12 < extra.length := by rw [fullAir_len] at ht; omega
    have htk : t = 12 + (t - 12) := by omega
    rw [x_get htk ht hk] at hi
    refine .inr ⟨t - 12, hk, r, by rw [← htk]; exact hr, i, hi, hb, hs, ?_, ?_⟩
    · rw [← htk]; exact hp
    · rw [← htk]

theorem host_send {host : List (Nat × Bool × List Nat)} (hs : ∀ e ∈ host, e.2.1 = true) {i : Interaction}
    (hi : i ∈ (tapeTable host).interactions) : i.send = true := by
  simp only [tapeTable, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  exact hs e he

theorem req_acc (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    (hR : HostReqs (fullAir D (m5bX host prev post n) nb np) tr pub host reqs) {q : Req} (hq : q ∈ reqs) :
    ∃ a ∈ wsa tr pub, a.t = q.ts ∧ a.seg = q.seg := by
  obtain ⟨b1, b2, -, -⟩ := hR.bound q hq
  have hs : q.msg ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SREQ true :=
    (hR.sreq _).2 ⟨q, hq, rfl⟩
  have hrv := (holds_perm hH B_SREQ).mem_iff.1 hs
  -- the `STW` row consuming the request
  obtain ⟨r, hr, hact, he⟩ : ∃ r, r < tr.height 15 ∧ (Stw.c "act").eval tr 15 r pub = 1 ∧
      q.msg = (rcv B_SREQ (Stw.c "act") [Stw.c "ts", Stw.c "pr", Stw.c "seg", Stw.c "klen", Stw.c "kptr",
        Stw.c "vlen", Stw.c "vptr"]).msgVal tr 15 r pub := by
    rcases bus_split hrv with ⟨t, ht, r, hr, i, hi, hb, -, -, -⟩ | ⟨k, hk, r, hr, i, hi, hb, hsd, hp, he⟩
    · have := of_decide_eq_true (List.all_eq_true.1 (m5a_busesLt D t ht) i hi)
      rw [hb] at this
      exact absurd this (by decide)
    · rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact absurd (hb.symm.trans h) (by decide)
      · exact absurd hb (noBus_ne shas_noSREQ h)
      · exact absurd hb (noBus_ne stb_noSREQ h)
      · obtain rfl := filter_one_mem stw_sreq_r h hb hsd
        exact ⟨r, hr, multNat_one_bit rfl hp, he⟩
      · have := host_send hR.send (show i ∈ (tapeTable host).interactions from hi)
        rw [hsd] at this
        exact absurd this (by decide)
  simp only [Req.msg, rcv, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
  obtain ⟨ets, -, eseg, -⟩ := he
  -- its `WRITE`, consumed by a `WSA` row
  have hw := msg_mem_busList (A := fullAir D (m5bX host prev post n) nb np) (pub := pub) (t := 15)
    (by rw [bx_len]; omega) (by rw [get15]; exact stw_write_mem) hr rfl hact
  have hwr := (holds_perm hH B_WRITE).mem_iff.1 hw
  rcases bus_split hwr with ⟨t, ht, r', hr', i, hi, hb, hsd, hp, he⟩ | ⟨k, hk, r', hr', i, hi, hb, hsd, hp, he⟩
  · by_cases h7 : t = 7
    · subst h7
      change i ∈ Wsa.interactions at hi
      obtain rfl := filter_one_mem wsa_write_r hi hb hsd
      have hA := multNat_one_bit rfl hp
      simp only [snd, rcv, Interaction.msgVal, List.map_append, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.cons.injEq] at he
      refine ⟨wsaRow tr pub r', List.mem_filterMap.2 ⟨r', List.mem_range.2 hr', by simp [hA]⟩, ?_, ?_⟩
      · show ((Wsa.c "t").eval tr 7 r' pub).toNat = q.ts
        rw [← he.2.1, ← ets, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt b1]
      · show ((Wsa.c "seg").eval tr 7 r' pub).toNat = q.seg
        rw [← he.1, ← eseg, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt b2]
    · exact absurd hb (noBus_ne (m5a_noWrite D t ht h7) hi)
  · rcases x_cases hh hk hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact absurd (hb.symm.trans h) (by decide)
    · exact absurd hb (noBus_ne shas_noWrite h)
    · exact absurd hb (noBus_ne stb_noWrite h)
    · exact (filter_none stw_write_r h hb hsd).elim
    · rcases h with h | h <;> exact absurd (hb.symm.trans h) (by decide)

end

end StateM5a.StSound
