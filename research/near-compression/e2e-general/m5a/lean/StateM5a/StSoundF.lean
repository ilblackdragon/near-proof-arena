import StateM5a.StSoundF2
import StateM5a.StSoundF3

/-!
# StateM5a.StSoundF — `committed ~ cs` on the M5b AIR (M5a-7 item 3, second half)

**`final_changes_m5b`**: for the M5b AIR the prover runs, from `FinalOrder.Prem` (which carries
`Walk.Sha256CR`), `HostOK host` and the named producer premise `HostReqs … reqs` (`StSoundF2`):
there is a list `cs` of the writing rows' changes with

* `FinalChanges tr pub cs` — the remaining premise of `Tape.air_final` /
  `FinalOrder.air_final_sorted` (`cs[k]` has the `KEY` bytes of writing row `k` and the value its
  `(cp, cl, cv)` commits to), and
* `(committedOf T reqs).Perm cs` — the spec's committed overlay after the requests
  (`Ovl.set` / `Ovl.remove` / `Ovl.commit`, `StSoundF1`) is a permutation of `cs`;

so `air_final_sorted`'s `committed` may be taken to be the spec's overlay of the execution's
requests.

The argument: a writing row is a real FINAL row `2^D + i` whose value is (`final_latest`,
`StSoundF3`, from `ws_entries` / `ws_decoded_final3`) the written value of the
`(segment, time)`-greatest access to its key digest `kd_i` (its `wr = 1`, the INTAKE value has
`wr = 0`).  Each access is a request's (`acc_req`) and each request has an access (`req_acc`), with
equal `(seg, ts)`, the access's key digest `pairs (sha256 key)` (so its key is `kd_i`'s key by
`Sha256CR` and distinct INTAKE keys) and written value `Req.newV`.  With requests in increasing
`(seg, ts)` order (`HostReqs.order`), that access is the last request on the key (`MaxReq`), whose
change is the overlay's entry for the key (`mem_ovl`); conversely every request's key has an access
and hence a writing row.  Both lists have distinct keys (`ovl_nodup`, `fc_sorted`), so equal
membership gives the permutation.
-/

namespace StateM5a.StSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.FieldRows
open StateM5a.KeyDecode StateM5a.DecodeM5a StateM5a.Tape StateM5a.M5b StateM5a.WsDecode2 StateM5a.WsBus
open StateM5a.WsLeafF StateM5a.IntakeKeys StateM5a.FinalOrder StateM5a.DecodeWalk NearSpec NearSpecV3.D2

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- `q` is the latest request (in `(seg, ts)` order) on key `K`. -/
def MaxReq (reqs : List Req) (K : Bytes) (q : Req) : Prop :=
  q ∈ reqs ∧ q.key = K ∧ ∀ q' ∈ reqs, q'.key = K → LexLe q'.seg q'.ts q.seg q.ts

abbrev ReqOrder (reqs : List Req) : Prop :=
  reqs.Pairwise (fun a b => a.seg < b.seg ∨ (a.seg = b.seg ∧ a.ts < b.ts))

theorem maxReq_uniq {reqs : List Req} (ho : ReqOrder reqs) {K : Bytes} {q q' : Req}
    (h1 : MaxReq reqs K q) (h2 : MaxReq reqs K q') : q = q' := by
  have a := h1.2.2 q' h2.1 h2.2.1
  have b := h2.2.2 q h1.1 h1.2.1
  unfold LexLe at a b
  exact req_uniq ho h1.1 h2.1 (by omega) (by omega)

/-- The latest change on key `K` (`K ↦ none` if there is no request on `K`; not used then). -/
noncomputable def chg (reqs : List Req) (K : Bytes) : Bytes × Option Bytes := by
  classical
  exact if h : ∃ q, MaxReq reqs K q then (Classical.choose h).change else (K, none)

theorem chg_eq {reqs : List Req} (ho : ReqOrder reqs) {K : Bytes} {q : Req} (h : MaxReq reqs K q) :
    chg reqs K = q.change := by
  unfold chg
  rw [dif_pos ⟨q, h⟩, maxReq_uniq ho (Classical.choose_spec (⟨q, h⟩ : ∃ q, MaxReq reqs K q)) h]

theorem chg_fst (reqs : List Req) (K : Bytes) : (chg reqs K).1 = K := by
  unfold chg
  split
  · rename_i h; exact (Classical.choose_spec h).2.1
  · rfl

/-! ## Rows -/

section
variable {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {host : List (Nat × Bool × List Nat)}
  {prev post : NearSpec.Bytes} {n : Nat} {compress : List Nat → List Nat → List Nat} {reqs : List Req}

theorem mem_wsl {l : WslRow (List Nat) (List Nat) Sha512If.Dig} (hl : l ∈ wsl tr pub) :
    ∃ r, r < tr.height 10 ∧ (Wsl.c "act").eval tr 10 r pub = 1 ∧ l = wslRow tr pub r := by
  simp only [wsl, actRows, List.mem_filterMap, List.mem_range] at hl
  obtain ⟨r, hr, h⟩ := hl
  split at h
  · rename_i hA; exact ⟨r, hr, hA, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem curV_last (r : Nat) : (wsbE.curV tr pub 5 r).getLast? = some (ev tr 5 r pub (Wsb.c "wr")) :=
  List.getLast?_concat

variable (hP : Prem tr pub D (m5bX host prev post n) nb np compress)
include hP

theorem wsl_kd {l : WslRow (List Nat) (List Nat) Sha512If.Dig} (hl : l ∈ wsl tr pub) :
    l.kd = wsbE.kdV tr pub 5 l.i := by
  obtain ⟨r, hr, hA, rfl⟩ := mem_wsl hl
  exact ((WsEntries.ws_entries hP.hH hP.hx hP.hcomp hP.hC hP.hD1 hP.hD hP.hNCR hP.hLCR hP.dist
    hP.kdr).1 r hr hA).1.1

theorem kd_inj {i j : Nat} (hi : i < WsLen.wsLen pub) (hj : j < WsLen.wsLen pub)
    (h : wsbE.kdV tr pub 5 i = wsbE.kdV tr pub 5 j) : i = j := by
  have s := hP.hsil
  exact wsb_kd_inj hP.hH (by have := hP.hD; omega) hP.hCR (fun T hT => (s T hT).1) (fun T hT => (s T hT).2.1)
    (fun T hT => (s T hT).2.2.1) hP.hxB (fun T hT => (s T hT).2.2.2.1)
    (fun T hT => (s T hT).2.2.2.2.1) (fun T hT => (s T hT).2.2.2.2.2) hi hj h

theorem kd_key {i : Nat} (hi : i < WsLen.wsLen pub) :
    wsbE.kdV tr pub 5 i = pairs (sha256 (wkey tr pub i)) := by
  have s := hP.hsil
  obtain ⟨hi5, -, -, ri⟩ := phase0 hP.hH (by have := hP.hD; omega) hi
  exact KeyDigest.wsb_kd hP.hH hP.hxB (fun T hT => (s T hT).2.2.2.1)
    (fun T hT => (s T hT).2.2.2.2.1) (fun T hT => (s T hT).2.2.2.2.2) hi5 ri

/-- **The FINAL value of a real entry is its latest written value** (`final_latest` instantiated). -/
theorem final_val {i : Nat} (hi : i < WsLen.wsLen pub) :
    Latest (wsa tr pub) (wsbE.kdV tr pub 5 i) (wsbE.curV tr pub 5 i) (fun _ => True)
      (wsbE.curV tr pub 5 (2 ^ D + i)) := by
  have E := WsEntries.ws_entries hP.hH hP.hx hP.hcomp hP.hC hP.hD1 hP.hD hP.hNCR hP.hLCR hP.dist hP.kdr
  obtain ⟨nw, -, -, -, -, -, hacc, hlt⟩ :=
    WsKey.ws_decoded_final3 hP.hH hP.hx hP.hcomp hP.hC hP.hD1 hP.hD hP.hNCR hP.hLCR hP.dist
  refine final_latest (wsl tr pub) (wsa tr pub) i _ _ ?_ ?_ ?_ ?_ ?_ (E.2.1 i hi).2.2.2.1 ?_
  · intro l hl hli; rw [wsl_kd hP hl, hli]
  · intro a ha hk
    obtain ⟨l, hl, hkey⟩ := hacc a ha
    simp only [WslRow.key, WsaRow.key, Prod.mk.injEq] at hkey
    refine ⟨l, hl, kd_inj hP (hlt l hl) hi ?_, hkey.1⟩
    rw [← wsl_kd hP hl, hkey.2, hk]
  · intro l hl hli hmin
    obtain ⟨r, hr, hA, rfl⟩ := mem_wsl hl
    have := (E.1 r hr hA).2.1 (fun l' hl' hi' => hmin l' hl' (hi'.trans hli))
    rw [this, hli]
  · intro l hl hli l' hl' hli' hs hmax
    obtain ⟨r, hr, hA, rfl⟩ := mem_wsl hl
    obtain ⟨r', hr', hA', rfl⟩ := mem_wsl hl'
    exact (E.1 r hr hA).2.2 r' hr' hA' (hli'.trans hli.symm) hs
      (fun l'' h1 h2 h3 => hmax l'' h1 (h2.trans hli) h3)
  · intro l hl
    obtain ⟨s, h1, h2, h3, -⟩ := E.2.2 l hl
    exact ⟨s, h1, h2, h3⟩
  · intro l hl hli hm
    obtain ⟨r, hr, hA, rfl⟩ := mem_wsl hl
    exact (E.2.1 i hi).2.2.2.2 r hr hA hli hm

theorem intake_last {i : Nat} (hi : i < WsLen.wsLen pub) : (wsbE.curV tr pub 5 i).getLast? = some 0 := by
  rw [((WsEntries.ws_entries hP.hH hP.hx hP.hcomp hP.hC hP.hD1 hP.hD hP.hNCR hP.hLCR hP.dist
    hP.kdr).2.1 i hi).1]
  exact List.getLast?_concat

/-- The FINAL row `2^D + i` of a real entry is a phase-1 row. -/
theorem final_ph {i : Nat} (hi : i < WsLen.wsLen pub) :
    2 ^ D + i < tr.height 5 ∧ ev tr 5 (2 ^ D + i) pub (Wsb.c "ph") = 1 := by
  have hD30 : D ≤ 30 := by have := hP.hD; omega
  have hc := wsb_hc hP.hH
  have hlog := wsb_log hP.hH
  have hWl := WsLen.wsb_wsLen_le hc hlog hD30
  have hht := wsb_height hP.hH hD30
  have hr1 : 2 ^ D + i < tr.height 5 := by rw [hht, Nat.pow_succ]; omega
  rcases FieldWsb.wsb_index hc hlog hD30 _ hr1 with ⟨a, _⟩ | ⟨b, _⟩
  · have := ph0_lt hP.hH hD30 (tr.height 5 - (2 ^ D + i) - 1) _ (by omega) hr1 a; omega
  · exact ⟨hr1, b⟩

theorem wr_one {r : Nat} (hr : r ∈ wrRows tr pub) : ev tr 5 r pub (Wsb.c "wr") = 1 := by
  have hc := wsb_hc hP.hH
  obtain ⟨hr5, hg⟩ := List.mem_filter.1 hr
  have hr5 := List.mem_range.1 hr5
  have hgv := eval_one_ev (of_decide_eq_true hg : gw.eval tr 5 r pub = 1)
  have e : ev tr 5 r pub gw = ev tr 5 r pub (Wsb.c "ph") * ev tr 5 r pub (Wsb.c "wr") % 2013265921 :=
    ev_hmul _ _
  have hp := FieldRows2.ev_bool (hold rfl (hc r hr5) (m_bool_ph D))
  rcases FieldRows2.ev_bool (hold rfl (hc r hr5) (m_bool_wr D)) with hw | hw
  · rw [e, hw] at hgv; simp at hgv
  · exact hw

theorem mem_wrRows {i : Nat} (hi : i < WsLen.wsLen pub) (hw : ev tr 5 (2 ^ D + i) pub (Wsb.c "wr") = 1) :
    2 ^ D + i ∈ wrRows tr pub := by
  obtain ⟨hr, hp⟩ := final_ph hP hi
  refine List.mem_filter.2 ⟨List.mem_range.2 hr, decide_eq_true (ev_one_eval ?_)⟩
  show ev tr 5 (2 ^ D + i) pub (Wsb.c "ph" * Wsb.c "wr") = 1
  rw [ev_hmul, hp, hw]

/-! ## Writing rows and requests -/

variable (hh : HostOK host) (hR : HostReqs (fullAir D (m5bX host prev post n) nb np) tr pub host reqs)
include hh hR

/-- An access's request writes a key whose digest is the access's. -/
theorem acc_key {a : WsaRow (List Nat) (List Nat)} (ha : a ∈ wsa tr pub) {q : Req} (hq : q ∈ reqs)
    (ht : a.t = q.ts) (hs : a.seg = q.seg) : a.kd = pairs (sha256 q.key) ∧ a.new = q.newV := by
  obtain ⟨q', hq', ht', hs', hkd, hnew⟩ := acc_req hh hP.hH hR ha
  obtain rfl := req_uniq hR.order hq hq' (hs.symm.trans hs') (ht.symm.trans ht')
  exact ⟨hkd, hnew⟩

/-- **A real entry with an access: its FINAL row writes the latest request on its key.** -/
theorem final_req {i : Nat} (hi : i < WsLen.wsLen pub)
    (hw : ev tr 5 (2 ^ D + i) pub (Wsb.c "wr") = 1) :
    ∃ q, MaxReq reqs (wkey tr pub (2 ^ D + i)) q ∧ wsbE.curV tr pub 5 (2 ^ D + i) = q.newV := by
  rcases final_val hP hi with ⟨h1, -⟩ | ⟨a, ha, hk, -, hv, hmax⟩
  · have e := curV_last (tr := tr) (pub := pub) (2 ^ D + i)
    rw [h1, intake_last hP hi, hw] at e
    exact absurd e (by simp)
  obtain ⟨q, hq, ht, hs, hkd, hnew⟩ := acc_req hh hP.hH hR ha
  have hK : wkey tr pub (2 ^ D + i) = wkey tr pub i := final_key hP hi
  have hkey : q.key = wkey tr pub i := pairs_sha_inj hP.hCR (by rw [← hkd, hk, kd_key hP hi])
  refine ⟨q, ⟨hq, by rw [hkey, hK], fun q' hq' hk' => ?_⟩, by rw [hv, hnew]⟩
  obtain ⟨a', ha', ht', hs'⟩ := req_acc hh hP.hH hR hq'
  obtain ⟨hkd', -⟩ := acc_key hP hh hR ha' hq' ht' hs'
  have := hmax a' ha' (by rw [hkd', hk', hK, kd_key hP hi]) trivial
  rw [ht', hs', ht, hs] at this
  exact this

/-- **Every request's key has a writing FINAL row.** -/
theorem req_row {q : Req} (hq : q ∈ reqs) :
    ∃ i, i < WsLen.wsLen pub ∧ 2 ^ D + i ∈ wrRows tr pub ∧ wkey tr pub (2 ^ D + i) = q.key := by
  obtain ⟨nw, -, -, -, -, -, hacc, hlt⟩ :=
    WsKey.ws_decoded_final3 hP.hH hP.hx hP.hcomp hP.hC hP.hD1 hP.hD hP.hNCR hP.hLCR hP.dist
  obtain ⟨a, ha, ht, hs⟩ := req_acc hh hP.hH hR hq
  obtain ⟨hkd, hnew⟩ := acc_key hP hh hR ha hq ht hs
  obtain ⟨l, hl, hkey⟩ := hacc a ha
  simp only [WslRow.key, WsaRow.key, Prod.mk.injEq] at hkey
  have hj := hlt l hl
  have hkj : pairs (sha256 (wkey tr pub l.i)) = pairs (sha256 q.key) := by
    rw [← kd_key hP hj, ← wsl_kd hP hl, hkey.2, hkd]
  have hK : wkey tr pub l.i = q.key := pairs_sha_inj hP.hCR hkj
  have hw : ev tr 5 (2 ^ D + l.i) pub (Wsb.c "wr") = 1 := by
    rcases final_val hP hj with ⟨-, h2⟩ | ⟨a', ha', -, -, hv, -⟩
    · exact absurd trivial (h2 a ha (by rw [hkd, ← hkj, ← kd_key hP hj]))
    · obtain ⟨q', -, -, -, -, hnew'⟩ := acc_req hh hP.hH hR ha'
      have := curV_last (tr := tr) (pub := pub) (2 ^ D + l.i)
      rw [hv, hnew'] at this
      simp only [Req.newV, List.getLast?_concat, Option.some.injEq] at this
      exact this.symm
  exact ⟨l.i, hj, mem_wrRows hP hj hw, by rw [final_key hP hj, hK]⟩

end

/-! ## The theorem -/

theorem vals_cv {tr : Trace Fp} {pub : List Fp} (r : Nat) :
    (vals tr 5 r pub (Wsb.vec "cv" 16)).map Fp.toNat = vecN tr pub 5 r (fun t => Wsb.c "cv" t) 16 := by
  simp only [vals, Wsb.vec, vecN, List.map_map]
  rfl

theorem newV_split {tr : Trace Fp} {pub : List Fp} {r : Nat} {q : Req}
    (h : wsbE.curV tr pub 5 r = q.newV) :
    ev tr 5 r pub (Wsb.c "cp") = (if q.pr then 1 else 0) ∧
    ev tr 5 r pub (Wsb.c "cl") = (if q.pr then q.val.length else 0) ∧
    vecN tr pub 5 r (fun t => Wsb.c "cv" t) 16 =
      (if q.pr then pairs (sha256 q.val) else List.replicate 16 0) := by
  unfold LE.curV Req.newV at h
  have hl : (if q.pr then pairs (sha256 q.val) else List.replicate 16 0).length = 16 := by
    split
    · exact pairs_sha_len _
    · simp
  obtain ⟨h1, -⟩ := List.append_inj h (by rw [List.length_append, List.length_append, hl]; simp [vecN])
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨h2.1, h2.2, h3⟩

/-- **`committed ~ cs` for the M5b AIR.** -/
theorem final_changes_m5b {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {host : List (Nat × Bool × List Nat)}
    {prev post : NearSpec.Bytes} {n : Nat} {compress : List Nat → List Nat → List Nat} {reqs : List Req}
    (hP : Prem tr pub D (m5bX host prev post n) nb np compress) (hh : HostOK host)
    (hR : HostReqs (fullAir D (m5bX host prev post n) nb np) tr pub host reqs) (T : PTrie) :
    ∃ cs : List (Bytes × Option Bytes), cs.length = (wrRows tr pub).length ∧ FinalChanges tr pub cs ∧
      (committedOf T reqs).Perm cs := by
  have ho : ReqOrder reqs := hR.order
  -- a writing row's change
  have hrow : ∀ r ∈ wrRows tr pub, ∃ q, MaxReq reqs (wkey tr pub r) q ∧ wsbE.curV tr pub 5 r = q.newV := by
    intro r hr
    obtain ⟨i, rfl, hi⟩ := wr_row hP hr
    exact final_req hP hh hR hi (wr_one hP hr)
  let cs := (wrRows tr pub).map fun r => chg reqs (wkey tr pub r)
  have hcs : FinalChanges tr pub cs := by
    intro k hk hk'
    have hg : (wrRows tr pub).getD k 0 = (wrRows tr pub)[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
    obtain ⟨q, hq, hv⟩ := hrow _ (List.getElem_mem hk')
    have e : cs[k] = q.change := by
      simp only [cs, List.getElem_map]
      exact chg_eq ho hq
    obtain ⟨h1, h2, h3⟩ := newV_split hv
    rw [e]
    refine ⟨?_, ?_⟩
    · show q.key = keyBytes tr (wf tr pub k "kid")
      rw [hq.2.1]
      unfold wf wkey
      rw [hg]
    · unfold wf wcv
      rw [hg, vals_cv, h3]
      unfold Req.change
      cases hpr : q.pr
      · simp only [hpr] at h1 ⊢
        exact h1
      · simp only [hpr, if_true] at h1 h2 ⊢
        exact ⟨h1, h2, limbBytes_pairs _ (by rw [ArenaCore.sha256_length])⟩
  refine ⟨cs, by simp [cs], hcs, ?_⟩
  rw [committedOf_eq]
  -- both lists have distinct entries
  have hn1 : (ovl reqs).Nodup := List.Pairwise.of_map Prod.fst (fun a b h e => h (congrArg Prod.fst e))
    (ovl_nodup reqs)
  have hn2 : cs.Nodup := by
    have := fc_sorted hP (cs := cs) (by simp [cs]) hcs
    refine this.imp fun {a b} h e => ?_
    subst e
    unfold KR at h
    rw [bytesLt_irrefl] at h
    exact absurd h (by decide)
  rw [List.perm_ext_iff_of_nodup hn1 hn2]
  intro p
  rw [mem_ovl]
  constructor
  · rintro ⟨l1, l2, e, hl2⟩
    obtain ⟨r1, r2', rfl, -, e2⟩ := List.map_eq_append_iff.1 e
    obtain ⟨q, r2, rfl, hqp, e3⟩ := List.map_eq_cons_iff.1 e2
    have hq : q ∈ r1 ++ q :: r2 := List.mem_append_right _ (List.mem_cons_self ..)
    have hmax : MaxReq (r1 ++ q :: r2) q.key q := by
      refine ⟨hq, rfl, fun q' hq' hk => ?_⟩
      rcases List.mem_append.1 hq' with h | h
      · have := (List.pairwise_append.1 ho).2.2 q' h q (List.mem_cons_self ..)
        unfold LexLe; omega
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inr ⟨rfl, Nat.le_refl _⟩
        · have hne := hl2 q'.change (by rw [← e3]; exact List.mem_map_of_mem h)
          exact absurd (show q'.key = p.1 by rw [← hqp]; exact hk) hne
    obtain ⟨i, hi, hw, hK⟩ := req_row hP hh hR hq
    refine List.mem_map.2 ⟨_, hw, ?_⟩
    rw [hK, chg_eq ho hmax, hqp]
  · intro hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    obtain ⟨q, hq, -⟩ := hrow r hr
    rw [chg_eq ho hq]
    obtain ⟨r1, r2, e⟩ := List.append_of_mem hq.1
    refine ⟨r1.map Req.change, r2.map Req.change, by rw [e]; simp, fun x hx => ?_⟩
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hx
    intro hk
    rw [e] at ho
    have hlt := List.pairwise_cons.1 (List.pairwise_append.1 ho).2.1 |>.1 q' hq'
    have hle := hq.2.2 q' (by rw [e]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hq'))
      (by rw [← hq.2.1]; exact hk)
    unfold LexLe at hle
    omega

end StateM5a.StSound
