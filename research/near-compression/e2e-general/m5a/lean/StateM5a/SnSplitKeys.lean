import StateM5a.SnSplit

/-!
# StateM5a.SnSplitKeys — the keys and the decoded row of a short-key `SN` split row
(split out of the former `SnSplitLoc`, M5a-7: one module per Lean process within the 20 GB budget)

A split row at `(w, d)` with `cont = 0`: its key `snKey = p ++ x₀ :: xs` (`p` the `jm` nibbles
looked up against the walk key, `x₀ = k_jm`), the walk key `K[d..] = p ++ y :: ys` (`y ≠ x₀`,
`split_keys`), the old key `K_kid2[d..]` starts with `snKey` (`g2` lookups).  Its result is the
`SPR` answer (`SnSplit.split_ans`), so `BusSplit.localOK_leafSplit` (`oLX`, `localOK_oLX`) and
`BusSplit2.localOK_extSplit` (`oEX`, `localOK_oEX`: the old side the extension's child or the
re-keyed extension answered on `SXR` by `oEM`, `FreshRel`) apply.
-/

namespace StateM5a.SnSplitLoc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem drop_split {K p : List Nat} {d L y : Nat} (hp : p.length = L) (h : ∀ j < L, K[d + j]? = p[j]?)
    (hy : K[d + L]? = some y) : K.drop d = p ++ y :: K.drop (d + L + 1) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  rcases Nat.lt_trichotomy i L with hi | rfl | hi
  · rw [List.getElem?_append_left (by omega)]; exact h i hi
  · rw [List.getElem?_append_right (by omega), hp, Nat.sub_self]; simpa using hy
  · rw [List.getElem?_append_right (by omega), hp]
    obtain ⟨k, rfl⟩ : ∃ k, i = L + 1 + k := ⟨i - L - 1, by omega⟩
    rw [show L + 1 + k - L = k + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop]
    congr 1; omega

theorem list_split {l : List Nat} {j x : Nat} (h : l[j]? = some x) : l = l.take j ++ x :: l.drop (j + 1) := by
  have hj : j < l.length := by
    rcases Nat.lt_or_ge j l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have := drop_split (K := l) (d := 0) (p := l.take j) (L := j) (y := x) (by simp; omega)
    (fun i hi => by rw [Nat.zero_add, List.getElem?_take]; simp [hi]) (by simpa using h)
  simpa using this

theorem map_zip3_thd {tr : Trace Fp} {r : Nat} {pub : List Fp} (g h k : Expr) (hg : g.eval tr 3 r pub = 0)
    (hh : h.eval tr 3 r pub = 0) (hk : k.eval tr 3 r pub = 1) :
    ∀ (A B C : List Expr), A.length = B.length → B.length = C.length →
      (((A.zip B).zip C).map (fun ((p, q), s) => g * p + h * q + k * s)).map (E tr 3 r pub) = C.map (E tr 3 r pub)
  | [], [], [], _, _ => rfl
  | a :: A, b :: B, c :: C, h1, h2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zip3_thd g h k hg hh hk A B C (by simpa using h1) (by simpa using h2)⟩
    simp only [E, eval_add, eval_mul, hg, hh, hk]; grind
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | _, [], _ :: _, _, h2 => by simp at h2
  | _, _ :: _, [], _, h2 => by simp at h2

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- **The keys of a short-key split row.** -/
theorem split_keys (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {s : Nat} (hs : s < tr.height 3)
    (hX : ev tr 3 s pub Sn.gX = 1) (hcont : ev tr 3 s pub (Sn.c "cont") = 0) :
    ev tr 3 s pub (Sn.c "jm") < ev tr 3 s pub (Sn.c "klen") ∧
    (snKey tr pub s)[ev tr 3 s pub (Sn.c "jm")]? = some (ev tr 3 s pub (Sn.c "kj")) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d")) =
      (snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "y") ::
        (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop (ev tr 3 s pub (Sn.c "d")) =
      snKey tr pub s ++ (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop
        (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen")) ∧
    ev tr 3 s pub (Sn.c "y") ≠ ev tr 3 s pub (Sn.c "kj") ∧
    ev tr 3 s pub (Sn.c "d") + 64 < P := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hg, -, hA, -⟩ := split_flags hc hX
  obtain ⟨-, hajm⟩ := split_mN hc hX
  have hdep : ev tr 3 s pub (Sn.c "d") + 64 < P := SnDepthAll.sn_depth_all hH hxN hxL s hs (ev_one_eval hg)
  obtain ⟨hj64, hb, hkj, haj⟩ := RowSnM.sn_jm hc hA
  obtain ⟨hkl, hf⟩ := FieldRows2.sn_flags hc hcont
  obtain ⟨hy, -, hne⟩ := split_nibs hH hxN hxL hs hX
  have hlt : ev tr 3 s pub (Sn.c "jm") < ev tr 3 s pub (Sn.c "klen") := by
    have := hf _ hj64; rw [← haj, hajm] at this; split at this <;> omega
  have hget : ∀ j, j < ev tr 3 s pub (Sn.c "klen") → (snKey tr pub s)[j]? = some (ev tr 3 s pub (Sn.c "k" j)) := by
    intro j hj
    unfold snKey FieldRows2.keyOf
    rw [List.getElem?_map, List.getElem?_range hj]; rfl
  have hg2 : ev tr 3 s pub (Sn.c "g2") = 1 := by
    obtain ⟨-, -, -, hX'⟩ := split_flags hc hX
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := sn_flags' hc hg
    rw [h]; snfacts hc hg; omega
  refine ⟨hlt, by rw [hget _ hlt, hkj], ?_, ?_, hne, hdep⟩
  · refine drop_split (by rw [List.length_take, snKey_length]; omega) (fun j hj => ?_) hy
    rw [List.getElem?_take, if_pos hj, hget j (by omega)]
    have hbj : ev tr 3 s pub (Sn.b j) = 1 := by
      rw [sn_b_lt j (by omega), hb j (by omega), if_pos hj]
    have := (sn_nib hH hxN j (by omega) hs (fp_of_ev1 hbj)).1
    rw [ev_dK j (by omega), FieldRows2.sn_k_lt j (by omega)] at this
    exact this
  · exact RowSnE.sn_key2_prefix hc hcont hg2 hdep (fun j hj hgj => (sn_nib2 hH hxN j hj hs hgj).1)

/-- The decoded walk row of a split row: no child, upsert, result the `SPR` answer. -/
theorem split_row {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (hX : ev tr 3 s pub Sn.gX = 1) :
    (snRow tr pub s).dout = none ∧ (snRow tr pub s).din.pay.mode = 1 ∧
    (snRow tr pub s).din.ref = snIn tr pub s ∧ (snRow tr pub s).din.d = ev tr 3 s pub (Sn.c "d") ∧
    (snRow tr pub s).din.pay.kid = ev tr 3 s pub (Sn.c "kid") ∧
    (snRow tr pub s).din.pay.vlen = ev tr 3 s pub (Sn.c "dvlen") ∧
    (snRow tr pub s).din.pay.vh = bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)) ∧
    (snRow tr pub s).uout.ref = refOf (E tr 3 s pub (Sn.c "shf")) (((List.range 16).map fun i => Sn.c "sh" i).map (E tr 3 s pub)) ∧
    (snRow tr pub s).uout.nm = le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub)) ∧
    (snRow tr pub s).uout.om = snMem tr pub s := by
  obtain ⟨hg, h0, -, hX'⟩ := split_flags hc hX
  snfacts hc hg
  have a1 : (Sn.c "oLR").eval tr 3 s pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 s pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 s pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 s pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 s pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 s pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 s pub = 1 := s1
  have eD : (Sn.c "mD").eval tr 3 s pub = 0 := s0
  have eNu : gnu.eval tr 3 s pub = 0 := by simp only [gnu, eval_add, a1, a2, a5]; grind
  have eS : Sn.gS.eval tr 3 s pub = 0 := by simp only [Sn.gS, eval_add, a8, a9, a10]; grind
  have eX : Sn.gX.eval tr 3 s pub = 1 := ev_one_eval hX
  have hdin := (rfl : (snRow tr pub s).din = cDc.down (vals tr 3 s pub snW.di)).trans sn_din
  have huout := (rfl : (snRow tr pub s).uout = cDc.dr ((vals tr 3 s pub snW.uo).drop 2)).trans sn_uout
  refine ⟨WalkEnd.snRow_dout h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdin, snpay_mode]; show (Sn.mode.eval tr 3 s pub).toNat = 1
    rw [show Sn.mode.eval tr 3 s pub = 1 by evsn; grind]; rfl
  · rw [hdin]
  · rw [hdin]
  · rw [hdin, snpay_kid]; rfl
  · rw [hdin, snpay_vlen]; rfl
  · rw [hdin, snpay_vh]
  · rw [huout]; dsimp only
    rw [map_zip3_thd gnu Sn.gS Sn.gX eNu eS eX _ _ _ (by simp [pack2]) (by simp [pack2])]
    congr 1
    simp only [E, eval_add, eval_mul, eNu, eS, eX]; grind
  · rw [huout]; dsimp only
    rw [map_zip_right gnu Sn.gX (fun p => p) _ eNu eX _ (by simp [Sn.NM, memLimbs])]
  · rw [huout]; dsimp only
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]; rfl

end

end StateM5a.SnSplitLoc
