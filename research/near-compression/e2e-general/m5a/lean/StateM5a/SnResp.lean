import StateM5a.SnAssembly

/-!
# StateM5a.SnResp — the `SN` responders: `SnSibOK` (`oLS`) and `SnMatOK` (`oLM`)

An `oLS` row reads its node (a leaf) under the requested ref and answers its key (the walk
key's nibbles from `d`, `NIB` + `KLEN`) and value ref: `BusSplit.sibRel_oLS`.  An `oLM` row
publishes the leaf `K_kid[d..] ↦ (dvlen, dvh)` with memory `leafMem` (`RowSnN.sn_leaf_nmem`):
`BusSplit.matRel_oLM`.  Premises, per responder row: its old record (`oLS`) / published new record
(`oLM`) — the `VER` / SHA-256 facts as for walk rows (`SnOldAny`, `SnNewAny`) —, on `oLM` the
value-length bytes and the new leaf's memory `< P` (as `oLR`, see `RowSnAll2.SnLeafMemLt`), and
the continued-key responders (`cont = 1`) as a premise.
-/

namespace StateM5a.SnResp

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.KeyDecode StateM5a.KeyLookups StateM5a.RowSnAll StateM5a.RowSnN
open StateM5a.RowSnAll2 StateM5a.SnDepthAll

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- The op bundle of a responder row (`oLS` / `oLM`). -/
theorem resp_flags (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (h : ev tr 3 r pub (Sn.c "oLS") = 1 ∨ ev tr 3 r pub (Sn.c "oLM") = 1) :
    ev tr 3 r pub (Sn.c "gA") = 0 ∧ ev tr 3 r pub (Sn.c "isL") = 1 ∧ ev tr 3 r pub (Sn.c "oLR") = 0 ∧
    ev tr 3 r pub (Sn.c "oEU") = 0 ∧ ev tr 3 r pub (Sn.c "oEB") = 0 ∧ ev tr 3 r pub (Sn.c "act") = 1 ∧
    ev tr 3 r pub (Sn.c "oEP") = 0 ∧ ev tr 3 r pub (Sn.c "oEM") = 0 ∧
    ev tr 3 r pub (Sn.c "oLS") + ev tr 3 r pub (Sn.c "oLM") = 1 := by
  have hb : ∀ s ∈ snNames, ev tr 3 r pub (Sn.c s) ≤ 1 := fun s hs => sn_flag_le hc s hs
  have S := fun (s : String) (l : List String) (h : s :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s l h hl
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e2 := S "oLF" ["oEF", "oLA", "oEA"] (by simp [snNames]) (by simp)
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e4 := S "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e5 := S "oLF" ["oLR", "oLD", "oLS", "oLM", "oLA", "oLZ", "oLX"] (by simp [snNames]) (by simp)
  have e8 := S "oLA" ["oEA", "oLZ", "oEZ", "oLX", "oEX"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc] at e1 e2 e3 e4 e5 e8
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c2 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mF)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  have c4 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mD)
  have c5 := eq_of_sub (hold rfl hc sn_mem_isL)
  have c8 := eq_of_sub (hold rfl hc sn_mem_gA)
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3; rw [e4] at c4; rw [e5] at c5; rw [e8] at c8
  have b0 := hb "act" (by simp [snNames])
  have b1 := hb "oLS" (by simp [snNames]); have b2 := hb "oLM" (by simp [snNames])
  clear hb S e1 e2 e3 e4 e5 e8
  omega

/-- The depth of a responder (a leaf, every key nibble looked up) is a key position or the key's
end: `d ≤ 2^21`. -/
theorem resp_depth {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) (hr : r < tr.height 3)
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA0 : ev tr 3 r pub (Sn.c "gA") = 0) (hisL : ev tr 3 r pub (Sn.c "isL") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) : ev tr 3 r pub (Sn.c "d") + 64 < P := by
  suffices h : ev tr 3 r pub (Sn.c "d") ≤ 2 ^ 21 by omega
  have hb0 := sn_b_bool hc 0 (by decide)
  rcases (by omega : ev tr 3 r pub (Sn.c "b" 0) = 1 ∨ ev tr 3 r pub (Sn.c "b" 0) = 0) with h1 | h0
  · have := (sn_nib hH hN 0 (by decide) hr (fp_of_ev1 (by rw [sn_b_lt 0 (by decide)]; exact h1))).2
    rw [ev_d0 (e := K 0) (ev_const 0)] at this
    omega
  · have ha0 : ev tr 3 r pub (Sn.c "a" 0) = 0 := by
      rw [← FieldRows2.sn_a_lt 0 (by decide), ← sn_b_eq_a hc hA0 0 (by decide), sn_b_lt 0 (by decide)]
      exact h0
    have hkl := FieldRows2.sn_flags hc hcont
    have hk0 : ev tr 3 r pub (Sn.c "klen") = 0 := by
      have := hkl.2 0 (by decide); rw [ha0] at this; split at this <;> omega
    have hk := sn_klen_leaf hH hL hr (fp_of_ev1 (by rw [ev_hmul, hisL, FieldRows2.ev_one_sub0 hA0]))
    have hk' : (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d") := by
      rw [← ev_d0 hk0]; exact hk
    have := (RowFacts.keyOf_bounds hH (ev tr 3 r pub (Sn.c "kid"))).2
    omega

/-- A responder's key is the walk key's rest from `d` (every nibble looked up, the key ends). -/
theorem resp_key {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) (hr : r < tr.height 3)
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA0 : ev tr 3 r pub (Sn.c "gA") = 0) (hisL : ev tr 3 r pub (Sn.c "isL") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) = snKey tr pub r := by
  have hd := resp_depth hH hN hL hr hc hA0 hisL hcont
  have hK := sn_key_prefix (keyOf := keyOf tr) hc hcont hA0 hd (fun j hj hgj => (sn_nib hH hN j hj hr hgj).1)
  have hlen := sn_klen_leaf hH hL hr (fp_of_ev1 (by rw [ev_hmul, hisL, FieldRows2.ev_one_sub0 hA0]))
  change (keyOf tr _).length = _ at hlen
  rw [ev_hadd, Nat.mod_eq_of_lt (by have := (FieldRows2.sn_flags hc hcont).1; omega)] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  exact hK

end

/-- **Premise**: every active `SN` row reading its node has its old record (`VER` / SHA-256). -/
def SnOldAny (σ : Store) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "oLS") = 1 → ev tr 3 r pub (Sn.c "cont") = 0 → OldOK σ (snIn tr pub r) (snOld tr pub r)

/-- **Premise**: every `SN` row building a node publishes it (`VER` / SHA-256). -/
def SnNewAny (σ : Store) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "oLM") = 1 → ev tr 3 r pub (Sn.c "cont") = 0 → NewOK σ (snOut tr pub r) (snNew tr pub r)

/-- **Premise**: the `oLM` value-length bytes and the new leaf's memory `< P` (not implied by the
AIR, as `SnLeafMemLt`). -/
def SnMatLeaf (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "oLM") = 1 → ev tr 3 r pub (Sn.c "cont") = 0 → 
    (∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) ∧ snNMem tr pub r < P

set_option maxHeartbeats 4000000 in
/-- **`SnSibOK` from `Holds`** (head-key responders; continued keys a premise). -/
theorem snSibOK_of {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp} {σ : Store}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hold : SnOldAny σ tr pub)
    (hlong : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLS") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      SibRel σ (keyOf tr) (ev tr 3 s pub (Sn.c "d"))
        (refOf (E tr 3 s pub (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (E tr 3 s pub)))
        (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
        (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub)))) :
    BrSib.SnSibOK σ (keyOf tr) tr pub := by
  intro s hs h1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hcb := FieldRows2.sn_bool hc "cont" (by simp)
  by_cases hcont : ev tr 3 s pub (Sn.c "cont") = 0
  · obtain ⟨hA0, hisL, -⟩ := resp_flags hc (Or.inl h1)
    have ho := hold s hs h1 hcont
    rw [snOld_leaf hisL] at ho
    exact sibRel_oLS ho (resp_key hH hN hL hs hc hA0 hisL hcont)
  · exact hlong s hs h1 (by omega)

set_option maxHeartbeats 4000000 in
/-- **`SnMatOK` from `Holds`** (head-key responders; continued keys a premise). -/
theorem snMatOK_of {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp} {σ : Store}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hnew : SnNewAny σ tr pub) (hSM : BrRange.SnMatLimbs tr pub) (hleaf : SnMatLeaf tr pub)
    (hlong : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLM") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      MatRel σ (keyOf tr) (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.c "d")) (ev tr 3 s pub (Sn.c "dvlen"))
        (bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)))
        (refOf (E tr 3 s pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 s pub)))
        (le4 (Sn.NM.map (E tr 3 s pub)))) :
    BrMat.SnMatOK σ (keyOf tr) tr pub := by
  intro s hs h1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hcb := FieldRows2.sn_bool hc "cont" (by simp)
  by_cases hcont : ev tr 3 s pub (Sn.c "cont") = 0
  · obtain ⟨hA0, hisL, hLR, -, -, hA, -⟩ := resp_flags hc (Or.inr h1)
    have g : ev tr 3 s pub (Sn.c "oLR" + Sn.c "oLM") = 1 := by rw [ev_hadd, hLR, h1]
    obtain ⟨hnx, hlt⟩ := hleaf s hs h1 hcont
    have hmem := sn_leaf_nmem hc hA hcont g (hSM s hs h1) hlt hnx
    have hvl : ev tr 3 s pub (Sn.c "dvlen") = ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "nx" t) :=
      FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_vl) g
    have hvh : ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub) =
        (pack2 fun b => Sn.c "nx" (4 + b)).map (E tr 3 s pub) := by
      simp only [pack2, List.map_map]
      apply List.map_congr_left; intro i hi
      have hi' := List.mem_range.1 hi
      have := FieldVer.eq_of_gate (FieldRows2.sn_hold hc (sn_mem_dvh i hi')) g
      simp only [Function.comp, E]
      rw [show 4 + (2 * i + 1) = 5 + 2 * i by omega]
      exact Fp.ext this
    have hn := hnew s hs h1 hcont
    rw [snNew_leaf hisL] at hn
    unfold snNVal at hn
    rw [hmem, ← hvl] at hn
    refine matRel_oLM (resp_key hH hN hL hs hc hA0 hisL hcont) ?_ ?_
    · rw [hvh]; exact hn
    · show snNMem tr pub s = _
      rw [hmem, hvl]
  · exact hlong s hs h1 (by omega)

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.VerAssembly
  StateM5a.SnAssembly in
/-- **Batched FINAL in the spec's order** (`SnAssembly.air_final_sorted_sn`) with the `SN` responder
relations `SnSibOK` / `SnMatOK` discharged for head-key responders. -/
theorem air_final_sorted_sn2 {tr : Trace Fp} {pub : List Fp} (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hrS : ∀ T ∈ rest, sendsOn T.interactions B_MATQ = false ∧ sendsOn T.interactions B_MATR = false ∧
      sendsOn T.interactions B_SIBQ = false ∧ sendsOn T.interactions B_SIBA = false)
    (hxV : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_VER = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (snVers : List (Nat × Rec))
    (hnd : ((brVers tr pub ++ snVers).map (·.1)).Nodup)
    (hSU : BrRange.SnUpLimbs tr pub) (hSM : BrRange.SnMatLimbs tr pub)
    (hVl : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ev tr 2 r pub (Br.c "gsha") = 0 →
      ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) < 65536)
    (hVP : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → brVlen tr pub r < 2013265921)
    (hOsl : BrMat.OslApart tr pub)
    (hold : SnOldAll (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hnew : SnNewAll (storeOf (brVers tr pub ++ snVers)) tr pub)
    (holdS : SnOldAny (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hnewM : SnNewAny (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hlim : SnLimbs3 tr pub) (hlm : SnLeafMemLt tr pub) (hleaf : SnMatLeaf tr pub)
    (hrest : SnRest2 (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub)
    (hlongS : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLS") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      SibRel (storeOf (brVers tr pub ++ snVers)) (keyOf tr) (ev tr 3 s pub (Sn.c "d"))
        (refOf (E tr 3 s pub (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (E tr 3 s pub)))
        (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
        (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))))
    (hlongM : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLM") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      MatRel (storeOf (brVers tr pub ++ snVers)) (keyOf tr) (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.c "d"))
        (ev tr 3 s pub (Sn.c "dvlen"))
        (bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)))
        (refOf (E tr 3 s pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 s pub)))
        (le4 (Sn.NM.map (E tr 3 s pub))))
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (committed : List (Bytes × Option Bytes)) (hcomm : committed.Perm cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV committed) = some (some T') ∧ rootHash (some T') = post :=
  air_final_sorted_sn D writes prev post n rest nb np hP hr hrN hrS hxV hn hprev hpost snVers hnd hSU hSM hVl hVP
    (snSibOK_of hP.hH (fun T hT => (hP.hsil T hT).1) (fun T hT => (hP.hsil T hT).2.1) holdS hlongS)
    (snMatOK_of hP.hH (fun T hT => (hP.hsil T hT).1) (fun T hT => (hP.hsil T hT).2.1) hnewM hSM hleaf hlongM)
    hOsl hold hnew hlim hlm hrest cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnResp
