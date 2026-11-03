import StateM5a.SnSplitBus

/-!
# StateM5a.SnSplit — the split answer (`BusSplit.SplitAns`) of an `SN` split row from `Holds`

* **`FreshRel`**: what a fresh-extension row (`SN.oEP`: the extension over a split's common prefix;
  `SN.oEM`: a split's re-keyed extension) establishes: its new record is the extension
  `K_kid[d .. d + klen)` over the child it received (`nxf`, `nx`, memory `unm`), published under
  its output ref.  `fresh_short`: proved for a short key (`cont = 0`) from `Holds`, the row's
  `NewOK` and limb ranges; continued keys (`cont = 1`) are a premise of the assembly.
* **`split_ans`**: a split row at `(w, d)` (mismatch at `jm`) received `SPR(w, d, ref, mem)`; its
  sender is the walk's `oSL` row (then `jm = 0`) or an `oEP` row that received the split row's
  `EPQ` and the `oSL` row's `SPR` at `(w, d + jm)` (`jm ≠ 0`).  Every hop is identified through the
  walk's unique split row (`WalkEnd.sn_term_unique`).  With `BrOslSplit.osl_split` and `FreshRel`,
  `(ref, mem)` is the spec's split subtree: `SplitAns σ keyOf d (d + jm) (snQ s) ref mem`.
-/

namespace StateM5a.SnSplit

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Fresh extensions (`oEP`, `oEM`) -/

/-- **What a fresh-extension row establishes**: the extension `K_kid[d .. d + klen)` over the child
`(nxf, nx)` with memory `unm`, published under `snOut` with memory `snNMem`. -/
def FreshRel (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) (p : Nat) : Prop :=
  ExtOver σ (epKey keyOf (ev tr 3 p pub (Sn.c "d")) (ev tr 3 p pub (Sn.c "d" + Sn.c "klen")) (ev tr 3 p pub (Sn.c "kid")))
    (snNChild tr pub p) (le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 p pub)))
    (snOut tr pub p) (snNMem tr pub p)

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- The op bundle of a fresh-extension row. -/
theorem fresh_flags {p : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 p pub = 0)
    (h : ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) :
    ev tr 3 p pub (Sn.c "gA") = 0 ∧ ev tr 3 p pub (Sn.c "isL") = 0 ∧ ev tr 3 p pub (Sn.c "isE") = 1 ∧
    ev tr 3 p pub (Sn.c "act") = 1 ∧ ev tr 3 p pub (Sn.c "oEU") = 0 ∧ ev tr 3 p pub (Sn.c "gfr") = 1 := by
  have hb : ∀ s ∈ snNames, ev tr 3 p pub (Sn.c s) ≤ 1 := fun s hs => sn_flag_le hc s hs
  have S := fun (s : String) (l : List String) (h : s :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s l h hl
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e2 := S "oLF" ["oEF", "oLA", "oEA"] (by simp [snNames]) (by simp)
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e4 := S "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e5 := S "oLF" ["oLR", "oLD", "oLS", "oLM", "oLA", "oLZ", "oLX"] (by simp [snNames]) (by simp)
  have e6 := S "oEF" ["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e8 := S "oLA" ["oEA", "oLZ", "oEZ", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e9 := S "oEB" ["oEP", "oEM"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc]
    at e1 e2 e3 e4 e5 e6 e8 e9
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c2 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mF)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  have c4 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mD)
  have c5 := eq_of_sub (hold rfl hc sn_mem_isL)
  have c6 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_isE)
  have c8 := eq_of_sub (hold rfl hc sn_mem_gA)
  have c9 := eq_of_sub (hold rfl hc sn_mem_gfr)
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3; rw [e4] at c4; rw [e5] at c5; rw [e6] at c6
  rw [e8] at c8; rw [e9] at c9
  have := hb "act" (by simp [snNames]); have := hb "mF" (by simp [snNames]); have := hb "mU" (by simp [snNames])
  have := hb "mD" (by simp [snNames]); have := hb "isE" (by simp [snNames])
  have := hb "oLF" (by simp [snNames]); have := hb "oLR" (by simp [snNames]); have := hb "oLD" (by simp [snNames])
  have := hb "oLS" (by simp [snNames]); have := hb "oLM" (by simp [snNames]); have := hb "oEF" (by simp [snNames])
  have := hb "oEU" (by simp [snNames]); have := hb "oED" (by simp [snNames]); have := hb "oLA" (by simp [snNames])
  have := hb "oEA" (by simp [snNames]); have := hb "oLZ" (by simp [snNames]); have := hb "oEZ" (by simp [snNames])
  have := hb "oES" (by simp [snNames]); have := hb "oEB" (by simp [snNames]); have := hb "oLX" (by simp [snNames])
  have := hb "oEX" (by simp [snNames]); have := hb "oEP" (by simp [snNames]); have := hb "oEM" (by simp [snNames])
  clear hb S e1 e2 e3 e4 e5 e6 e8 e9
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 8000000 in
/-- **`FreshRel` of a short-key fresh-extension row** (`cont = 0`). -/
theorem fresh_short {σ : Store} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) {p : Nat} (hp : p < tr.height 3)
    (h : ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1)
    (hcont : ev tr 3 p pub (Sn.c "cont") = 0) (hnew : NewOK σ (snOut tr pub p) (snNew tr pub p))
    (hN : ∀ k, k < 4 → ev tr 3 p pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536) : FreshRel σ (keyOf tr) tr pub p := by
  have hc := tbl_sn D extra nb np hH p (List.mem_range.2 hp)
  obtain ⟨hA0, hL0, hE1, hA, hEU, hF⟩ := fresh_flags hc h
  -- depth: the first key nibble is looked up
  have hb0 : ev tr 3 p pub (Sn.b 0) = 1 := by
    rw [sn_b_eq_a hc hA0 0 (by decide)]
    have := FieldRows2.sn_hold hc SnDepthAll.sn_mem_ea0
    rw [RowSnN.ev_gm hE1, ev_sub, ev_one] at this
    have := ev_lt (tr := tr) (t := 3) (r := p) (pub := pub) (Sn.a 0)
    omega
  have hd0 := (sn_nib hH hxN 0 (by decide) hp (fp_of_ev1 hb0)).2
  rw [SnDepthAll.ev_d0 (e := K 0) (ev_const 0)] at hd0
  have hd : ev tr 3 p pub (Sn.c "d") + 64 < P := by omega
  have hK := sn_key_prefix (keyOf := keyOf tr) hc hcont hA0 hd (fun j hj hgj => (sn_nib hH hxN j hj hp hgj).1)
  have hkl0 := (FieldRows2.sn_flags hc hcont).1
  have hkl : ev tr 3 p pub (Sn.c "d" + Sn.c "klen") = ev tr 3 p pub (Sn.c "d") + (snKey tr pub p).length := by
    rw [snKey_length, ev_hadd, Nat.mod_eq_of_lt (by omega)]
  rw [← snKey_length] at hK
  have eG : ev tr 3 p pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by rw [ev_hadd, hF, hEU]
  have hmem := RowSnE.sn_mem_eb hc hA hcont eG hF hN hu
  unfold FreshRel
  rw [hkl, epKey_eq hK]
  refine extOver_of_new (by rw [snNew_ext (by omega)] at hnew; exact hnew) hmem ⟨?_, snNMem_lt hN, ?_⟩
  · have hb := (RowFacts.keyOf_bounds hH (ev tr 3 p pub (Sn.c "kid"))).1
    unfold nibblesOk
    rw [List.all_eq_true]
    intro y hy
    have : y ∈ (keyOf tr (ev tr 3 p pub (Sn.c "kid"))).drop (ev tr 3 p pub (Sn.c "d")) := by
      rw [hK]; exact List.mem_append_left _ hy
    exact decide_eq_true (hb y (List.mem_of_mem_drop this))
  · rw [hp_length, snKey_length]; omega

end

/-! ## The split answer -/

theorem spr_dec {a b c a' b' c' : Expr} {A B A' B' : List Expr} {f g : Expr → Fp}
    (h : ([a, b, c] ++ A ++ B).map f = ([a', b', c'] ++ A' ++ B').map g) (hA : A.length = A'.length) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ A.map f = A'.map g ∧ B.map f = B'.map g := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := List.append_inj h4 (by simp [hA])
  exact ⟨h1, h2, h3, h5, h6⟩

theorem sn_mem_j0 : Sn.gX * (1 - Sn.c "j0") * (Sn.c "jm" * Sn.c "ij0" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem jm_ne {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (h1 : ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1) : ev tr 3 s pub (Sn.c "jm") ≠ 0 := by
  intro h0
  have := FieldRows2.sn_hold hc sn_mem_j0
  rw [RowSnN.ev_gm h1, ev_sub, ev_hmul, h0, ev_one] at this
  simp at this

theorem gX_of {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (h1 : ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1) : ev tr 3 s pub Sn.gX = 1 := by
  have bX := fun s' hs => sn_flag_le (t := 3) hc s' hs
  have b1 := bX "oLX" (by simp [snNames]); have b2 := bX "oEX" (by simp [snNames])
  rw [ev_hmul] at h1
  unfold Sn.gX at h1 ⊢
  rw [ev_hadd] at h1 ⊢
  rw [Nat.mod_eq_of_lt (by omega)] at h1 ⊢
  rcases (by omega : ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") = 0 ∨
    ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") = 1) with h | h
  · rw [h] at h1; simp at h1
  · exact h

section
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
  (hxMQ : ∀ T ∈ extra, sendsOn T.interactions B_MATQ = false)
  (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false)
  (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false)
  (hxE : ∀ T ∈ extra, sendsOn T.interactions B_EPQ = false)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE

/-- The split row behind an `oSL` row of walk `w` is the walk's split row `s`. -/
theorem osl_of_split {s r : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oSL") = 1)
    (hw : E tr 2 r pub (Br.c "w") = E tr 3 s pub (Sn.c "w")) :
    snSpQ.map (E tr 3 s pub) = brSpQ.map (E tr 2 r pub) := by
  obtain ⟨s', hs', hX', hq⟩ := osl_spq hH hxQ hr h1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hc' := tbl_sn D extra nb np hH s' (List.mem_range.2 hs')
  obtain ⟨hg, h0, -⟩ := split_flags hc hX
  obtain ⟨hg', h0', -⟩ := split_flags hc' hX'
  have w' : E tr 3 s' pub (Sn.c "w") = E tr 2 r pub (Br.c "w") := at_eq2 hq (k := 0) rfl rfl
  obtain rfl := sn_term_unique hH hD hx hxN hxK hxR hs hs' (ev_one_eval hg) (ev_one_eval hg') h0 h0'
    (toNat_eq (hw.symm.trans w'.symm))
  exact hq

/-- The split row behind an `oEP` row of walk `w` is the walk's split row `s`. -/
theorem ep_of_split {s p : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (hp : p < tr.height 3) (h1 : ev tr 3 p pub (Sn.c "oEP") = 1)
    (hw : E tr 3 p pub (Sn.c "w") = E tr 3 s pub (Sn.c "w")) :
    ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1 ∧ snEpqS.map (E tr 3 s pub) = snEpqR.map (E tr 3 p pub) := by
  obtain ⟨s', hs', hX', hq⟩ := epq_src hH hxE hp h1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hc' := tbl_sn D extra nb np hH s' (List.mem_range.2 hs')
  have hX'' := gX_of hc' hX'
  obtain ⟨hg, h0, -⟩ := split_flags hc hX
  obtain ⟨hg', h0', -⟩ := split_flags hc' hX''
  have w' : E tr 3 s' pub (Sn.c "w") = E tr 3 p pub (Sn.c "w") := at_eq2 hq (k := 0) rfl rfl
  obtain rfl := sn_term_unique hH hD hx hxN hxK hxR hs hs' (ev_one_eval hg) (ev_one_eval hg') h0 h0'
    (toNat_eq (hw.symm.trans w'.symm))
  exact ⟨hX', hq⟩

set_option maxHeartbeats 16000000 in
/-- **The split answer of an `SN` split row**, from `Holds`, the responders' relations (`SnMatOK`,
`FreshRel` on `oEP` rows) and the `oSL` rows' `NewOK` and limbs. -/
theorem split_ans {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub)
    (hBnew : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hBlim : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → ∀ k, k < 4 →
      ev tr 2 r pub (Br.NM.getD k 0) < 65536 ∧ ev tr 2 r pub (Br.c "nm" k) < 65536 ∧
      ev tr 2 r pub (Br.c "nm2" k) < 65536)
    (hF : ∀ p, p < tr.height 3 → ev tr 3 p pub (Sn.c "oEP") = 1 → FreshRel σ (keyOf tr) tr pub p)
    {s : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1) :
    SplitAns σ (keyOf tr) (ev tr 3 s pub (Sn.c "d")) (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm"))
      (snQ tr pub s) (refOf (E tr 3 s pub (Sn.c "shf")) (((List.range 16).map fun i => Sn.c "sh" i).map (E tr 3 s pub)))
      (le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub))) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hg, h0, hA, -⟩ := split_flags hc hX
  have hdep : ev tr 3 s pub (Sn.c "d") + 64 < P := SnDepthAll.sn_depth_all hH hxN hxL s hs (ev_one_eval hg)
  have hjm := (RowSnM.sn_jm hc hA).1
  have hdj : ev tr 3 s pub (Sn.c "d" + Sn.c "jm") = ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") := by
    rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
  -- the `oSL` relation, transported to `s`
  have oslRel : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 →
      E tr 2 r pub (Br.c "w") = E tr 3 s pub (Sn.c "w") →
      ev tr 2 r pub (Br.c "d") = ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") ∧
      SplitRel σ (keyOf tr) (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm")) (snQ tr pub s)
        (brOut tr pub r) (brNMem tr pub r) := by
    intro r hr h1 hw
    have hq := osl_of_split hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hs hX hr h1 hw
    have ed : ev tr 2 r pub (Br.c "d") = ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") := by
      rw [← hdj]; exact toNat_eq (at_eq2 hq (k := 1) rfl rfl).symm
    have hl := hBlim r hr h1
    have := osl_split hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hS hr h1 (hBnew r hr h1)
      (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2.1) (fun k hk => (hl k hk).2.2)
    rw [oslQ_eq hc hX hq, ed] at this
    exact ⟨ed, this⟩
  -- the `SPR` the split row received
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_spr_rX) hs rfl (ev_one_eval hX)
  rcases spr_src hH hxP hm with ⟨r, hr, h1, he⟩ | ⟨p, hp, h1, he⟩
  · -- directly from `oSL`: `jm = 0`
    have he' : brSprS.map (E tr 2 r pub) = snSprR.map (E tr 3 s pub) := he.symm
    obtain ⟨ew, edd, ef, eh, em⟩ := spr_dec he' (by simp [pack2])
    obtain ⟨ed, hrel⟩ := oslRel r hr h1 hr ew
    have hj0 : ev tr 3 s pub (Sn.c "jm") = 0 := by have := toNat_eq edd; omega
    rw [hj0, Nat.add_zero] at hrel ⊢
    have href : brOut tr pub r = refOf (E tr 3 s pub (Sn.c "shf"))
        (((List.range 16).map fun i => Sn.c "sh" i).map (E tr 3 s pub)) := by
      unfold brOut; rw [← eh, ← ef]
    have hmem : brNMem tr pub r = le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub)) := by
      unfold brNMem; rw [← em]
    rw [href, hmem] at hrel
    exact splitAns_direct hrel
  · -- from `oEP` over `oSL`: `jm ≠ 0`
    have he' : snSprS.map (E tr 3 p pub) = snSprR.map (E tr 3 s pub) := he.symm
    obtain ⟨ew, edd, ef, eh, em⟩ := spr_dec he' (by simp [pack2])
    obtain ⟨hj1, hq⟩ := ep_of_split hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hs hX hp h1 ew
    have hjne := jm_ne hc hj1
    have eq1 : ev tr 3 p pub (Sn.c "d") = ev tr 3 s pub (Sn.c "d") := toNat_eq (at_eq2 hq (k := 1) rfl rfl).symm
    have eq2 : ev tr 3 p pub (Sn.c "d" + Sn.c "klen") = ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") := by
      rw [← hdj]; exact toNat_eq (at_eq2 hq (k := 2) rfl rfl).symm
    have eq3 : ev tr 3 p pub (Sn.c "kid") = ev tr 3 s pub (Sn.c "kid") := toNat_eq (at_eq2 hq (k := 3) rfl rfl).symm
    -- the `SPR` the `oEP` row received
    have hmp := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_spr_rP) hp rfl (ev_one_eval h1)
    have hrc := hF p hp h1
    unfold FreshRel at hrc
    rw [eq1, eq2, eq3] at hrc
    have hout : snOut tr pub p = refOf (E tr 3 s pub (Sn.c "shf"))
        (((List.range 16).map fun i => Sn.c "sh" i).map (E tr 3 s pub)) := by
      unfold snOut; rw [← eh, ← ef]
    have hnm : snNMem tr pub p = le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub)) := by
      unfold snNMem; rw [← em]
    rw [hout, hnm] at hrc
    rcases spr_src hH hxP hmp with ⟨r, hr, h1r, her⟩ | ⟨p', hp', h1', her⟩
    · have her' : brSprS.map (E tr 2 r pub) = snSprP.map (E tr 3 p pub) := her.symm
      obtain ⟨ew2, ed2, ef2, eh2, em2⟩ := spr_dec her' (by simp [pack2])
      obtain ⟨-, hrel⟩ := oslRel r hr h1r (ew2.trans ew)
      have hout' : brOut tr pub r = snNChild tr pub p := by unfold brOut snNChild; rw [eh2, ef2]
      have hmem' : brNMem tr pub r = le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 p pub)) := by
        unfold brNMem; rw [em2]
      rw [hout', hmem'] at hrel
      refine splitAns_ext (sprR := [((0, ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm")),
        (snNChild tr pub p, le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 p pub))))]) (w := 0)
        (by omega) ⟨_, _, List.mem_singleton_self _, hrc⟩ ?_
      intro cref cmem hin
      simp only [List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨-, rfl, rfl⟩ := hin
      exact hrel
    · exfalso
      have her' : snSprS.map (E tr 3 p' pub) = snSprP.map (E tr 3 p pub) := her.symm
      obtain ⟨ew2, ed2, -⟩ := spr_dec her' (by simp [pack2])
      obtain ⟨-, hq'⟩ := ep_of_split hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hs hX hp' h1' (ew2.trans ew)
      have a := toNat_eq (at_eq2 hq' (k := 1) rfl rfl)
      have b := toNat_eq ed2
      rw [eq2] at b
      omega

end

end

end StateM5a.SnSplit
