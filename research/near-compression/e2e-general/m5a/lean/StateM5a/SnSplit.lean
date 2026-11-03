import StateM5a.SnSplitHop


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
open StateM5a.RowSnF StateM5a.RowBrN

local notation "P" => 2013265921

set_option maxRecDepth 100000


section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

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
    obtain ⟨ed, hrel⟩ := oslRel r hr h1 ew
    have hj0 : ev tr 3 s pub (Sn.c "jm") = 0 := by have := toNat_eq edd; omega
    rw [hj0, Nat.add_zero] at hrel ⊢
    have href : brOut tr pub r = refOf (E tr 3 s pub (Sn.c "shf"))
        (((List.range 16).map fun i => Sn.c "sh" i).map (E tr 3 s pub)) := by
      show refOf (E tr 2 r pub (Br.c "nref")) ((pack2 fun b => Br.c "hn" b).map (E tr 2 r pub)) = _; rw [ef, eh]
    have hmem : brNMem tr pub r = le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub)) := by
      show le4 (Br.NM.map (E tr 2 r pub)) = _; rw [em]
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
      show refOf (E tr 3 p pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 p pub)) = _; rw [ef, eh]
    have hnm : snNMem tr pub p = le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub)) := by
      show le4 (Sn.NM.map (E tr 3 p pub)) = _; rw [em]
    rw [hout, hnm] at hrc
    rcases spr_src hH hxP hmp with ⟨r, hr, h1r, her⟩ | ⟨p', hp', h1', her⟩
    · have her' : brSprS.map (E tr 2 r pub) = snSprP.map (E tr 3 p pub) := her.symm
      obtain ⟨ew2, ed2, ef2, eh2, em2⟩ := spr_dec her' (by simp [pack2])
      obtain ⟨-, hrel⟩ := oslRel r hr h1r (ew2.trans ew)
      have hout' : brOut tr pub r = snNChild tr pub p := by
        show refOf (E tr 2 r pub (Br.c "nref")) ((pack2 fun b => Br.c "hn" b).map (E tr 2 r pub)) = refOf (E tr 3 p pub (Sn.c "nxf")) ((pack2 fun b => Sn.c "nx" b).map (E tr 3 p pub))
        rw [ef2, eh2]
      have hmem' : brNMem tr pub r = le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 p pub)) := by
        show le4 (Br.NM.map (E tr 2 r pub)) = _; rw [em2]
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
