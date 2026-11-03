import StateM5a.RowBrK

/-!
# StateM5a.RowBrL — `LocalOK` of `BR.oDL` (delete below a branch whose child is a leaf descriptor)

As `RowBrK.localOK_oDH`, with the child's `LD` result materialized by `MATQ`/`MATR`
(`BusSplit.step_brLeaf`).  The `MATR` answer is the premise `hmat` in the form `BusSplit.mat_reqresp`
gives it (responders `SN.oLM`, `matRel_oLM`).
-/

namespace StateM5a.RowBrL

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem br_mem_rkdl : Br.c "oDL" * (Br.c "rk" - K RK_LD) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 8000000 in
/-- **`BR.oDL`**: delete below a branch whose child result is a leaf descriptor (`LD`); the leaf is
materialized (`MATQ`/`MATR`, answered by an `SN.oLM` row: `hmat`, the `MatRel` of the row's own
request / answer cells) and the branch keeps.  `hmono`: `om ≤ mem` (`RowFacts.br_mono`). -/
theorem localOK_oDL {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDL") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r)
    (hmono : le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) ≤ brMem tr pub r)
    (hmat : MatRel σ keyOf (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)))) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 1 := f1
  have eFD : (Br.c "oFD").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨hrk, href, hnm, hom⟩ := keep_up (tr := tr) (pub := pub) (r := r) eGn (by evg; grind)
    (by evg; grind) eUD eUN eUV eDV eD1 (by evg; grind)
  have hrkc : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).rk = RK_LD := by
    rw [br_uin]; show ev tr 2 r pub (Br.c "rk") = RK_LD
    rw [FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_rkdl) h1]; rfl
  have hmat' : MatRel σ keyOf (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).kid2
      (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).st2 (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).alen
      (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).avh
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub))) := by
    rw [br_uin]
    have k2 : ev tr 2 r pub (Br.c "oDL" * Br.c "kid2") = ev tr 2 r pub (Br.c "kid2") :=
      ev_eq_of_eval (by evg; grind)
    have s2 : ev tr 2 r pub (Br.c "oDL" * Br.c "st2") = ev tr 2 r pub (Br.c "st2") :=
      ev_eq_of_eval (by evg; grind)
    have l2 : ev tr 2 r pub ((Br.c "oFD" + Br.c "oDL") * Br.c "lvlen") = ev tr 2 r pub (Br.c "lvlen") :=
      ev_eq_of_eval (by evg; grind)
    have h2 : (((List.range 16).map fun i => (Br.c "oFD" + Br.c "oDL") * Br.c "lvh" i).map (E tr 2 r pub)) =
        (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)) := by
      rw [map_gate (Br.c "oFD" + Br.c "oDL") (fun i => Br.c "lvh" i) (by evg; grind), List.map_map]; rfl
    dsimp only
    rw [k2, s2, l2, h2]; exact hmat
  have com : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).om =
      le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) := by
    rw [br_uin]
  have hmem := br_mem_desc hc eGn eSL eUV eDV hR
  have hkeep := FieldRows.br_keep hc (eval_one_ev (by evg; grind)) (br_bool_nf hc)
  have hcount := newKids_count hc (tr := tr) (pub := pub) (r := r)
  have hkd := br_kids_desc hc eGn eUN eDN eSL hD1 hn hs1 hs0 hfn1
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch
  refine step_brLeaf (n := n) hold ?_ ?_ hrkc hrk hmat' ?_ ?_ ?_ hom ?_ ?_ hch
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · rw [href, com, ← hkd]
    have : brMem tr pub r - le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) +
        le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) = brNMem tr pub r := by omega
    unfold brNew at hnew
    rw [br_val_kept hc eGn eUV eDV] at hnew
    rw [this]; exact hnew
  · rw [← hkd, hcount]; omega
  · intro hv
    rw [← hkd, hcount]
    have : ev tr 2 r pub (Br.c "hasv") = 0 := by
      have hb := br_bool_hasv' hc
      unfold brVal at hv
      split at hv
      · cases hv
      · omega
    have := hkeep.2 this; omega
  · rw [hnm, com]; omega
  · rw [hnm]; exact brNMem_lt hR

end

end StateM5a.RowBrL
