import StateM5a.RowBrV2

/-!
# StateM5a.RowBrUN — `LocalOK` of `BR.oUN` (upsert into an empty slot)

The walk's new leaf `K[d+1..] ↦ (|x|, sha256 x)` is materialized (`MATQ`/`MATR`, answered by an
`SN.oLM` row: the `MatRel` premise `hmat` on the row's request / answer cells, as
`BusSplit.mat_reqresp` gives it); the request is the walk's own (`kid2 = kid`, `st2 = d + 1`,
`lvlen = dvlen`, `lvh = dvh`: constraints).  The rewritten branch gains slot `n` (`nf_n = 1`,
`br_kids_new`) with memory `mem + nm` (`om = 0`).  `BusWalk.step_brNew`; the new leaf is
well-formed (`newLeaf_wf`) given the key's nibbles `< 16` and length `≤ 2^21` (`hkey`, from the
`KEY` table on the AIR).
-/

namespace StateM5a.RowBrUN

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK StateM5a.RowBrV StateM5a.RowBrV2

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem packNibbles_len : ∀ l : List Nat, (packNibbles l).length ≤ l.length
  | a :: b :: rest => by simp only [packNibbles, List.length_cons]; have := packNibbles_len rest; omega
  | [_] => by simp [packNibbles]
  | [] => by simp [packNibbles]

theorem hexPrefix_len (k : List Nat) (b : Bool) : (hexPrefix k b).length ≤ k.length + 1 := by
  cases k with
  | nil => simp [hexPrefix, packNibbles]
  | cons a l =>
    have h1 := packNibbles_len l
    have h2 := packNibbles_len (a :: l)
    simp only [hexPrefix]
    split <;> simp_all <;> omega

/-- **A new leaf is well-formed** (nibbles, value length, hex-prefix length, memory). -/
theorem newLeaf_wf {k : List Nat} {x : Bytes} (hk : ∀ y ∈ k, y < 16) (hl : k.length ≤ 2 ^ 21)
    (hx : x.length < P) : (newLeaf k x).wf = true := by
  have hp := hexPrefix_len k true
  simp only [newLeaf, PTrie.wf, nibblesOk, slotOk, leafMem, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨⟨⟨hk, by omega⟩, by omega⟩, by omega⟩

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
/-- **The rewritten slots of `oUN`**: slot `n` (empty) takes the materialized leaf's ref. -/
theorem br_kids_new (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eUN : (Br.c "oUN").eval tr 2 r pub = 1)
    (eDN : (Br.c "oDN").eval tr 2 r pub = 0) (eSL : (Br.c "oSL").eval tr 2 r pub = 0)
    (hD1 : ev tr 2 r pub (Br.c "oD1") = 0)
    {n : Nat} (hn : n < 16) (hs1 : ev tr 2 r pub (Br.c "sel" n) = 1)
    (hs0 : ∀ j, j < 16 → j ≠ n → ev tr 2 r pub (Br.c "sel" j) = 0) (hfn : ev tr 2 r pub (Br.c "f" n) = 0) :
    brNewKids tr pub r = (brKids tr pub r).put n
      (some (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))) := by
  have hsr := br_sr_zero hc hD1 (ev_of_eval eSL)
  have es1 := fp_of_ev1 hs1
  have ef0 := fp_of_ev0 hfn
  unfold brNewKids brKids
  apply kidsFrom_put _ _ _ _ _ 16 0 n hn
  · intro j hj hjn
    simp only [Nat.zero_add]
    have e0 := fp_of_ev0 (hs0 j hj hjn)
    have e1 := hsr j hj
    have hnf := br_nf_eq hc j hj
    refine ⟨ev_eq_of_eval (by evga; grind), fun _ => ?_⟩
    unfold brNewSlot brSlot
    congr 1
    · simp only [bE, Br.nisn]; evga; grind
    · exact pack2_eval fun b => by simp only [Br.newch]; evga; grind
  · intro y hy
    cases hy
    simp only [Nat.zero_add]
    have e1 := hsr n hn
    have hnf := br_nf_eq hc n hn
    refine ⟨eval_one_ev (by evga; grind), ?_⟩
    unfold brNewSlot
    congr 1
    · simp only [bE, Br.nisn]; evga; grind
    · exact pack2_eval fun b => by simp only [Br.newch]; evga; grind
  · intro h; cases h

macro "brmem2" : tactic => `(tactic| (unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.mem_singleton]; first | memfind | simp))

set_option maxHeartbeats 4000000 in
theorem br_mem_unk : (Br.c "oUN" + Br.c "oSL") * (Br.c "kid2" - Br.c "kid") ∈ Br.constraints := by brmem2
set_option maxHeartbeats 4000000 in
theorem br_mem_uns : (Br.c "oUN" + Br.c "oSL") * (Br.c "st2" - Br.c "d" - 1) ∈ Br.constraints := by brmem2
set_option maxHeartbeats 4000000 in
theorem br_mem_unl : (Br.c "oUN" + Br.c "oSL") * (Br.c "lvlen" - Br.c "dvlen") ∈ Br.constraints := by brmem2
set_option maxHeartbeats 4000000 in
theorem br_mem_unh (i : Nat) (hi : i < 16) :
    (Br.c "oUN" + Br.c "oSL") * (Br.c "lvh" i - Br.c "dvh" i) ∈ Br.constraints := by brmem2
set_option maxHeartbeats 4000000 in
theorem br_mem_unom (k : Nat) (hk : k < 4) : (Br.c "oUN" + Br.c "oSL") * Br.c "om" k ∈ Br.constraints := by brmem2

set_option maxHeartbeats 8000000 in
/-- **`BR.oUN`**: upsert into an empty slot. -/
theorem localOK_oUN {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oUN") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r)
    (hmat : MatRel σ keyOf (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub))))
    (hkey : (∀ y ∈ keyOf (ev tr 2 r pub (Br.c "kid")), y < 16) ∧
      (keyOf (ev tr 2 r pub (Br.c "kid"))).length ≤ 2 ^ 21) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 1 := f1
  have eD : (Br.c "mD").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 1 := f1
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn0 : ev tr 2 r pub (Br.c "f" n) = 0 := hfn.trans (ev_of_eval eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 1 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨href, hnm, hom⟩ := new_up (tr := tr) (pub := pub) (r := r) eGn (by evg; grind) (by evg; grind)
  have g1 : ev tr 2 r pub (Br.c "oUN" + Br.c "oSL") = 1 := eval_one_ev (by evg; grind)
  have hk2 : ev tr 2 r pub (Br.c "kid2") = ev tr 2 r pub (Br.c "kid") :=
    FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_unk) g1
  have hst : ev tr 2 r pub (Br.c "st2") = ev tr 2 r pub (Br.c "d") + 1 := by
    have e := fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_uns) g1)
    have e' : (Br.c "st2").eval tr 2 r pub = (Br.c "d" + 1).eval tr 2 r pub := by
      simp only [eval_mul, eval_sub, eval_add, eval_lit] at e ⊢; grind
    rw [ev_eq_of_eval e', ev_d1 hd]
  have hlv : ev tr 2 r pub (Br.c "lvlen") = ev tr 2 r pub (Br.c "dvlen") :=
    FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_unl) g1
  have hlh : ((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub) =
      ((List.range 16).map fun i => Br.c "dvh" i).map (E tr 2 r pub) := by
    simp only [List.map_map]
    apply List.map_congr_left; intro i hi
    exact Fp.ext (FieldVer.eq_of_gate (FieldRows.hold rfl hc (br_mem_unh i (List.mem_range.1 hi))) g1)
  have hom0 : le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) = 0 := by
    have z : ∀ k, k < 4 → (Br.c "om" k).eval tr 2 r pub = 0 := fun k hk =>
      fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_unom k hk)) g1)
    simp only [le4, List.range, List.range.loop, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, E, z 0 (by decide), z 1 (by decide), z 2 (by decide), z 3 (by decide)]
    rfl
  have hmem := br_mem_desc hc eGn eSL eUV eDV hR
  have hkn := br_kids_new hc eGn eUN eDN eSL hD1 hn hs1 hs0 hfn0
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din]
  simp only [Sem, hmode]
  rw [payOf_kid]
  intro x hx1 hx2
  rw [payOf_vlen] at hx1
  rw [payOf_vh] at hx2
  refine step_brNew (n := n) (kid := ev tr 2 r pub (Br.c "kid"))
    (lref := refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
    (lmem := le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub))) hold ?_ hn rfl
    (by rw [← hnn]; exact drop_cons_of_get hnib) ?_ ?_ hom ?_ ?_ ?_
  · rw [kids_at n hn, if_neg (by omega)]
  · have hm := hmat
    rw [hk2, hst, hlv, hlh, hx2] at hm
    have e : ev tr 2 r pub (Br.c "dvlen") = x.length := hx1
    rw [e] at hm; exact hm
  · rw [href]
    unfold brNew at hnew
    rw [br_val_kept hc eGn eUV eDV, hkn] at hnew
    have : brMem tr pub r + le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) = brNMem tr pub r := by
      omega
    rw [this]; exact hnew
  · rw [hnm]; omega
  · rw [hnm]; exact brNMem_lt hR
  · apply newLeaf_wf
    · intro y hy; exact hkey.1 y (List.mem_of_mem_drop hy)
    · rw [List.length_drop]; exact Nat.le_trans (Nat.sub_le _ _) hkey.2
    · rw [← hx1]; exact ev_lt _

end

end StateM5a.RowBrUN
