import StateM5a.SnSplitHop
import StateM5a.SnRange
import StateM5a.SnFinal4

/-!
# StateM5a.SnLimbsAll — `SnUpLimbs` / `SnMatLimbs` from `Holds` (M5a-7)

The 16-bit memory limbs every `SN` row sends on `UP` (positions `20..27`) and on `MATR`
(`oLM`), from `Holds`, except the memory limbs of the rows with a **continued key** (`cont = 1`),
which stay the named premise `SnContMem` (item 2 of M5a-7: a continued key's node is hashed over
the `SNC` chain, so `SnRange`'s byte argument does not apply to it as stated):

* `UP` positions `20..23` are `gnu·NM + gX·sm`: a row with a new node (`gnu`: `oLR`/`oEU`/`oEB`,
  so `gnew = 1`) sends its new memory limbs (`SnRange.sn_NM_lt` at `cont = 0`); a split row (`gX`)
  sends the `sm` it received on `SPR`, whose sender is the walk's `oSL` row (`BR` new memory,
  `BrRange.br_NM_lt`) or an `oEP` row (its new memory, `gnew = 1`);
* positions `24..27` are `(mU + mD)·M`: the old memory (`gold = 1` on a walk row,
  `SnRange.sn_M_lt` at `cont = 0`);
* `MATR` (`oLM`): the new memory, `gnew = 1` on `oLM`.

`SnContMem` is satisfiable on honest traces: an honest node's memory is `< 2^25`, so its 16-bit
limbs are `< 65536` (and every honest `cont = 1` row stores them as such).
-/

namespace StateM5a.SnLimbsAll

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.SnRange

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- **Premise (continued keys)**: the memory limbs of the rows with `cont = 1` are 16-bit — the new
node's (`gnew`) and the old node's (`gold`). -/
def SnContMem (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "cont") = 1 →
    (ev tr 3 r pub (Sn.c "gnew") = 1 → ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536) ∧
    (ev tr 3 r pub (Sn.c "gold") = 1 → ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536)

theorem sn_mem_gnew : Sn.c "gnew" - (Sn.c "oLR" + Sn.c "oLM" + Sn.c "oEU" + Sn.c "oEB" + Sn.c "oEP" +
    Sn.c "oEM") ∈ Sn.constraints := by
  unfold Sn.constraints; simp

theorem sn_mem_gold : Sn.c "gold" - (Sn.c "act" - Sn.c "oLM" - Sn.c "oEP" - Sn.c "oEM") ∈ Sn.constraints :=
  SnFinal4.sn_mem_gold'

/-- The arithmetic of `gnew_of` on plain naturals (`omega` directly on the trace's `ev` atoms is
over the memory budget). -/
theorem gnew_arith {act mF mU mD oLS oLM oEP oEM oLR oEU oLX oEX oLD oED oLZ oEZ oES oEB gnew : Nat}
    (bA : act ≤ 1)
    (c1 : mF + (mU + (mD + (oLS + (oLM + (oEP + (oEM + 0)))))) = act)
    (c3 : oLR + (oEU + (oLX + (oEX + 0))) = mU)
    (c4 : oLD + (oED + (oLZ + (oEZ + (oES + (oEB + 0))))) = mD)
    (c7 : gnew = oLR + (oLM + (oEU + (oEB + (oEP + (oEM + 0)))))) :
    (oLR = 1 → gnew = 1) ∧ (oLM = 1 → gnew = 1) ∧ (oEU = 1 → gnew = 1) ∧ (oEB = 1 → gnew = 1) ∧
      (oEP = 1 → gnew = 1) ∧ (oEM = 1 → gnew = 1) := by
  omega

section
variable {tr : Trace Fp} {pub : List Fp}

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- `gnew = 1` on a row with one of the new-node ops. -/
theorem gnew_of {r : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0) {o : String}
    (ho : o = "oLR" ∨ o = "oLM" ∨ o = "oEU" ∨ o = "oEB" ∨ o = "oEP" ∨ o = "oEM")
    (h1 : ev tr 3 r pub (Sn.c o) = 1) : ev tr 3 r pub (Sn.c "gnew") = 1 := by
  have hb : ∀ s ∈ snNames, ev tr 3 r pub (Sn.c s) ≤ 1 := fun s hs => sn_flag_le hc s hs
  have S := fun (s : String) (l : List String) (h : s :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s l h hl
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e4 := S "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e7 := S "oLR" ["oLM", "oEU", "oEB", "oEP", "oEM"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc]
    at e1 e3 e4 e7
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  have c4 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mD)
  have c7 := eq_of_sub (hold rfl hc sn_mem_gnew)
  rw [e1] at c1; rw [e3] at c3; rw [e4] at c4; rw [e7] at c7
  have bA := hb "act" (by simp [snNames])
  clear hb S e1 e3 e4 e7
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (gnew_arith bA c1 c3 c4 c7).1 h1
  · exact (gnew_arith bA c1 c3 c4 c7).2.1 h1
  · exact (gnew_arith bA c1 c3 c4 c7).2.2.1 h1
  · exact (gnew_arith bA c1 c3 c4 c7).2.2.2.1 h1
  · exact (gnew_arith bA c1 c3 c4 c7).2.2.2.2.1 h1
  · exact (gnew_arith bA c1 c3 c4 c7).2.2.2.2.2 h1

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : XSbHi D extra nb np tr pub)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)

include hH hxB hxD hxK hN hxr in
/-- **New memory limbs of every row with a new node** (`cont = 1` from `SnContMem`). -/
theorem sn_NM_all (hCM : SnContMem tr pub) {r : Nat} (hr : r < tr.height 3)
    (hg : ev tr 3 r pub (Sn.c "gnew") = 1) : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hcb := FieldRows2.sn_bool hc "cont" (by simp)
  rcases (by omega : ev tr 3 r pub (Sn.c "cont") = 0 ∨ ev tr 3 r pub (Sn.c "cont") = 1) with h0 | h1
  · exact sn_NM_lt hH hxB hxD hxK hN hxr hr hg h0
  · exact (hCM r hr h1).1 hg

include hH hxB hxD hxK hN hxr hxV in
/-- **Old memory limbs of every row with an old node** (`cont = 1` from `SnContMem`). -/
theorem sn_M_all (hCM : SnContMem tr pub) {r : Nat} (hr : r < tr.height 3)
    (hg : ev tr 3 r pub (Sn.c "gold") = 1) : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hcb := FieldRows2.sn_bool hc "cont" (by simp)
  rcases (by omega : ev tr 3 r pub (Sn.c "cont") = 0 ∨ ev tr 3 r pub (Sn.c "cont") = 1) with h0 | h1
  · exact sn_M_lt hH hxB hxD hxK hN hxr hxV hr hg h0
  · exact (hCM r hr h1).2 hg

include hH hxB hxD hxK hN hxr in
/-- **`SnMatLimbs` from `Holds`** (and `SnContMem`). -/
theorem snMatLimbs_of (hCM : SnContMem tr pub) : SnMatLimbs tr pub := fun r hr h1 =>
  sn_NM_all hH hxB hxD hxK hN hxr hCM hr
    (gnew_of (tbl_sn D extra nb np hH r (List.mem_range.2 hr)) (Or.inr (Or.inl rfl)) h1)

theorem map4_get {f g : Expr → Fp} {A B : List Expr} (hA : A.length = 4) (hB : B.length = 4)
    (h : A.map f = B.map g) {k : Nat} (hk : k < 4) : f (A.getD k 0) = g (B.getD k 0) := by
  have := congrArg (fun l => l[k]?) h
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
  simp only [Option.map_some, Option.some.injEq] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < A.length by omega),
    List.getElem?_eq_getElem (show k < B.length by omega), Option.getD_some]
  exact this

theorem fpeq {a b : Fp} {n : Nat} (e : a = b) (h : b.toNat < n) : a.toNat < n := by rw [e]; exact h

include hH hxB hxD hxK hN hxr in
set_option maxHeartbeats 4000000 in
/-- **The split answer's memory limbs** `sm` of a split row (`gX`): the `SPR` sender's new memory. -/
theorem sm_lt (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false) (hCM : SnContMem tr pub)
    {s : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1) :
    ∀ k, k < 4 → ev tr 3 s pub (Sn.c "sm" k) < 65536 := by
  intro k hk
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_spr_rX) hs rfl (ev_one_eval hX)
  have hsm : ((List.range 4).map fun t => Sn.c "sm" t).getD k 0 = Sn.c "sm" k := getD_r4 _ hk
  rcases spr_src hH hxP hm with ⟨r, hr, h1, he⟩ | ⟨p, hp, h1, he⟩
  · have he' : brSprS.map (E tr 2 r pub) = snSprR.map (E tr 3 s pub) := he.symm
    obtain ⟨-, -, -, -, em⟩ := spr_dec he' (by simp [pack2])
    have e := map4_get (by simp [Br.NM, memLimbs]) (by simp) em hk
    rw [hsm] at e
    have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
    have := br_NM_lt hH hxB hxD hxK hxr hr (osl_flags hc h1).2.1 k hk
    exact fpeq e.symm this
  · have he' : snSprS.map (E tr 3 p pub) = snSprR.map (E tr 3 s pub) := he.symm
    obtain ⟨-, -, -, -, em⟩ := spr_dec he' (by simp [pack2])
    have e := map4_get (by simp [Sn.NM, memLimbs]) (by simp) em hk
    rw [hsm] at e
    have hc := tbl_sn D extra nb np hH p (List.mem_range.2 hp)
    have := sn_NM_all hH hxB hxD hxK hN hxr hCM hp (gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h1) k hk
    exact fpeq e.symm this

theorem sn_uo_nm (k : Nat) (hk : k < 4) :
    snW.uo[20 + k]? = some (gnu * Sn.NM.getD k 0 + Sn.gX * Sn.c "sm" k) := by
  rw [sn_uo]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem sn_uo_om (k : Nat) (hk : k < 4) :
    snW.uo[24 + k]? = some ((Sn.c "mU" + Sn.c "mD") * Sn.M.getD k 0) := by
  rw [sn_uo]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

include hH hxB hxD hxK hN hxr hxV in
set_option maxHeartbeats 8000000 in
/-- **`SnUpLimbs` from `Holds`** (and `SnContMem`). -/
theorem snUpLimbs_of (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false) (hCM : SnContMem tr pub) :
    SnUpLimbs tr pub := by
  intro r hr hg k hk1 hk2
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := hg
  obtain ⟨hb, hA, hLS, hLM, hEP, hEM, hs, hF, hU, hD, -⟩ := sn_flags' hc hg'
  have b1 := hb "oLR" (by simp [snNames]); have b2 := hb "oEU" (by simp [snNames])
  have b3 := hb "oEB" (by simp [snNames]); have b4 := hb "oLX" (by simp [snNames])
  have b5 := hb "oEX" (by simp [snNames]); have b6 := hb "mU" (by simp [snNames])
  have b7 := hb "mD" (by simp [snNames])
  have hgold : ev tr 3 r pub (Sn.c "gold") = 1 := SnFinal4.gold_of hc hA hLM hEP hEM
  rcases (by omega : k < 24 ∨ 24 ≤ k) with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, k = 20 + j := ⟨k - 20, by omega⟩
    show ((snW.uo.map fun x => x.eval tr 3 r pub).getD (20 + j) 0).toNat < 65536
    rw [getD_map_some (sn_uo_nm j (by omega))]
    change ev tr 3 r pub (gnu * Sn.NM.getD j 0 + Sn.gX * Sn.c "sm" j) < 65536
    have eN : ev tr 3 r pub gnu = ev tr 3 r pub (Sn.c "oLR") + ev tr 3 r pub (Sn.c "oEU") + ev tr 3 r pub (Sn.c "oEB") := by
      unfold gnu; rw [ev_add_lt (by rw [ev_add_lt (by omega)]; omega), ev_add_lt (by omega)]
    have eX : ev tr 3 r pub Sn.gX = ev tr 3 r pub (Sn.c "oLX") + ev tr 3 r pub (Sn.c "oEX") := by
      unfold Sn.gX; rw [ev_add_lt (by omega)]
    rcases (by omega : ev tr 3 r pub gnu = 1 ∧ ev tr 3 r pub Sn.gX = 0 ∨
        ev tr 3 r pub gnu = 0 ∧ ev tr 3 r pub Sn.gX = 1 ∨ ev tr 3 r pub gnu = 0 ∧ ev tr 3 r pub Sn.gX = 0) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ev_hadd, ev_gm h1, ev_gm0 h2, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
      have hgn : ev tr 3 r pub (Sn.c "gnew") = 1 := by
        rcases (by omega : ev tr 3 r pub (Sn.c "oLR") = 1 ∨ ev tr 3 r pub (Sn.c "oEU") = 1 ∨
          ev tr 3 r pub (Sn.c "oEB") = 1) with e | e | e
        · exact gnew_of hc (Or.inl rfl) e
        · exact gnew_of hc (Or.inr (Or.inr (Or.inl rfl))) e
        · exact gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e
      exact sn_NM_all hH hxB hxD hxK hN hxr hCM hr hgn j (by omega)
    · rw [ev_hadd, ev_gm0 h1, ev_gm h2, Nat.zero_add, Nat.mod_eq_of_lt (ev_lt _)]
      exact sm_lt hH hxB hxD hxK hN hxr (by assumption) hCM hr h2 j (by omega)
    · rw [ev_hadd, ev_gm0 h1, ev_gm0 h2]; simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = 24 + j := ⟨k - 24, by omega⟩
    show ((snW.uo.map fun x => x.eval tr 3 r pub).getD (24 + j) 0).toNat < 65536
    rw [getD_map_some (sn_uo_om j (by omega))]
    change ev tr 3 r pub ((Sn.c "mU" + Sn.c "mD") * Sn.M.getD j 0) < 65536
    have e : ev tr 3 r pub (Sn.c "mU" + Sn.c "mD") = ev tr 3 r pub (Sn.c "mU") + ev tr 3 r pub (Sn.c "mD") :=
      ev_add_lt (by omega)
    rcases (by omega : ev tr 3 r pub (Sn.c "mU" + Sn.c "mD") = 0 ∨ ev tr 3 r pub (Sn.c "mU" + Sn.c "mD") = 1) with
      h0 | h1
    · rw [ev_gm0 h0]; omega
    · rw [ev_gm h1]; exact sn_M_all hH hxB hxD hxK hN hxr hxV hCM hr hgold j (by omega)

end

end StateM5a.SnLimbsAll
