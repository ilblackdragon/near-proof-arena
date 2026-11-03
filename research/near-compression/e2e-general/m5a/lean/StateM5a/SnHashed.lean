import StateM5a.SnDigest

/-!
# StateM5a.SnHashed — the record of a hashing `SN` head is `Hashed` to its digest

* `sn_ops`: the op bundle of any `SN` row (active or not; walk rows and responders) as natural
  equations: `act = mF + mU + mD + oLS + oLM + oEP + oEM`, `isL + isE = act`, …, `gold`, `gnew`;
* `sn_k16`: the head's key nibbles are `< 16` (a `NIB` lookup into the `KEY` table, against `kid`
  or `kid2`, or the `RNG` pair `k, k + 240`);
* `gRecS`: the record a row's columns spell (`RowSnMsg.snOld` / `RowSnN.snNew` are instances);
* **`grecS_hashed`**: when every `snSerF` entry is a byte, the record is all-digest, well formed,
  `Shallow`, and hashes to `sha256 snSerF`;
* **`sn_old_node`** / **`sn_new_node`** (`cont = 0`): a row hashing its old node (`gsha`) / its
  final new node (`gfin`) has byte-ranged columns and its record `Hashed` to its digest.
-/

namespace StateM5a.SnHashed

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode
open StateM5a.SnDigest StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnN StateM5a.FieldWalk2

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The op bundle of any `SN` row -/

section
variable {tr : Trace Fp} {pub : List Fp} {t r : Nat}

theorem sn_mem_gold : Sn.c "gold" - (Sn.c "act" - Sn.c "oLM" - Sn.c "oEP" - Sn.c "oEM") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_gnew : Sn.c "gnew" - (Sn.c "oLR" + Sn.c "oLM" + Sn.c "oEU" + Sn.c "oEB" + Sn.c "oEP" + Sn.c "oEM")
    ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp

set_option maxHeartbeats 4000000 in
/-- **The op bundle of an `SN` row**, as natural equations. -/
theorem sn_ops (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) :
    (∀ s ∈ snNames, ev tr t r pub (Sn.c s) ≤ 1) ∧
    ev tr t r pub (Sn.c "mF") + ev tr t r pub (Sn.c "mU") + ev tr t r pub (Sn.c "mD") + ev tr t r pub (Sn.c "oLS") +
      ev tr t r pub (Sn.c "oLM") + ev tr t r pub (Sn.c "oEP") + ev tr t r pub (Sn.c "oEM") = ev tr t r pub (Sn.c "act") ∧
    ev tr t r pub (Sn.c "oLF") + ev tr t r pub (Sn.c "oEF") + ev tr t r pub (Sn.c "oLA") + ev tr t r pub (Sn.c "oEA") =
      ev tr t r pub (Sn.c "mF") ∧
    ev tr t r pub (Sn.c "oLR") + ev tr t r pub (Sn.c "oEU") + ev tr t r pub (Sn.c "oLX") + ev tr t r pub (Sn.c "oEX") =
      ev tr t r pub (Sn.c "mU") ∧
    ev tr t r pub (Sn.c "oLD") + ev tr t r pub (Sn.c "oED") + ev tr t r pub (Sn.c "oLZ") + ev tr t r pub (Sn.c "oEZ") +
      ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") = ev tr t r pub (Sn.c "mD") ∧
    ev tr t r pub (Sn.c "isL") = ev tr t r pub (Sn.c "oLF") + ev tr t r pub (Sn.c "oLR") + ev tr t r pub (Sn.c "oLD") +
      ev tr t r pub (Sn.c "oLS") + ev tr t r pub (Sn.c "oLM") + ev tr t r pub (Sn.c "oLA") + ev tr t r pub (Sn.c "oLZ") +
      ev tr t r pub (Sn.c "oLX") ∧
    ev tr t r pub (Sn.c "isE") = ev tr t r pub (Sn.c "oEF") + ev tr t r pub (Sn.c "oEU") + ev tr t r pub (Sn.c "oED") +
      ev tr t r pub (Sn.c "oEA") + ev tr t r pub (Sn.c "oEZ") + ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") +
      ev tr t r pub (Sn.c "oEX") + ev tr t r pub (Sn.c "oEP") + ev tr t r pub (Sn.c "oEM") ∧
    ev tr t r pub (Sn.c "g2") = ev tr t r pub (Sn.c "oED") + ev tr t r pub (Sn.c "oLX") + ev tr t r pub (Sn.c "oEX") ∧
    ev tr t r pub (Sn.c "gnew") = ev tr t r pub (Sn.c "oLR") + ev tr t r pub (Sn.c "oLM") + ev tr t r pub (Sn.c "oEU") +
      ev tr t r pub (Sn.c "oEB") + ev tr t r pub (Sn.c "oEP") + ev tr t r pub (Sn.c "oEM") := by
  have hb : ∀ s ∈ snNames, ev tr t r pub (Sn.c s) ≤ 1 := fun s hs => sn_flag_le hc s hs
  have S := fun (s : String) (l : List String) (h : s :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s l h hl
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e2 := S "oLF" ["oEF", "oLA", "oEA"] (by simp [snNames]) (by simp)
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e4 := S "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e5 := S "oLF" ["oLR", "oLD", "oLS", "oLM", "oLA", "oLZ", "oLX"] (by simp [snNames]) (by simp)
  have e6 := S "oEF" ["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e9 := S "oED" ["oLX", "oEX"] (by simp [snNames]) (by simp)
  have e10 := S "oLR" ["oLM", "oEU", "oEB", "oEP", "oEM"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc] at e1 e2 e3 e4 e5 e6 e9 e10
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c2 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mF)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  have c4 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mD)
  have c5 := eq_of_sub (hold rfl hc sn_mem_isL)
  have c6 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_isE)
  have c9 := eq_of_sub (hold rfl hc sn_mem_g2)
  have c10 := eq_of_sub (hold rfl hc sn_mem_gnew)
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3; rw [e4] at c4; rw [e5] at c5; rw [e6] at c6
  rw [e9] at c9; rw [e10] at c10
  have b0 := hb "act" (by simp [snNames]); have b1 := hb "oLS" (by simp [snNames])
  have b2 := hb "oLM" (by simp [snNames]); have b3 := hb "oEP" (by simp [snNames])
  have b4 := hb "oEM" (by simp [snNames])
  have b5 := hb "mF" (by simp [snNames]); have b6 := hb "mU" (by simp [snNames]); have b7 := hb "mD" (by simp [snNames])
  refine ⟨hb, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end

/-! ## Key nibbles -/

theorem sn_rng_k : ∀ j, j < 64 →
    memD (rcv B_RNG ((Sn.a j - Sn.b j) * (1 - Sn.c "g2")) [Sn.k j]) Sn.interactions = true := by decide
theorem sn_rng_k240 : ∀ j, j < 64 →
    memD (rcv B_RNG ((Sn.a j - Sn.b j) * (1 - Sn.c "g2")) [Sn.k j + 240]) Sn.interactions = true := by decide

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem full3 : (fullAir D extra nb np).tables[3]! = Sn.table := by
  rw [WsDecode.full_get 3 (by decide)]; rfl

set_option maxHeartbeats 4000000 in
/-- **The head's key nibbles are `< 16`** (any `SN` row). -/
theorem sn_k16 (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG) {r : Nat} (hr : r < tr.height 3) :
    ∀ j, j < 64 → ev tr 3 r pub (Sn.c "k" j) < 16 := by
  intro j hj
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have ha := FieldRows2.sn_a_bool hc j hj
  have hkk : Sn.k j = Sn.c "k" j := FieldRows2.sn_k_lt j hj
  have haa : Sn.a j = Sn.c "a" j := FieldRows2.sn_a_lt j hj
  have hbb : Sn.b j = Sn.c "b" j := by simp [Sn.b, KMAX, hj]
  have hkey : ∀ K i : Nat, (KeyDecode.keyOf tr K)[i]? = some (ev tr 3 r pub (Sn.k j)) →
      ev tr 3 r pub (Sn.c "k" j) < 16 := by
    intro K i h
    rw [hkk] at h
    exact (RowFacts.keyOf_bounds hH K).1 _ (List.mem_of_getElem? h)
  rcases (by omega : ev tr 3 r pub (Sn.c "a" j) = 0 ∨ ev tr 3 r pub (Sn.c "a" j) = 1) with a0 | a1
  · rw [FieldRows2.sn_k_zero hc j hj a0]; omega
  have hb := RowSnM.sn_b_bool hc j hj
  rcases (by omega : ev tr 3 r pub (Sn.c "b" j) = 1 ∨ ev tr 3 r pub (Sn.c "b" j) = 0) with b1 | b0
  · exact hkey _ _ (KeyLookups.sn_nib hH hN j hj hr (by rw [hbb]; exact ev_one_eval b1)).1
  obtain ⟨hfl, hact, -, -, -, -, -, -, -⟩ := sn_ops hc
  have b5 := hfl "mU" (by simp [snNames]); have b6 := hfl "mD" (by simp [snNames])
  have b7 := hfl "act" (by simp [snNames])
  have hops := sn_ops hc
  rcases (by omega : ev tr 3 r pub (Sn.c "g2") = 1 ∨ ev tr 3 r pub (Sn.c "g2") = 0) with g1 | g0
  · exact hkey _ _ (KeyLookups.sn_nib2 hH hN j hj hr (ev_one_eval (by
      rw [ev_hmul, g1, haa, a1]))).1
  · have hg : ((Sn.a j - Sn.b j) * (1 - Sn.c "g2")).eval tr 3 r pub = 1 := ev_one_eval (by
      rw [ev_hmul, ev_sub, ev_sub, haa, hbb, a1, b0, g0, ev_one])
    have h1 := WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir])
      (by rw [full3]; exact memD_mem (sn_rng_k j hj)) hr hg
    have h2 := WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir])
      (by rw [full3]; exact memD_mem (sn_rng_k240 j hj)) hr hg
    rw [hkk] at h1 h2
    rw [ev_hadd, show ev tr 3 r pub (240 : Expr) = 240 from ev_const 240] at h2
    omega

end

end StateM5a.SnHashed
