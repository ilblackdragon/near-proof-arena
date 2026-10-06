import ZkFormal.Chacha.Rng.Row
import ZkFormal.Chacha.Sound.Contract

/-!
# ZkFormal.Chacha.Rng.Sound — `rng_contract` and `genIndex_contract`

Hypothesis `ChachaRecv`: every active row's `busChacha` message is a ChaCha20 output
message (`Sound.chachaMsg key ctr idx ((chachaBlock key ctr)[idx]!)`).  This is what the
bus balance gives together with `Sound.chacha_contract` when the ChaCha table is the only
sender on `busChacha` (`recv_of_balance`).

* `rng_contract`: the word drawn on an active row is `streamWord key k`, `k = 16·ctr + idx`;
* `genIndex_contract`: an active `busGen` message is `genMsg key kstart n j kend` with
  `genIndex 64 n (rngAt key kstart) = some (j, rngAt key kend)` and `1 ≤ n < 2^14`.
-/

namespace ZkFormal.Chacha.Rng

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- Stream position of row `r`. -/
def kv (tr : Trace Fp) (t r : Nat) : Nat := 16 * cv tr t r colCtr + numv tr t r colIdx 4
/-- The key of row `r`. -/
def keyOf (tr : Trace Fp) (t r : Nat) : List Nat :=
  (List.range 8).map fun j => cv tr t r (colK j 0) + 65536 * cv tr t r (colK j 1)
def vv (tr : Trace Fp) (t r : Nat) : Nat := cv tr t r colVlo + 65536 * cv tr t r colVhi

/-- The `busGen` message of a `gen_index` call. -/
def genMsg (key : List Nat) (kstart n j kend : Nat) : List Fp :=
  (List.range 16).map (fun q => Fp.ofNat ((key.getD (q / 2) 0 / 2 ^ (16 * (q % 2))) % 65536)) ++
    [Fp.ofNat kstart, Fp.ofNat n, Fp.ofNat j, Fp.ofNat kend]

/-- The `busChacha` message received on row `r`. -/
def recvMsg (tr : Trace Fp) (t r : Nat) (pub : List Fp) : List Fp :=
  (keyMsg ++ [ZkFormal.Chacha.Table.E.c colCtr, idxE, ZkFormal.Chacha.Table.E.c colVlo,
    ZkFormal.Chacha.Table.E.c colVhi]).map (·.eval tr t r pub)

theorem recvMsg_eq (busChacha busGen r : Nat) :
    (interactions busChacha busGen).head!.msgVal tr t r pub = recvMsg tr t r pub := rfl

/-- Every active row receives a ChaCha20 output word. -/
def ChachaRecv (tr : Trace Fp) (t : Nat) (pub : List Fp) (busChacha busGen : Nat) : Prop :=
  ∀ r, r < tr.height t → cv tr t r colA = 1 →
    ∃ key ctr idx, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ ctr < 2 ^ 26 ∧ idx < 16 ∧
      recvMsg tr t r pub = Sound.chachaMsg key ctr idx ((chachaBlock key ctr)[idx]!)

theorem ofNat_inj {a b : Nat} (ha : a < 2013265921) (hb : b < 2013265921) (h : Fp.ofNat a = Fp.ofNat b) :
    a = b := by
  have := congrArg Fp.toNat h
  rw [Fp.toNat_ofNat, Fp.toNat_ofNat] at this
  unfold P at this; rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem eval_c (r x : Nat) : (ZkFormal.Chacha.Table.E.c x).eval tr t r pub = Fp.ofNat (cv tr t r x) := by
  show tr.cell t r x = _; unfold cv; rw [Fp.ofNat_toNat]

theorem eval_num (r : Nat) (col : Nat → Nat) (len : Nat) :
    (num col len).eval tr t r pub = Fp.ofNat (numv tr t r col len) := by
  rw [eval_eq, zev_num, intCast_ofNat]

/-- Decoding a received ChaCha message. -/
theorem decode (r : Nat) {key : List Nat} {ctr idx w : Nat} (hk : key.length = 8)
    (hkey : ∀ x ∈ key, x < 2 ^ 32) (hc : ctr < 2 ^ 26) (hi : idx < 16) (hw : w < 2 ^ 32)
    (hb : ∀ b, b < 4 → cv tr t r (colIdx b) ≤ 1)
    (h : recvMsg tr t r pub = Sound.chachaMsg key ctr idx w) :
    keyOf tr t r = key ∧ (∀ j l, j < 8 → l < 2 → cv tr t r (colK j l) < 65536) ∧
    cv tr t r colCtr = ctr ∧ numv tr t r colIdx 4 = idx ∧ vv tr t r = w ∧
    cv tr t r colVlo < 65536 ∧ cv tr t r colVhi < 65536 := by
  unfold recvMsg Sound.chachaMsg at h
  simp only [List.map_append, keyMsg, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h2
  obtain ⟨hctr, hidx, hlo, hhi, -⟩ := h2
  have hidx' : numv tr t r colIdx 4 < 16 := nbits_lt hb
  have hlim : ∀ q, q < 16 → cv tr t r (colK (q / 2) (q % 2)) = (key.getD (q / 2) 0 / 2 ^ (16 * (q % 2))) % 65536 := by
    intro q hq
    have := congrArg (·.getD q 0) h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq, Option.map_some,
      Option.getD_some, Function.comp, eval_c] at this
    rw [← List.getD_eq_getElem?_getD] at this
    exact ofNat_inj (cv_lt _ _) (by have := Nat.mod_lt (key.getD (q / 2) 0 / 2 ^ (16 * (q % 2))) (show 65536 > 0 by decide); omega) this
  rw [eval_c] at hctr hlo hhi; rw [show idxE = num colIdx 4 from rfl, eval_num] at hidx
  have ectr := ofNat_inj (cv_lt _ _) (by omega) hctr
  have eidx := ofNat_inj (by omega) (by omega) hidx
  have elo := ofNat_inj (cv_lt _ _) (by omega) hlo
  have ehi := ofNat_inj (cv_lt _ _) (by omega) hhi
  have hK : ∀ j l, j < 8 → l < 2 → cv tr t r (colK j l) = (key.getD j 0 / 2 ^ (16 * l)) % 65536 := by
    intro j l hj hl
    have := hlim (2 * j + l) (by omega)
    rwa [show (2 * j + l) / 2 = j by omega, show (2 * j + l) % 2 = l by omega] at this
  refine ⟨?_, fun j l hj hl => by rw [hK j l hj hl]; exact Nat.mod_lt _ (by decide), ectr, eidx, ?_,
    by rw [elo]; omega, by rw [ehi]; omega⟩
  · apply List.ext_getElem (by simp [keyOf, hk])
    intro j h1 h2
    simp only [keyOf, List.getElem_map, List.getElem_range]
    have hj : j < 8 := by simp [keyOf] at h1; exact h1
    rw [hK j 0 hj (by decide), hK j 1 hj (by decide)]
    have := hkey (key[j]) (List.getElem_mem _)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    simp; omega
  · unfold vv; rw [elo, ehi]; omega

/-! ## Call structure -/

def attv (tr : Trace Fp) (t r : Nat) : Nat := numv tr t r colAtt 6

section
variable (hL : GLocal tr t pub)
include hL

theorem bAtt {r : Nat} (hr : r < tr.height t) : attv tr t r < 64 :=
  nbits_lt (fun b hb => bit hL hr (x := colAtt b) (by unfold colAtt; omega) (by unfold colAtt; omega)
    (by unfold colAtt; omega))

theorem bIdx {r : Nat} (hr : r < tr.height t) : ∀ b, b < 4 → cv tr t r (colIdx b) ≤ 1 :=
  fun b hb => bit hL hr (x := colIdx b) (by unfold colIdx; omega) (by unfold colIdx; omega) (by unfold colIdx; omega)

theorem zev_g {r : Nat} : zev (tenv tr t r pub) gCont =
    (cv tr t r colA : Int) * (1 - (cv tr t r colAcc : Int)) := by
  simp [gCont, zev_mul, zev_sub, zev_c, cur_cv]

/-- `n.a − n.st = a·(1 − acc)`. -/
theorem trans0 {r : Nat} (hr : r + 1 < tr.height t) :
    (cv tr t (r + 1) colA : Int) - cv tr t (r + 1) colSt = (cv tr t r colA : Int) * (1 - cv tr t r colAcc) := by
  have hz := hL.zc (by omega : r < tr.height t) (mem_cM (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n colA) (ZkFormal.Chacha.Table.E.n colSt)) gCont)
    (by simp [cM]))
  simp only [zev_sub, zev_n, nxt_cv hr, zev_g hL] at hz
  have := bA hL (show r < _ by omega); have := bAcc hL (show r < _ by omega)
  have := bA hL hr; have := bSt hL hr
  rcases (show cv tr t r colA = 0 ∨ cv tr t r colA = 1 by omega) with e | e <;>
  rcases (show cv tr t r colAcc = 0 ∨ cv tr t r colAcc = 1 by omega) with e' | e' <;>
  (rw [e, e'] at hz ⊢; simp at hz ⊢; have := hz (by omega) (by omega); omega)

/-- Continuation: `a = 1`, `acc = 0` on row `r`. -/
theorem cont {r : Nat} (hr : r + 1 < tr.height t) (ha : cv tr t r colA = 1) (hacc : cv tr t r colAcc = 0) :
    cv tr t (r + 1) colA = 1 ∧ cv tr t (r + 1) colSt = 0 ∧
    numv tr t (r + 1) colN 14 = numv tr t r colN 14 ∧ cv tr t (r + 1) colKs = cv tr t r colKs ∧
    attv tr t (r + 1) = attv tr t r + 1 ∧
    (∀ j l, j < 8 → l < 2 → cv tr t (r + 1) (colK j l) = cv tr t r (colK j l)) ∧
    (cv tr t r colCtr < 2 ^ 26 → cv tr t (r + 1) colCtr < 2 ^ 26 → kv tr t (r + 1) = kv tr t r + 1) := by
  have hr0 : r < tr.height t := by omega
  have hg : zev (tenv tr t r pub) gCont = 1 := by rw [zev_g hL, ha, hacc]; rfl
  have t0 := trans0 hL hr; rw [ha, hacc] at t0
  have := bA hL hr; have := bSt hL hr
  have mul1 : ∀ e : Expr, e ∈ cM → zev (tenv tr t r pub) (.mul gCont e) = zev (tenv tr t r pub) e := by
    intro e _; rw [zev_mul, hg, Int.one_mul]
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · have hz := hL.zc hr0 (mem_cM (e := .mul gCont (ZkFormal.Chacha.Table.E.sub (num colN 14 true) nE)) (by simp [cM]))
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_numN hr, nE, zev_num] at hz
    have := nbits_lt (f := fun b => cv tr t r (colN b)) (n := 14) (fun b hb => bN hL hr0 hb)
    have := nbits_lt (f := fun b => cv tr t (r + 1) (colN b)) (n := 14) (fun b hb => bN hL hr hb)
    unfold numv at *; have := hz (by omega) (by omega); omega
  · have hz := hL.zc hr0 (mem_cM (e := .mul gCont (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n colKs) (ZkFormal.Chacha.Table.E.c colKs))) (by simp [cM]))
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_n, zev_c, nxt_cv hr, cur_cv] at hz
    have := cv_lt (tr := tr) (t := t) r colKs; have := cv_lt (tr := tr) (t := t) (r + 1) colKs
    have := hz (by omega) (by omega); omega
  · have hz := hL.zc hr0 (mem_cM (e := .mul gCont (ZkFormal.Chacha.Table.E.sub (num colAtt 6 true) (.add attE (ZkFormal.Chacha.Table.E.k 1))))
      (by simp [cM]))
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_numN hr, zev_add, attE, zev_num, zev_k] at hz
    have := bAtt hL hr0; have := bAtt hL hr
    unfold attv at *; have := hz (by omega) (by omega); omega
  · intro j l hj hl
    have hz := hL.zc hr0 (mem_cK (e := .mul gCont (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n (colK j l)) (ZkFormal.Chacha.Table.E.c (colK j l))))
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩))
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_n, zev_c, nxt_cv hr, cur_cv] at hz
    have := cv_lt (tr := tr) (t := t) r (colK j l); have := cv_lt (tr := tr) (t := t) (r + 1) (colK j l)
    have := hz (by omega) (by omega); omega
  · intro hc0 hc1
    have hz := hL.zc hr0 (mem_cM (e := .mul gCont (ZkFormal.Chacha.Table.E.sub kN (.add kE (ZkFormal.Chacha.Table.E.k 1)))) (by simp [cM]))
    rw [zev_mul, hg, Int.one_mul, zev_sub, kN, zev_add, zev_smul, zev_n, nxt_cv hr, zev_numN hr,
      kE, zev_add, zev_add, zev_smul, zev_c, cur_cv, idxE, zev_num, zev_k] at hz
    have := nbits_lt (f := fun b => cv tr t r (colIdx b)) (n := 4) (bIdx hL hr0)
    have := nbits_lt (f := fun b => cv tr t (r + 1) (colIdx b)) (n := 4) (bIdx hL hr)
    unfold kv numv at *; have := hz (by omega) (by omega); omega

/-- A start row: `att = 0`, `kstart = k`. -/
theorem start {r : Nat} (hr : r < tr.height t) (hst : cv tr t r colSt = 1) (hc : cv tr t r colCtr < 2 ^ 26) :
    attv tr t r = 0 ∧ cv tr t r colKs = kv tr t r := by
  have h1 := hL.zc hr (mem_cM (e := .mul (ZkFormal.Chacha.Table.E.c colSt) attE) (by simp [cM]))
  have h2 := hL.zc hr (mem_cM (e := .mul (ZkFormal.Chacha.Table.E.c colSt) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colKs) kE)) (by simp [cM]))
  rw [zev_mul, zev_c, cur_cv, hst, attE, zev_num] at h1
  rw [zev_mul, zev_c, cur_cv, hst, zev_sub, zev_c, cur_cv, kE, zev_add, zev_smul, zev_c, cur_cv,
    idxE, zev_num] at h2
  have := bAtt hL hr; have := nbits_lt (f := fun b => cv tr t r (colIdx b)) (n := 4) (bIdx hL hr)
  have := cv_lt (tr := tr) (t := t) r colKs
  unfold attv kv numv at *
  simp only [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at h1 h2
  exact ⟨by have := h1 (by omega) (by omega); omega, by have := h2 (by omega) (by omega); omega⟩

/-- Row `0`, if active, starts a call. -/
theorem first_start (ha : cv tr t 0 colA = 1) : cv tr t 0 colSt = 1 := by
  have hz := hL.zc (Nat.two_pow_pos _) (mem_cM (e := .mul .isFirst (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colA) (ZkFormal.Chacha.Table.E.c colSt)))
    (by simp [cM]))
  simp only [zev_mul, zev_isFirst, zev_sub, zev_c, cur_cv, ha] at hz
  simp [tenv] at hz
  have := bSt hL (Nat.two_pow_pos (tr.log t)) (r := 0)
  have := hz (by omega) (by omega); omega

end

/-! ## The contracts -/

theorem getBang (l : List Nat) (i : Nat) : l[i]! = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < l.length
  · rw [List.getElem?_eq_getElem h]; simp [h]
  · rw [List.getElem?_eq_none (by omega)]; simp [h]

section
variable (hL : GLocal tr t pub) {busChacha busGen : Nat} (hW : ChachaRecv tr t pub busChacha busGen)
include hL hW

/-- **`rng_contract`**: an active row draws word `kv` of the stream of its key. -/
theorem rng_contract {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) :
    vv tr t r = streamWord (keyOf tr t r) (kv tr t r) ∧ (keyOf tr t r).length = 8 ∧
    (∀ x ∈ keyOf tr t r, x < 2 ^ 32) ∧
    cv tr t r colCtr < 2 ^ 26 ∧ cv tr t r colVlo < 65536 ∧ cv tr t r colVhi < 65536 ∧
    (∀ j l, j < 8 → l < 2 → cv tr t r (colK j l) < 65536) := by
  obtain ⟨key, ctr, idx, hk, hkey, hc, hi, hm⟩ := hW r hr ha
  have hw : (chachaBlock key ctr)[idx]! < 2 ^ 32 := by
    have := streamWord_lt key (16 * ctr + idx)
    unfold streamWord at this
    rwa [show (16 * ctr + idx) / 16 = ctr by omega, show (16 * ctr + idx) % 16 = idx by omega,
      ← getBang] at this
  obtain ⟨ek, hK, ec, ei, ev, hlo, hhi⟩ := decode r hk hkey hc hi hw (bIdx hL hr) hm
  refine ⟨?_, by rw [ek]; exact hk, by rw [ek]; exact hkey, by rw [ec]; exact hc, hlo, hhi, hK⟩
  rw [ev, ek]; unfold kv streamWord; rw [ec, ei]
  rw [show (16 * ctr + idx) / 16 = ctr by omega, show (16 * ctr + idx) % 16 = idx by omega,
    ← getBang]

/-- Walking back from a row of a call. -/
theorem walk {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) :
    ∀ e, e ≤ attv tr t r → e ≤ r ∧ cv tr t (r - e) colA = 1 ∧ attv tr t (r - e) = attv tr t r - e ∧
      keyOf tr t (r - e) = keyOf tr t r ∧ numv tr t (r - e) colN 14 = numv tr t r colN 14 ∧
      cv tr t (r - e) colKs = cv tr t r colKs ∧ kv tr t (r - e) + e = kv tr t r ∧
      (1 ≤ e → cv tr t (r - e) colAcc = 0) := by
  intro e he
  induction e with
  | zero => exact ⟨Nat.zero_le _, ha, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (by omega)⟩
  | succ e ih =>
    obtain ⟨hle, ha', hatt, hkey, hn, hks, hk, -⟩ := ih (by omega)
    have hpos : attv tr t (r - e) ≥ 1 := by omega
    -- `st = 0` on row `r - e` (a start row has `att = 0`)
    have hc := (rng_contract hL hW (by omega) ha').2.2.2.1
    have hst : cv tr t (r - e) colSt = 0 := by
      have := bSt hL (show r - e < _ by omega)
      rcases (show cv tr t (r - e) colSt = 0 ∨ cv tr t (r - e) colSt = 1 by omega) with h | h
      · exact h
      · have := (start hL (by omega) h hc).1; omega
    have hre : 1 ≤ r - e := by
      rcases Nat.eq_zero_or_pos (r - e) with h0 | h0
      · rw [h0] at ha' hst; have := first_start hL ha'; omega
      · exact h0
    obtain ⟨r', hr'⟩ : ∃ r', r - e = r' + 1 := ⟨r - e - 1, by omega⟩
    have t0 := trans0 hL (show r' + 1 < _ by omega)
    rw [← hr', ha', hst] at t0
    have hb1 := bA hL (show r' < _ by omega); have hb2 := bAcc hL (show r' < _ by omega)
    have ha0 : cv tr t r' colA = 1 := by
      rcases (show cv tr t r' colA = 0 ∨ cv tr t r' colA = 1 by omega) with h | h
      · rw [h] at t0; simp at t0
      · exact h
    have hacc0 : cv tr t r' colAcc = 0 := by rw [ha0] at t0; simp at t0; omega
    obtain ⟨-, -, hn', hks', hatt', hK', hk'⟩ := cont hL (show r' + 1 < _ by omega) ha0 hacc0
    rw [← hr'] at hn' hks' hatt' hK' hk'
    have hc0 := (rng_contract hL hW (show r' < _ by omega) ha0).2.2.2.1
    have hkey' : keyOf tr t r' = keyOf tr t (r - e) := by
      unfold keyOf; apply List.map_congr_left; intro j hj
      have hj' := List.mem_range.mp hj
      rw [hK' j 0 hj' (by decide), hK' j 1 hj' (by decide)]
    have hrr : r - (e + 1) = r' := by omega
    rw [hrr]
    refine ⟨by omega, ha0, by omega, by rw [hkey', hkey], by rw [← hn', hn], by rw [← hks', hks], ?_,
      fun _ => hacc0⟩
    have := hk' hc0 hc; omega

/-- **`genIndex_contract`**: an active `busGen` message of the table is the result of
`genIndex 64 n` on the stream state `rngAt key kstart`. -/
theorem genIndex_contract {r : Nat} (hr : r < tr.height t) (hacc : cv tr t r colAcc = 1) :
    ∃ key kstart n j kend, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ 1 ≤ n ∧ n < 2 ^ 14 ∧
      kend < 2 ^ 30 + 1 ∧
      genAt 64 n key kstart = some (j, kend) ∧
      genIndex 64 n (rngAt key kstart) = some (j, rngAt key kend) ∧
      (interactions busChacha busGen)[1]!.msgVal tr t r pub = genMsg key kstart n j kend := by
  have ha : cv tr t r colA = 1 := by
    have hz := hL.zc hr (mem_cM (e := .mul (ZkFormal.Chacha.Table.E.c colAcc) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1) (ZkFormal.Chacha.Table.E.c colA)))
      (by simp [cM]))
    simp only [zev_mul, zev_c, zev_sub, zev_k, cur_cv, hacc] at hz
    have := bA hL hr; have := hz (by omega) (by omega); omega
  have hd := bAtt hL hr
  generalize hdd : attv tr t r = d at *
  obtain ⟨hdr, ha0, hatt0, hkey0, hn0, hks0, hk0, -⟩ := walk hL hW hr ha d (by omega)
  have hc0 := (rng_contract hL hW (by omega) ha0).2.2.2.1
  -- the start row
  have hst : cv tr t (r - d) colSt = 1 := by
    have := bSt hL (show r - d < _ by omega)
    rcases (show cv tr t (r - d) colSt = 0 ∨ cv tr t (r - d) colSt = 1 by omega) with h | h
    · exfalso
      rcases Nat.eq_zero_or_pos (r - d) with h0 | h0
      · rw [h0] at ha0 h; have := first_start hL ha0; omega
      · obtain ⟨r', hr'⟩ : ∃ r', r - d = r' + 1 := ⟨r - d - 1, by omega⟩
        have t0 := trans0 hL (show r' + 1 < _ by omega)
        rw [← hr', ha0, h] at t0
        have := bA hL (show r' < _ by omega); have := bAcc hL (show r' < _ by omega)
        have ha1 : cv tr t r' colA = 1 := by
          rcases (show cv tr t r' colA = 0 ∨ cv tr t r' colA = 1 by omega) with h1 | h1
          · rw [h1] at t0; simp at t0
          · exact h1
        have hacc1 : cv tr t r' colAcc = 0 := by rw [ha1] at t0; simp at t0; omega
        have := (cont hL (show r' + 1 < _ by omega) ha1 hacc1).2.2.2.2.1
        rw [← hr'] at this; omega
    · exact h
  obtain ⟨-, hks⟩ := start hL (by omega) hst hc0
  obtain ⟨hvr, hkl, hkb, hcr, hlo, hhi, hKr⟩ := rng_contract hL hW hr ha
  obtain ⟨n1, n2, hacc_iff, hm2⟩ := draw_row hL hr ha hlo hhi
  have hks' : cv tr t r colKs + d = kv tr t r := by rw [← hks0, hks]; exact hk0
  have hgen : genAt 64 (numv tr t r colN 14) (keyOf tr t r) (cv tr t r colKs) =
      some (numv tr t r colM2 14, kv tr t r + 1) := by
    rw [genAt_some_iff]
    refine ⟨d, by omega, by omega, ?_, ?_, ?_⟩
    · intro i hi
      have hrow : r - (d - i) < tr.height t := by omega
      obtain ⟨-, hai, -, hkeyi, hni, -, hki, hacci⟩ := walk hL hW hr ha (d - i) (by omega)
      obtain ⟨hvi, -, -, -, hloi, hhii, -⟩ := rng_contract hL hW hrow hai
      obtain ⟨-, -, hacci_iff, -⟩ := draw_row hL hrow hai hloi hhii
      have := hacci (by omega)
      have hvi' : cv tr t (r - (d - i)) colVlo + 65536 * cv tr t (r - (d - i)) colVhi =
          streamWord (keyOf tr t (r - (d - i))) (kv tr t (r - (d - i))) := hvi
      rw [hni, hvi', hkeyi] at hacci_iff
      rw [show cv tr t r colKs + i = kv tr t (r - (d - i)) by omega]
      cases h : accepts (numv tr t r colN 14) (streamWord (keyOf tr t r) (kv tr t (r - (d - i))))
      · rfl
      · rw [h] at hacci_iff; have := hacci_iff.mpr rfl; omega
    · have hvr' : cv tr t r colVlo + 65536 * cv tr t r colVhi = streamWord (keyOf tr t r) (kv tr t r) := hvr
      rw [show cv tr t r colKs + d = kv tr t r by omega, ← hvr']; exact hacc_iff.mp hacc
    · have hvr' : cv tr t r colVlo + 65536 * cv tr t r colVhi = streamWord (keyOf tr t r) (kv tr t r) := hvr
      rw [show cv tr t r colKs + d = kv tr t r by omega, ← hvr', hm2]
  refine ⟨keyOf tr t r, cv tr t r colKs, numv tr t r colN 14, numv tr t r colM2 14, kv tr t r + 1,
    hkl, hkb, n1, n2, ?_, hgen, ?_, ?_⟩
  · unfold kv; have := nbits_lt (f := fun b => cv tr t r (colIdx b)) (n := 4) (bIdx hL hr)
    unfold numv at *; omega
  · rw [genIndex_rngAt, hgen]; rfl
  · show (keyMsg ++ [ZkFormal.Chacha.Table.E.c colKs, nE, m2E, .add kE (ZkFormal.Chacha.Table.E.k 1)]).map (·.eval tr t r pub) = _
    unfold genMsg keyMsg
    rw [List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro q hq
      have hq' := List.mem_range.mp hq
      simp only [Function.comp, eval_c]
      congr 1
      have hg : (keyOf tr t r).getD (q / 2) 0 = cv tr t r (colK (q / 2) 0) + 65536 * cv tr t r (colK (q / 2) 1) := by
        simp [keyOf, show q / 2 < 8 by omega]
      rw [hg]
      have := hKr (q / 2) 0 (by omega) (by decide); have := hKr (q / 2) 1 (by omega) (by decide)
      rcases (show q % 2 = 0 ∨ q % 2 = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
    · have hk : (Expr.add kE (ZkFormal.Chacha.Table.E.k 1)).eval tr t r pub = Fp.ofNat (kv tr t r + 1) := by
        rw [eval_eq, kE, zev_add, zev_add, zev_smul, zev_c, cur_cv, idxE, zev_num, zev_k, ← intCast_ofNat]
        unfold kv numv; congr 1
      simp only [List.map_cons, List.map_nil, eval_c, nE, m2E, eval_num, hk]

end

end ZkFormal.Chacha.Rng
