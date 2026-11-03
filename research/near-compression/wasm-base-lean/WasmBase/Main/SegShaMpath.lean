import WasmBase.Main.SegSha

/-!
# WasmBase.Main.SegShaMpath — MPATH's node hash is SHA-384 (E2E M4b)

`Main/SegMpath.lean` proves the Merkle update of MPATH (`mpath_block`, `rch_chain`) for an abstract
compression `node : List F → List F → List F` on 18-limb digests, assumed on every active row
(`chipO`, `chipN`).  Here that hypothesis is discharged from the chip hypothesis `ChipIf`
(`Main/SegSha.lean`) with the SHA-384 node

  `shaNode a b = limbsF ((compressW IV384 (decF a ++ decF b ++ padW)).take 6)`

(`decF` reads 18 limbs as 6 words `l0 + 2^21·l1 + 2^42·l2`; `limbsF` writes words as limbs).

* `shaNode_sha384`: on canonical digests (`limbsF` of six 64-bit words) `shaNode` is SHA-384 of the
  96 bytes `left48 ‖ right48`; `shaNode_nodeH`: it is lane B's `nodeH compressW` on `Dig`.
* `comp_in_chip`: every bus-103 receive of a counted `comp` block is a chip message (table-generic).
* `mpath_row_sha`: on an active MPATH row (and, for the new path, `ro = 0`) the children `selL`,
  `selR` are canonical 6-word digests `dl`, `dr` and the parent `po` (`pn`) is
  `shaNode selL selR`, whose bytes are `sha384 (bytes dl ++ bytes dr)`.
* `mpath_block_sha`: `mpath_block` with `node := shaNode` and no hash hypothesis: the old root `ri` is
  the SHA-384 Merkle fold of the old leaf `co(r0)` under the siblings and bits, the new root `rt`
  that of the new leaf (or `rt = ri` when read-only).
* `memRoot_in_sha`: with `rch_chain` and `leaf_link`, `memRoot_in` is the SHA-384 Merkle fold of the
  first touched block's old leaf, which is MEMB's in-hash `hoI` of that block's padding row.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-! ## Limb codecs -/

/-- Read 18 limbs as 6 words. -/
def decF (a : List F) : List Nat :=
  (List.range 6).map fun k =>
    (a.getD (3 * k) 0).toNat + 2 ^ 21 * (a.getD (3 * k + 1) 0).toNat + 2 ^ 42 * (a.getD (3 * k + 2) 0).toNat

/-- **The SHA-384 node on 18-limb digests.** -/
def shaNode (a b : List F) : List F :=
  limbsF ((compressW NearSpecV3.E2E.Bnd.IV384 (decF a ++ decF b ++ padW)).take 6)

theorem limbsF_getD : ∀ (d : List Nat) (k l : Nat), l < 3 → k < d.length →
    (limbsF d).getD (3 * k + l) 0 = (wF (d.getD k 0)).getD l 0
  | [], _, _, _, h => absurd h (by simp)
  | w :: d, 0, l, hl, _ => by
    simp only [limbsF, List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero,
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [wF_length]; exact hl)]
    rfl
  | w :: d, k + 1, l, hl, hk => by
    have ih := limbsF_getD d k l hl (by simp at hk; omega)
    simp only [limbsF, List.flatMap_cons, List.getD_cons_succ, List.getD_eq_getElem?_getD] at ih ⊢
    rw [List.getElem?_append_right (by rw [wF_length]; omega), wF_length,
      show 3 * (k + 1) + l - 3 = 3 * k + l by omega]
    exact ih

theorem limbsF_length (d : List Nat) : (limbsF d).length = 3 * d.length := by
  induction d with
  | nil => rfl
  | cons w d ih => simp only [limbsF, List.flatMap_cons, List.length_append, wF_length] at ih ⊢; rw [ih]; simp; omega

theorem decF_limbsF {d : List Nat} (hl : d.length = 6) (hw : W64 d) : decF (limbsF d) = d := by
  have hP := P_val
  apply List.ext_getElem? ; intro k
  by_cases hk : k < 6
  · simp only [decF, List.getElem?_map, List.getElem?_range hk, Option.map_some]
    have g0 : (limbsF d).getD (3 * k) 0 = (wF (d.getD k 0)).getD 0 0 := by
      simpa using limbsF_getD d k 0 (by decide) (by omega)
    rw [g0, limbsF_getD d k 1 (by decide) (by omega), limbsF_getD d k 2 (by decide) (by omega)]
    have hdk : d.getD k 0 < 2 ^ 64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact hw _ (List.getElem_mem _)
    simp only [wF, StateM5a.wlimbs, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega)]
    rw [List.getElem?_eq_getElem (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hdk ⊢
    simp only [Option.getD_some, Option.some.injEq]
    omega
  · rw [List.getElem?_eq_none (by simp [decF]; omega), List.getElem?_eq_none (by omega)]

theorem shaNode_limbs {dl dr : List Nat} (hl : dl.length = 6) (hr : dr.length = 6) (wl : W64 dl) (wr : W64 dr) :
    shaNode (limbsF dl) (limbsF dr) =
      limbsF ((compressW NearSpecV3.E2E.Bnd.IV384 (dl ++ dr ++ padW)).take 6) := by
  rw [shaNode, decF_limbsF hl wl, decF_limbsF hr wr]

/-- **`shaNode` is SHA-384 of `left48 ‖ right48`** on canonical digests: its output is the limbs of
the six words whose bytes are `sha384 (bytes dl ++ bytes dr)`. -/
theorem shaNode_sha384 {dl dr : List Nat} (hl : dl.length = 6) (hr : dr.length = 6) (wl : W64 dl) (wr : W64 dr) :
    ∃ dout : List Nat, dout.length = 6 ∧ W64 dout ∧ shaNode (limbsF dl) (limbsF dr) = limbsF dout ∧
      wbytes dout = NearSpecV3.E2E.Bnd.sha384 (wbytes dl ++ wbytes dr) := by
  have hco := compressW_ok NearSpecV3.E2E.Bnd.IV384 (dl ++ dr ++ padW)
  refine ⟨_, by rw [List.length_take, hco.1]; rfl, fun w hw => hco.2 w (List.mem_of_mem_take hw), shaNode_limbs hl hr wl wr, ?_⟩
  rw [← wbytes_append, sha384_node dl dr hl hr]

/-- `shaNode` is lane B's `nodeH compressW` on `Dig`. -/
theorem shaNode_nodeH (a b : Dig) : shaNode (limbsF a.1) (limbsF b.1) = limbsF (nodeH compressW a b).1 := by
  rw [shaNode_limbs a.2.1 b.2.1 a.2.2 b.2.2, nodeH,
    take6_eq_digest6 (compressW_ok _ _).1 (compressW_ok _ _).2]
  rfl

/-! ## A counted `comp` block on a row -/

theorem comp_in_chip {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hC : ChipIf compress (wasmBaseSegAir nloc ngl) pub tr chip)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) {r : Nat} (hr : r < tr.height t)
    {cidE cnt : Expr} {ws : List W3} (hsub : ∀ i ∈ comp cidE ws cnt, i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hcnt : (cnt.eval (tr.row pub t r)).toNat = 1) :
    ∀ m, m < 16 → (cidE.eval (tr.row pub t r) :: ((m : Nat) : F) ::
      ((ws.getD (2 * m) zeroW).map (·.eval (tr.row pub t r)) ++ (ws.getD (2 * m + 1) zeroW).map (·.eval (tr.row pub t r))))
        ∈ chip.map ifF := by
  intro m hm
  have hi := hsub _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)
  have hocc := occ_of_inter ht hr hi hcnt
  have := if_recv_mem H hC hocc rfl rfl
  simpa [List.map_append] using this

/-! ## MPATH rows -/

/-- Field triples `(g(3k), g(3k+1), g(3k+2))`, `k < n`, flatten to `(range (3n)).map g`. -/
theorem flat_triples : ∀ (d : List Nat) (g : Nat → F),
    (∀ k, k < d.length → (List.range 3).map (fun l => g (3 * k + l)) = wF (d.getD k 0)) →
    (List.range (3 * d.length)).map g = limbsF d
  | [], _, _ => rfl
  | w :: d, g, h => by
    have h0 := h 0 (by simp)
    have ih := flat_triples d (fun i => g (3 + i)) (fun k hk => by
      have := h (k + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rw [← this]; apply List.map_congr_left; intro l _; congr 1; omega)
    simp only [List.length_cons, show 3 * (d.length + 1) = 3 + 3 * d.length by omega, List.range_add,
      List.map_append, List.map_map]
    simp only [limbsF, List.flatMap_cons] at ih ⊢
    rw [← ih]
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at h0
    rw [h0]; rfl

/-- The 32 words MPATH's `comp` sends for the path whose current digest starts at column `cur`
(`12` old, `30` new) and parent at `po` (`66`/`84`), extra at `xo` (`102`/`108`). -/
def mpW (tr : Trace) (r cur po xo k : Nat) : List F :=
  if k < 8 then wF (Seg.IV384.getD k 0)
  else if k < 14 then (List.range 3).map fun l =>
    mc tr r 3 * mc tr r (48 + 3 * (k - 8) + l) + (1 - mc tr r 3) * mc tr r (cur + 3 * (k - 8) + l)
  else if k < 20 then (List.range 3).map fun l =>
    mc tr r 3 * mc tr r (cur + 3 * (k - 14) + l) + (1 - mc tr r 3) * mc tr r (48 + 3 * (k - 14) + l)
  else if k < 24 then wF (padW.getD (k - 20) 0)
  else if k < 30 then (List.range 3).map fun l => mc tr r (po + 3 * (k - 24) + l)
  else (List.range 3).map fun l => mc tr r (xo + 3 * (k - 30) + l)

theorem mp_wsO_eval (tr : Trace) (pub : List F) (r : Nat) :
    ∀ k, k < 32 → ((Mpath.ivW ++ Mpath.nodeBlock "co" ++ wordsAt Mpath.c "po" 6 ++ wordsAt Mpath.c "xo" 2).getD k zeroW).map
      (·.eval (tr.row pub 20 r)) = mpW tr r 12 66 102 k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | _ + 32, h => absurd h (by omega)

theorem mp_wsN_eval (tr : Trace) (pub : List F) (r : Nat) :
    ∀ k, k < 32 → ((Mpath.ivW ++ Mpath.nodeBlock "cn" ++ wordsAt Mpath.c "pn" 6 ++ wordsAt Mpath.c "xn" 2).getD k zeroW).map
      (·.eval (tr.row pub 20 r)) = mpW tr r 30 84 108 k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | _ + 32, h => absurd h (by omega)

theorem mpath_compO_sub : ∀ i ∈ comp (Mpath.c "cidO") (Mpath.ivW ++ Mpath.nodeBlock "co" ++ wordsAt Mpath.c "po" 6 ++
    wordsAt Mpath.c "xo" 2) (Mpath.c "act"), i ∈ Mpath.table.inters := by
  intro i hi
  simp only [Mpath.table, Mpath.inters, List.mem_append]
  left; right; exact hi

theorem mpath_compN_sub : ∀ i ∈ comp (Mpath.c "cidN") (Mpath.ivW ++ Mpath.nodeBlock "cn" ++ wordsAt Mpath.c "pn" 6 ++
    wordsAt Mpath.c "xn" 2) (Mpath.c "act" * (1 - Mpath.c "ro")), i ∈ Mpath.table.inters := by
  intro i hi
  simp only [Mpath.table, Mpath.inters, List.mem_append]
  right; exact hi

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} {chip : List IfMsg}
  (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
include H hC

omit H in
/-- One path of an MPATH row whose `comp` is counted: generic in the column bases. -/
theorem mpath_path_sha {r cur po xo : Nat} {cid : F}
    (hrecv : ∀ m, m < 16 → cid ::
      ((m : Nat) : F) :: (mpW tr r cur po xo (2 * m) ++ mpW tr r cur po xo (2 * m + 1)) ∈ chip.map ifF) :
    ∃ dl dr dout : List Nat, dl.length = 6 ∧ dr.length = 6 ∧ dout.length = 6 ∧ W64 dl ∧ W64 dr ∧ W64 dout ∧
      selL tr r cur = limbsF dl ∧ selR tr r cur = limbsF dr ∧ mdig tr r po = limbsF dout ∧
      dout = (compressW NearSpecV3.E2E.Bnd.IV384 (dl ++ dr ++ padW)).take 6 ∧
      wbytes dout = NearSpecV3.E2E.Bnd.sha384 (wbytes (dl ++ dr)) := by
  have hW3 : ∀ k, k < 32 → (mpW tr r cur po xo k).length = 3 := by
    intro k _; unfold mpW
    by_cases h1 : k < 8 <;> by_cases h2 : k < 14 <;> by_cases h3 : k < 20 <;> by_cases h4 : k < 24 <;>
      by_cases h5 : k < 30 <;> simp [h1, h2, h3, h4, h5, wF_length]
  obtain ⟨dl, dr, dout, l1, l2, l3, w1, w2, w3, e1, e2, e3, e4, e5⟩ :=
    consumer_node_sha384 hC.contract hC.cidLt hW3
      (fun k hk => by simp [mpW, hk]; rfl)
      (fun k hk => by simp [mpW, show ¬ 20 + k < 8 by omega, show ¬ 20 + k < 14 by omega,
        show ¬ 20 + k < 20 by omega, show 20 + k < 24 by omega])
      hrecv
  refine ⟨dl, dr, dout, l1, l2, l3, w1, w2, w3, ?_, ?_, ?_, e4, e5⟩
  · have hf := flat_triples dl (fun i => mc tr r 3 * mc tr r (48 + i) + (1 - mc tr r 3) * mc tr r (cur + i)) (fun k hk => by
      rw [l1] at hk
      rw [← e1 k hk]
      simp only [mpW, show ¬ 8 + k < 8 by omega, show 8 + k < 14 by omega, ite_false, ite_true,
        show 8 + k - 8 = k by omega]
      apply List.map_congr_left; intro l _; simp only [Nat.add_assoc])
    rw [l1] at hf; exact hf
  · have hf := flat_triples dr (fun i => mc tr r 3 * mc tr r (cur + i) + (1 - mc tr r 3) * mc tr r (48 + i)) (fun k hk => by
      rw [l2] at hk
      rw [← e2 k hk]
      simp only [mpW, show ¬ 14 + k < 8 by omega, show ¬ 14 + k < 14 by omega, show 14 + k < 20 by omega,
        ite_false, ite_true, show 14 + k - 14 = k by omega]
      apply List.map_congr_left; intro l _; simp only [Nat.add_assoc])
    rw [l2] at hf; exact hf
  · have hf := flat_triples dout (fun i => mc tr r (po + i)) (fun k hk => by
      rw [l3] at hk
      rw [← e3 k hk]
      simp only [mpW, show ¬ 24 + k < 8 by omega, show ¬ 24 + k < 14 by omega, show ¬ 24 + k < 20 by omega,
        show ¬ 24 + k < 24 by omega, show 24 + k < 30 by omega, ite_false, ite_true, show 24 + k - 24 = k by omega]
      apply List.map_congr_left; intro l _; simp only [Nat.add_assoc])
    rw [l3] at hf; exact hf

omit H hC in
theorem mp_cnt_one {r : Nat} (e : Expr) (h : e.eval (tr.row pub 20 r) = 1) : (e.eval (tr.row pub 20 r)).toNat = 1 := by
  rw [h]; decide

/-- **An active MPATH row's old parent is the SHA-384 node of its children.** -/
theorem mpath_row_old {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) :
    ∃ dl dr dout : List Nat, dl.length = 6 ∧ dr.length = 6 ∧ dout.length = 6 ∧ W64 dl ∧ W64 dr ∧ W64 dout ∧
      selL tr r 12 = limbsF dl ∧ selR tr r 12 = limbsF dr ∧ mdig tr r 66 = limbsF dout ∧
      dout = (compressW NearSpecV3.E2E.Bnd.IV384 (dl ++ dr ++ padW)).take 6 ∧
      wbytes dout = NearSpecV3.E2E.Bnd.sha384 (wbytes (dl ++ dr)) := by
  have ht : 20 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hin := comp_in_chip H hC ht hr (fun i hi => by rw [seg_t20]; exact mpath_compO_sub i hi)
    (mp_cnt_one (Mpath.c "act") (by rw [← ha]; rfl))
  refine mpath_path_sha hC (cid := (Mpath.c "cidO").eval (tr.row pub 20 r)) (xo := 102) (fun m hm => ?_)
  have := hin m hm
  rwa [mp_wsO_eval tr pub r (2 * m) (by omega), mp_wsO_eval tr pub r (2 * m + 1) (by omega)] at this

/-- **An active, writable MPATH row's new parent is the SHA-384 node of its children.** -/
theorem mpath_row_new {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) (hro : mc tr r 4 = 0) :
    ∃ dl dr dout : List Nat, dl.length = 6 ∧ dr.length = 6 ∧ dout.length = 6 ∧ W64 dl ∧ W64 dr ∧ W64 dout ∧
      selL tr r 30 = limbsF dl ∧ selR tr r 30 = limbsF dr ∧ mdig tr r 84 = limbsF dout ∧
      dout = (compressW NearSpecV3.E2E.Bnd.IV384 (dl ++ dr ++ padW)).take 6 ∧
      wbytes dout = NearSpecV3.E2E.Bnd.sha384 (wbytes (dl ++ dr)) := by
  have ht : 20 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hin := comp_in_chip H hC ht hr (fun i hi => by rw [seg_t20]; exact mpath_compN_sub i hi)
    (mp_cnt_one (Mpath.c "act" * (1 - Mpath.c "ro")) (by
      show mc tr r 0 * (1 - mc tr r 4) = 1
      rw [ha, hro]; decide))
  refine mpath_path_sha hC (cid := (Mpath.c "cidN").eval (tr.row pub 20 r)) (xo := 108) (fun m hm => ?_)
  have := hin m hm
  rwa [mp_wsN_eval tr pub r (2 * m) (by omega), mp_wsN_eval tr pub r (2 * m + 1) (by omega)] at this

theorem mpath_chipO {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) :
    mdig tr r 66 = shaNode (selL tr r 12) (selR tr r 12) := by
  obtain ⟨dl, dr, dout, l1, l2, -, w1, w2, -, e1, e2, e3, e4, -⟩ := mpath_row_old H hC hr ha
  rw [e1, e2, e3, shaNode_limbs l1 l2 w1 w2, e4]

theorem mpath_chipN {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) (hro : mc tr r 4 = 0) :
    mdig tr r 84 = shaNode (selL tr r 30) (selR tr r 30) := by
  obtain ⟨dl, dr, dout, l1, l2, -, w1, w2, -, e1, e2, e3, e4, -⟩ := mpath_row_new H hC hr ha hro
  rw [e1, e2, e3, shaNode_limbs l1 l2 w1 w2, e4]

omit hC in
/-- Every row of a block is active, and `ro` is constant on it. -/
theorem mp_block_act {r0 n : Nat} (hh : r0 + n ≤ tr.height 20) (hact : mc tr r0 0 = 1)
    (hmid : ∀ l, l + 1 < n → mc tr (r0 + l) 2 = 0) :
    ∀ l, l < n → mc tr (r0 + l) 0 = 1 ∧ mc tr (r0 + l) 4 = mc tr r0 4 := by
  intro l
  induction l with
  | zero => intro _; exact ⟨hact, rfl⟩
  | succ l ih =>
    intro hl
    obtain ⟨a, b⟩ := ih (by omega)
    have := mp_next H (show r0 + l + 1 < tr.height 20 by omega) a (hmid l hl)
    exact ⟨this.1, this.2.2.2.2.1.trans b⟩

/-- **`mpath_block` with the real hash.**  For one block's rows `r0 … r0 + n − 1` of MPATH, under the
chip hypothesis alone: the old root `ri` is the SHA-384 Merkle fold (`mfold shaNode`) of the old leaf
`co(r0)` under the siblings and bits, the new root `rt` that of the new leaf `cn(r0)` (or `rt = ri`
when read-only), `blk = Σ bit_l·2^l`, `n − 1 = depth − 1`, and `kb`, `ro` constant. -/
theorem mpath_block_sha {r0 n : Nat} (hn : 0 < n)
    (hh : r0 + n ≤ tr.height 20) (hact : mc tr r0 0 = 1) (hbot : mc tr r0 1 = 1)
    (hmid : ∀ l, l + 1 < n → mc tr (r0 + l) 2 = 0) (htop : mc tr (r0 + (n - 1)) 2 = 1) :
    mdig tr (r0 + (n - 1)) 114 =
      mfold shaNode (mdig tr r0 12) ((List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3)) ∧
    (mc tr r0 4 = 0 → mdig tr (r0 + (n - 1)) 132 =
      mfold shaNode (mdig tr r0 30) ((List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3))) ∧
    (mc tr r0 4 = 1 → mdig tr (r0 + (n - 1)) 132 = mdig tr (r0 + (n - 1)) 114) ∧
    mc tr r0 5 = ((List.range n).map fun l => mc tr (r0 + l) 3 * ((2 ^ l : Nat) : F)).foldr (· + ·) 0 ∧
    (((n - 1 : Nat) : F) = pub.getD pubDepth 0 - 1) ∧
    mc tr (r0 + (n - 1)) 9 = mc tr r0 9 ∧ mc tr (r0 + (n - 1)) 4 = mc tr r0 4 := by
  have hb := mp_block_act H hh hact hmid
  exact mpath_block H shaNode hn hh hact hbot hmid htop
    (fun l hl => mpath_chipO H hC (by omega) (hb l hl).1)
    (fun h0 l hl => mpath_chipN H hC (by omega) (hb l hl).1 ((hb l hl).2.trans h0))

/-- **`memRoot_in` is the SHA-384 Merkle fold of the first touched block's old leaf**, which is the
in-hash `hoI` (columns 486…503) of a MEMB padding row (`p8 = 1`) of the same block number. -/
theorem memRoot_in_sha {r0 n : Nat} (hn : 0 < n)
    (hh : r0 + n ≤ tr.height 20) (hact : mc tr r0 0 = 1) (hbot : mc tr r0 1 = 1)
    (hmid : ∀ l, l + 1 < n → mc tr (r0 + l) 2 = 0) (htop : mc tr (r0 + (n - 1)) 2 = 1)
    (hfirst : topCount tr (r0 + (n - 1)) = 0) :
    ∃ r', r' < tr.height 19 ∧ bc tr r' 9 = 1 ∧ bc tr r' 10 = mc tr r0 5 ∧ bc tr r' 11 = mc tr r0 4 ∧
      pubDig pub pubMemIn =
        mfold shaNode (bdig tr r' 486) ((List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3)) := by
  obtain ⟨r', hr', hp8, he⟩ := leaf_link H (show r0 < tr.height 20 by omega) hbot
  have hl : bdig tr r' 486 = mdig tr r0 12 ∧ bc tr r' 10 = mc tr r0 5 ∧ bc tr r' 11 = mc tr r0 4 := by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨a, b, c⟩ := he
    exact ⟨(List.append_inj c (by simp [bdig, mdig])).1, a, b⟩
  refine ⟨r', hr', hp8, hl.2.1, hl.2.2, ?_⟩
  rw [hl.1, ← (mpath_block_sha H hC hn hh hact hbot hmid htop).1]
  exact ((rch_chain H).1 _ (by omega) htop hfirst).symm

/-- **`memRoot_out` is the SHA-384 Merkle fold of the last touched block's new leaf** (writable
block), the out-hash `hoO` (columns 534…551) of its MEMB padding row. -/
theorem memRoot_out_sha {r0 n : Nat} (hn : 0 < n)
    (hh : r0 + n ≤ tr.height 20) (hact : mc tr r0 0 = 1) (hbot : mc tr r0 1 = 1)
    (hmid : ∀ l, l + 1 < n → mc tr (r0 + l) 2 = 0) (htop : mc tr (r0 + (n - 1)) 2 = 1)
    (hlast : topCount tr (r0 + (n - 1)) + 1 = topCount tr (tr.height 20)) (hro : mc tr r0 4 = 0) :
    ∃ r', r' < tr.height 19 ∧ bc tr r' 9 = 1 ∧ bc tr r' 10 = mc tr r0 5 ∧ bc tr r' 11 = mc tr r0 4 ∧
      pubDig pub pubMemOut =
        mfold shaNode (bdig tr r' 534) ((List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3)) := by
  obtain ⟨r', hr', hp8, he⟩ := leaf_link H (show r0 < tr.height 20 by omega) hbot
  have hl : bdig tr r' 534 = mdig tr r0 30 ∧ bc tr r' 10 = mc tr r0 5 ∧ bc tr r' 11 = mc tr r0 4 := by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨a, b, c⟩ := he
    exact ⟨(List.append_inj c (by simp [bdig, mdig])).2, a, b⟩
  refine ⟨r', hr', hp8, hl.2.1, hl.2.2, ?_⟩
  rw [hl.1, ← (mpath_block_sha H hC hn hh hact hbot hmid htop).2.1 hro]
  exact ((rch_chain H).2.2.1 _ (by omega) htop hlast).1

end
end SegSha

#print axioms SegSha.shaNode_sha384
#print axioms SegSha.shaNode_nodeH
#print axioms SegSha.mpath_row_old
#print axioms SegSha.mpath_row_new
#print axioms SegSha.mpath_block_sha
#print axioms SegSha.memRoot_in_sha
#print axioms SegSha.memRoot_out_sha

end WasmBase
