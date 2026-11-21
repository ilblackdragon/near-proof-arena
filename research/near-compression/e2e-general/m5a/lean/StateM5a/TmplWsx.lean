import StateM5a.TmplSeg

/-!
# StateM5a.TmplWsx — B-T1b: the `WSX` bus step and the segment template at depth 24

* **`wsx_ext`** (any AIR, any table index holding a `WSX` table): from `Holds`, the `FieldWsx`
  constraint facts and the chip contract on `IF384` (each active row's three compressions
  `zo = H(z, z)`, `ao = H(a, z)`, `bo = H(b, z)`, `node_comp`), the row-0 zero digest is the
  constant `zD D` (`Z_D`, `Tmpl.zeroLimbs`) and the two public depth-24 roots are the row-0 roots
  extended by `24 − D` zero-sibling levels: `extUp H (zD D) 0 (24 − D) a₀ = pubDig pub PUB_WSA`,
  the same for `b₀` and `PUB_WSB`.  Instances: `wsx_ext_seg` (`m5tSeg`, table 7) and
  `wsx_ext_if` (`m5tIF`, table 9).
* **`seg_rin_rout`** — the segment template at lane E's committed depth: for every depth-`D`
  working set whose zero-padded depth-24 root (`extUp`, `Merkle.root_pad`) is the public `R_in`,
  the working set after the segment's writes has the public `R_out` as its depth-24 root
  (`ext_inj` under `NodeCR`), with the touched-leaf and memory-chain facts of `m5tSeg_ws`.
-/

namespace StateM5a.TmplWsx

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsBus StateM5a.WsRaw StateM5a.Merkle
open StateM5a.TmplSeg

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The constant `Z_D` as a digest (the `WSX` row-0 `z` limbs, `FieldWsx.wsx_first_z`). -/
def zD (D : Nat) : Dig := decDig ((List.range 18).map fun j => (zeroLimbs D).getD j 0 % P)

/-- A depth-24 root public value (18 limbs from `base`) as a digest. -/
def pubDig (pub : List Fp) (base : Nat) : Dig := decDig ((List.range 18).map fun j => (pub.getD (base + j) 0).toNat)

/-- The INTAKE + FINAL template with the tables after it. -/
def ifAir (D : Nat) (extra : List Table) (nb np : Nat) : Air :=
  { tables := (m5tIF D).tables ++ extra, numBuses := nb, numPub := np }

theorem rowDig_rows {tr : Trace Fp} {t r r' : Nat} {pub : List Fp} {f g : Nat → Expr}
    (h : ∀ j < 18, ev tr t r' pub (f j) = ev tr t r pub (g j)) : rowDig tr t r' pub f = rowDig tr t r pub g := by
  unfold rowDig
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

section Wsx
variable {D : Nat} {A : Air} {tr : Trace Fp} {pub : List Fp} {compress : List Nat → List Nat → List Nat}
  {t : Nat} {T : Table}
  (hH : Holds A pub tr) (ht : t < A.tables.length) (hT : A.tables[t]! = T)
  (hTc : T.constraints = Wsx.constraints D) (hsub : ∀ i ∈ Wsx.comps, i ∈ T.interactions)
  (hcomp : CompressOK compress) (hC : Sha512IfContract compress ((busList A tr pub B_IF384 true).map decIf))
include hH ht hT hTc hsub hcomp hC

/-- **The `WSX` bus step.** -/
theorem wsx_ext (hml : T.maxLog ≤ 20) (hD : D ≤ 23) :
    rowDig tr t 0 pub (fun j => Wsx.c "z" j) = zD D ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) (rowDig tr t 0 pub (fun j => Wsx.c "a" j)) = pubDig pub PUB_WSA ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) (rowDig tr t 0 pub (fun j => Wsx.c "b" j)) = pubDig pub PUB_WSB := by
  have hc : ∀ r, r < tr.height t → ∀ e ∈ T.constraints, e.eval tr t r pub = 0 := by
    intro r hr e he
    have h := hH.constr t ht r hr e
    rw [← getElem!_pos _ t ht, hT] at h
    exact h he
  have hlog : tr.log t ≤ 20 := by
    have h := (hH.logBound t ht).2
    rw [← getElem!_pos _ t ht, hT] at h
    omega
  have hperm := holds_perm hH B_IF384
  obtain ⟨hlt, hlay⟩ := FieldWsx.wsx_layout hTc hc hD hlog
  let H := nodeH compress
  let dg := fun (s : String) (r : Nat) => rowDig tr t r pub (fun j => Wsx.c s j)
  -- the three compressions of an active row
  have hrow : ∀ r, r ≤ 23 - D →
      dg "zo" r = H (dg "z" r) (dg "z" r) ∧ dg "ao" r = H (dg "a" r) (dg "z" r) ∧
      dg "bo" r = H (dg "b" r) (dg "z" r) := by
    intro r hr
    have hr' : r < tr.height t := by omega
    have hA : (Wsx.c "act").eval tr t r pub = 1 := ev_one_eval (((hlay r hr').1).2 hr)
    have ins : ∀ L : List Interaction, (∀ i ∈ L, i ∈ Wsx.comps) → ∀ i ∈ L, i ∈ (A.tables[t]!).interactions :=
      fun L hL i hi => by rw [hT]; exact hsub i (hL i hi)
    refine ⟨node_comp (cid := Wsx.c "cz") (ox := fun j => Wsx.c "zx" j) hcomp hC hperm ht hr' hA (ins _ fun i hi => ?_),
      node_comp (cid := Wsx.c "ca") (ox := fun j => Wsx.c "ax" j) hcomp hC hperm ht hr' hA (ins _ fun i hi => ?_),
      node_comp (cid := Wsx.c "cb") (ox := fun j => Wsx.c "bx" j) hcomp hC hperm ht hr' hA (ins _ fun i hi => ?_)⟩
    · unfold Wsx.comps; exact List.mem_append_left _ (List.mem_append_left _ hi)
    · unfold Wsx.comps; exact List.mem_append_left _ (List.mem_append_right _ hi)
    · unfold Wsx.comps; exact List.mem_append_right _ hi
  -- the links between consecutive active rows
  have hlink : ∀ r, r + 1 ≤ 23 - D →
      dg "z" (r + 1) = dg "zo" r ∧ dg "a" (r + 1) = dg "ao" r ∧ dg "b" (r + 1) = dg "bo" r := by
    intro r hr
    have hr1 : r + 1 < tr.height t := by omega
    have h1 : ev tr t (r + 1) pub (Wsx.c "act") = 1 := ((hlay (r + 1) hr1).1).2 hr
    exact ⟨rowDig_rows fun j hj => (FieldWsx.wsx_link hTc hc hj hr1 h1).1,
      rowDig_rows fun j hj => (FieldWsx.wsx_link hTc hc hj hr1 h1).2.1,
      rowDig_rows fun j hj => (FieldWsx.wsx_link hTc hc hj hr1 h1).2.2⟩
  have hz0 : dg "z" 0 = zD D := by
    show rowDig tr t 0 pub (fun j => Wsx.c "z" j) = zD D
    unfold rowDig zD
    congr 1
    apply List.map_congr_left
    intro j hj
    exact FieldWsx.wsx_first_z hTc hc (List.mem_range.1 hj)
  -- the chain
  have chain : ∀ k, k ≤ 23 - D → dg "z" k = zd H (zD D) k ∧
      dg "a" k = extUp H (zD D) 0 k (dg "a" 0) ∧ dg "b" k = extUp H (zD D) 0 k (dg "b" 0) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hz0, rfl, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      obtain ⟨l1, l2, l3⟩ := hlink k hk
      obtain ⟨c1, c2, c3⟩ := hrow k (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [l1, c1, i1]; rfl
      · rw [l2, c2, i2, i1]; simp only [extUp, Nat.zero_add]
      · rw [l3, c3, i3, i1]; simp only [extUp, Nat.zero_add]
  -- the top row
  have hT0 : 23 - D < tr.height t := hlt
  have htop : ev tr t (23 - D) pub (Wsx.c "top") = 1 := (((hlay _ hT0).2 (Nat.le_refl _)).2).2 rfl
  obtain ⟨_, c2, c3⟩ := hrow (23 - D) (Nat.le_refl _)
  obtain ⟨i1, i2, i3⟩ := chain (23 - D) (Nat.le_refl _)
  have e24 : 24 - D = (23 - D) + 1 := by omega
  have pA : dg "ao" (23 - D) = pubDig pub PUB_WSA := by
    show rowDig tr t (23 - D) pub (fun j => Wsx.c "ao" j) = _
    unfold rowDig pubDig
    congr 1
    apply List.map_congr_left
    intro j hj
    exact (FieldWsx.wsx_top_pub hTc hc (List.mem_range.1 hj) hT0 htop).1
  have pB : dg "bo" (23 - D) = pubDig pub PUB_WSB := by
    show rowDig tr t (23 - D) pub (fun j => Wsx.c "bo" j) = _
    unfold rowDig pubDig
    congr 1
    apply List.map_congr_left
    intro j hj
    exact (FieldWsx.wsx_top_pub hTc hc (List.mem_range.1 hj) hT0 htop).2
  refine ⟨hz0, ?_, ?_⟩
  · rw [e24, ← pA, c2, i2, i1]; simp only [extUp, Nat.zero_add]; rfl
  · rw [e24, ← pB, c3, i3, i1]; simp only [extUp, Nat.zero_add]; rfl

end Wsx

/-! ## Instances: the two templates -/

section Inst
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}

theorem if_len : (ifAir D extra nb np).tables.length = 10 + extra.length := by
  simp [ifAir, m5tIF]; omega

theorem if_wsx : (ifAir D extra nb np).tables[9]! = Wsx.tableIF D := by
  simp only [ifAir]
  rw [getElem!_pos _ 9 (by simp [m5tIF])]
  simp [m5tIF]

/-- `WSX` of the segment template (table 7): `R_in`, `R_out` are the extended row-0 roots. -/
theorem wsx_ext_seg (hH : Holds (segAir D extra nb np) pub tr) (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (segAir D extra nb np) tr pub B_IF384 true).map decIf)) (hD : D ≤ 23) :
    rowDig tr 7 0 pub (fun j => Wsx.c "z" j) = zD D ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) (rowDig tr 7 0 pub (fun j => Wsx.c "a" j)) = pubDig pub PUB_WSA ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) (rowDig tr 7 0 pub (fun j => Wsx.c "b" j)) = pubDig pub PUB_WSB :=
  wsx_ext hH (by rw [seg_len]; omega) seg_wsx rfl (fun i hi => List.mem_append_right _ hi) hcomp hC (by show (5 : Nat) ≤ 20; decide) hD

/-- `WSX` of the INTAKE + FINAL template (table 9): `R_0`, `R_n` are the extended row-0 roots. -/
theorem wsx_ext_if (hH : Holds (ifAir D extra nb np) pub tr) (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (ifAir D extra nb np) tr pub B_IF384 true).map decIf)) (hD : D ≤ 23) :
    rowDig tr 9 0 pub (fun j => Wsx.c "z" j) = zD D ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) (rowDig tr 9 0 pub (fun j => Wsx.c "a" j)) = pubDig pub PUB_WSA ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) (rowDig tr 9 0 pub (fun j => Wsx.c "b" j)) = pubDig pub PUB_WSB :=
  wsx_ext hH (by rw [if_len]; omega) if_wsx rfl (fun i hi => List.mem_append_right _ hi) hcomp hC (by show (5 : Nat) ≤ 20; decide) hD

/-- **The segment template at depth 24** (`R_in → R_out`): every depth-`D` working set whose
zero-padded depth-24 root is the public `R_in` (`PUB_WSA`) becomes, after the segment's writes
(`wsAt`), a working set whose depth-24 root is the public `R_out` (`PUB_WSB`); the touched-leaf and
memory-chain facts are `m5tSeg_ws`'s. -/
theorem seg_rin_rout (hH : Holds (segAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (segAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR compress) {ws0 : List Dig} (hlen0 : ws0.length = 2 ^ D)
    {r : Dig} (hr : root (nodeH compress) D ws0 = some r)
    (hin : extUp (nodeH compress) (zD D) 0 (24 - D) r = pubDig pub PUB_WSA) :
    ∃ r', root (nodeH compress) D (WsSeg.wsAt (wsl (trS tr) pub) ws0 (ev tr 7 0 pub (Wsx.c "sb"))) = some r' ∧
      extUp (nodeH compress) (zD D) 0 (24 - D) r' = pubDig pub PUB_WSB := by
  obtain ⟨-, ea, eb⟩ := wsx_ext_seg hH hcomp hC (by omega)
  have e : r = rowDig tr 7 0 pub (fun j => Wsx.c "a" j) := ext_inj (nodeH compress) hCR (zD D) 0 (24 - D) _ _ (hin.trans ea.symm)
  subst e
  exact ⟨_, (m5tSeg_ws hH hx hcomp hC hD1 hD hCR hlen0 hr).1, eb⟩

end Inst

end StateM5a.TmplWsx
