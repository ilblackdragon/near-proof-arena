import StateM5a.TmplWsx

/-!
# StateM5a.TmplIf — B-T1b: the INTAKE + FINAL template's working-set roots

In `m5tIF D` the `RCH` bus is used by `WSN` (table 6, the INTAKE tree sends `(0, r₀)`, the FINAL
tree receives `(nw, r_F)`) and by `WSX` (table 9: receives `(0, a₀)`, sends `(sb₀, b₀)`).

* `busList_if_rch` — only these two tables (the other IF tables do not use `RCH`, the extra tables
  by premise);
* `sb_one` — the pin `Tmpl.Wsx.sbPin` (`isFirst·(sb − 1)`, B-T1b) gives `sb₀ = 1`;
* **`rch_if`** — with the `WSN` root messages `[(0, r₀)]`, `[(nw, r_F)]` (one INTAKE and one FINAL
  top row: `WsDecode4.wsn_roots` for the M5a table list, the same tables at the same indices here),
  `RCH` balance has exactly one matching: `r₀ = a₀`, `r_F = b₀`, `nw = 1`.  (Before the pin a
  second matching existed — `nw = sb₀ = 0`, `r_F = r₀`, `a₀ = b₀` arbitrary — so the IF proof could
  publish `R_0 = R_n` = any root when its FINAL tree equals its INTAKE tree.)
* **`m5tIF_roots`** — with `wsx_ext_if`: the INTAKE tree's root extended to depth 24 is the public
  `R_0`, the FINAL tree's is the public `R_n`.
-/

namespace StateM5a.TmplIf

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsBus StateM5a.WsRaw StateM5a.Merkle
open StateM5a.TmplSeg StateM5a.TmplWsx

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem wsxI_rs : fl Wsx.interactionsIF B_RCH true = [snd B_RCH .isFirst (Wsx.c "sb" :: Wsx.vec "b" 18)] := by rfl
theorem wsxI_rr : fl Wsx.interactionsIF B_RCH false = [rcv B_RCH .isFirst (0 :: Wsx.vec "a" 18)] := by rfl

/-- **`RCH` in the IF template**: only `WSN` (6) and `WSX` (9). -/
theorem busList_if_rch {tr : Trace Fp} {pub : List Fp} (D : Nat) (extra : List Table) (nb np : Nat)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RCH) (s : Bool) :
    busList (ifAir D extra nb np) tr pub B_RCH s =
      tableBusList Wsn.interactions tr 6 pub B_RCH s ++ tableBusList Wsx.interactionsIF tr 9 pub B_RCH s := by
  have ext := busList_extend (m5tIF D) extra nb np tr pub B_RCH s (fun T hT i hi ⟨e, _⟩ => hx T hT i hi e)
  simp only [ifAir]
  rw [ext]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := nb_ws B_RCH (Or.inr (Or.inr rfl))
  simp only [busList, m5tIF, busList.go]
  rw [tbl_nil n1, tbl_nil n2, tbl_nil (is := Br.table.interactions) n3, tbl_nil (is := Sn.table.interactions) n4,
    tbl_nil n5, tbl_nil (is := (Wsb.table D).interactions) n6, tbl_nil n7, tbl_nil n8]
  simp only [Wsn.table, Wsx.tableIF, List.nil_append, List.append_nil, List.append_assoc]

section
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}

/-- The IF's outgoing root is at segment index 1 (`sbPin`). -/
theorem sb_one (hH : Holds (ifAir D extra nb np) pub tr) : ev tr 9 0 pub (Wsx.c "sb") = 1 := by
  have h0 : 0 < tr.height 9 := Nat.two_pow_pos _
  have h := hH.constr 9 (by rw [if_len]; omega) 0 h0 Wsx.sbPin
  rw [← getElem!_pos _ 9 (by rw [if_len]; omega), if_wsx] at h
  have e := h (List.mem_append_right _ (List.mem_singleton_self _))
  have g : ev tr 9 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
  have e' : ev tr 9 0 pub Wsx.sbPin = 0 := by unfold ev; rw [e]; rfl
  have := eq_of_sub (FieldWsx.gate g e')
  rw [this, ev_one]

/-- **`RCH` balance, decoded** (IF): `WSN`'s roots plus `WSX`'s `(1, b₀)` / `(0, a₀)`. -/
theorem rch_traffic_if (hH : Holds (ifAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RCH) :
    (s0 tr pub ++ [(1, rowDig tr 9 0 pub (fun j => Wsx.c "b" j))]).Perm
      (q0 tr pub ++ [(0, rowDig tr 9 0 pub (fun j => Wsx.c "a" j))]) := by
  have hp := (holds_perm hH B_RCH).map decR
  rw [busList_if_rch D extra nb np hx true, busList_if_rch D extra nb np hx false,
    tbl_one _ _ _ _ _ wsn_rs, tbl_one _ _ _ _ _ wsxI_rs, tbl_one _ _ _ _ _ wsn_rr, tbl_one _ _ _ _ _ wsxI_rr,
    selL_first, selL_first] at hp
  simp only [List.map_append, List.map_cons, List.map_nil] at hp
  rw [decR_wsx, decR_wsx, sb_one hH,
    show ev tr 9 0 pub (0 : Expr) = 0 from ev_const (tr := tr) (t := 9) (r := 0) (pub := pub) 0] at hp
  exact hp

/-- **The IF's `RCH` matching is unique**: the INTAKE root is `WSX`'s incoming `a₀`, the FINAL root
its outgoing `b₀`, and `WSN` closes at index 1. -/
theorem rch_if (hH : Holds (ifAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RCH) {r0 rF : Dig} {nw : Nat}
    (hs0 : s0 tr pub = [(0, r0)]) (hq0 : q0 tr pub = [(nw, rF)]) :
    r0 = rowDig tr 9 0 pub (fun j => Wsx.c "a" j) ∧ rF = rowDig tr 9 0 pub (fun j => Wsx.c "b" j) ∧ nw = 1 := by
  have hp := rch_traffic_if hH hx
  rw [hs0, hq0] at hp
  have m1 := hp.mem_iff.1 (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at m1
  rcases m1 with ⟨e1, e2⟩ | ⟨e1, -⟩
  · subst e1
    have m0 := hp.mem_iff.1 (List.mem_cons_self ..)
    simp only [List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at m0
    rcases m0 with ⟨e3, -⟩ | ⟨-, e4⟩
    · exact absurd e3 (by decide)
    · exact ⟨e4, e2.symm, rfl⟩
  · exact absurd e1 (by decide)

/-- **The IF template's two working-set roots at depth 24**: the INTAKE tree's root (`WSN` phase 0)
extended by `24 − D` zero-sibling levels is the public `R_0`, the FINAL tree's (`WSN` phase 1) is
the public `R_n`. -/
theorem m5tIF_roots (hH : Holds (ifAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RCH)
    {compress : List Nat → List Nat → List Nat} (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (ifAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hD : D ≤ 23) {r0 rF : Dig} {nw : Nat} (hs0 : s0 tr pub = [(0, r0)]) (hq0 : q0 tr pub = [(nw, rF)]) :
    extUp (nodeH compress) (zD D) 0 (24 - D) r0 = pubDig pub PUB_WSA ∧
    extUp (nodeH compress) (zD D) 0 (24 - D) rF = pubDig pub PUB_WSB := by
  obtain ⟨e0, eF, -⟩ := rch_if hH hx hs0 hq0
  obtain ⟨-, ea, eb⟩ := wsx_ext_if hH hcomp hC hD
  exact ⟨e0 ▸ ea, eF ▸ eb⟩

end

end StateM5a.TmplIf
