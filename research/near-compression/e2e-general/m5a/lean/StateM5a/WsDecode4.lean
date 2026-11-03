import StateM5a.WsDecode3
import StateM5a.WsTree

/-!
# StateM5a.WsDecode4 — the `WSN` tree build from `Holds`: `RCH(0) = root ws0`, `RCH(nw) = root wsF`

The `TREE` bus (`WSB` leaf sends `(ph, 0, i, dg)` on every row; `WSN` active rows receive both
children and send `(ph, lvl + 1, idx, o)` unless top) is decoded into the `PT` shape of `WsBus`
(phase as segment, `tl = tr = true`, old = new digest) and `WsTree` applies:

* `tree_traffic`: `TREE` balance of the decoded rows (raw positions; `WsRaw` removes the wrap);
* `wsn_ok`, `wsn_rowF`: the `WSN` row facts (`nodeH` from the chip contract, top position);
* `wsLeaves tr pub ph`: the `2^D` `WSB` leaf digests of phase `ph`, index by index (row `ph·2^D + i`,
  `WsLen.wsb_pos`; by `WsLen.wsb_leaves` the first `wsLen` are real entries, the rest zero);
* **`wsn_roots`**: the decoded `WSN` root messages are exactly `s0 = [(0, r0)]` and
  `q0 = [(nw, rF)]` with `root ws0 = r0`, `root wsF = rF` (`ws0 = wsLeaves 0`, `wsF = wsLeaves 1`):
  each phase has exactly one top row (`WsTree.tree_root`, counting from the leaves, which are one
  per `(ph, i)` by `FieldWsb.wsb_row_inj`);
* **`ws_decoded_final2`**: `WsDecode3.ws_decoded_final` with the `WSN` premises discharged.
-/

namespace StateM5a.WsDecode4

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsBus StateM5a.WsRaw StateM5a.Merkle
open StateM5a.WsTree

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The `TREE` interactions -/

def wsbT : List Expr := [Wsb.c "ph", 0, Wsb.c "i"] ++ Wsb.vec "dg" 18
def wsnL : List Expr := [Wsn.c "ph", Wsn.c "lvl", sm 2 (Wsn.c "idx")] ++ Wsn.vec "l" 18
def wsnR : List Expr := [Wsn.c "ph", Wsn.c "lvl", sm 2 (Wsn.c "idx") + 1] ++ Wsn.vec "r" 18
def wsnO : List Expr := [Wsn.c "ph", Wsn.c "lvl" + 1, Wsn.c "idx"] ++ Wsn.vec "o" 18

theorem wsb_ts : fl Wsb.interactions B_TREE true = [snd B_TREE 1 wsbT] := by rfl
theorem wsb_tr : fl Wsb.interactions B_TREE false = [] := by rfl
theorem wsn_tr : fl Wsn.interactions B_TREE false = [rcv B_TREE (Wsn.c "act") wsnL, rcv B_TREE (Wsn.c "act") wsnR] := by rfl
theorem wsn_ts : fl Wsn.interactions B_TREE true = [snd B_TREE (Wsn.c "act" - Wsn.c "top") wsnO] := by rfl

theorem nb_tree :
    noBus shaTable.interactions B_TREE = true ∧ noBus Key.table.interactions B_TREE = true ∧
    noBus Br.table.interactions B_TREE = true ∧ noBus Sn.table.interactions B_TREE = true ∧
    noBus Kcmp.table.interactions B_TREE = true ∧ noBus Wsa.table.interactions B_TREE = true ∧
    noBus Snc.table.interactions B_TREE = true ∧ noBus Rng.table.interactions B_TREE = true ∧
    noBus Wsl.table.interactions B_TREE = true ∧ noBus Wsp.interactions B_TREE = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem busList_tree {tr : Trace Fp} {pub : List Fp} (D : Nat) (extra : List Table) (nb np : Nat)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_TREE) (s : Bool) :
    busList (fullAir D extra nb np) tr pub B_TREE s =
      tableBusList Wsb.interactions tr 5 pub B_TREE s ++ tableBusList Wsn.interactions tr 6 pub B_TREE s := by
  have ext := busList_extend (m5aAir D) extra nb np tr pub B_TREE s (fun T hT i hi ⟨e, _⟩ => hx T hT i hi e)
  simp only [fullAir]
  rw [ext]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := nb_tree
  simp only [busList, m5aAir, busList.go]
  rw [tbl_nil n1, tbl_nil n2, tbl_nil (is := Br.table.interactions) n3, tbl_nil (is := Sn.table.interactions) n4,
    tbl_nil n5, tbl_nil (is := Wsa.table.interactions) n6, tbl_nil n7, tbl_nil n8,
    tbl_nil (is := Wsl.table.interactions) n9, tbl_nil (is := (Wsp.table D).interactions) n10]
  simp only [Wsb.table, Wsn.table, List.nil_append, List.append_nil, List.append_assoc]

/-! ## Decoded rows -/

def decT (m : List Fp) : PT Dig :=
  ⟨tn (m.getD 0 0), tn (m.getD 1 0), tn (m.getD 2 0), digOf ((m.drop 3).take 18), digOf ((m.drop 3).take 18)⟩

section Rows
variable (tr : Trace Fp) (pub : List Fp)

/-- A `WSB` row as a leaf message `(ph, i, dg)`. -/
def wsbLeaf (r : Nat) : WslRow Unit Unit Dig :=
  let d := rowDig tr 5 r pub (fun j => Wsb.c "dg" j)
  ⟨ev tr 5 r pub (Wsb.c "ph"), ev tr 5 r pub (Wsb.c "i"), (), (), (), 0, d, d⟩

/-- An active `WSN` row (both children always received; old = new). -/
def wsnRow (r : Nat) : WspF Dig :=
  let e := fun x => ev tr 6 r pub x
  let d := fun s => rowDig tr 6 r pub (fun j => Wsn.c s j)
  ⟨⟨e (Wsn.c "ph"), e (Wsn.c "lvl"), e (Wsn.c "idx"), decide (e (Wsn.c "top") = 1), true, true,
    d "l", d "l", d "r", d "r", d "o", d "o"⟩,
   e (Wsn.c "lvl" + 1), e (sm 2 (Wsn.c "idx")), e (sm 2 (Wsn.c "idx") + 1), (e (Wsn.c "ph") + 1) % P⟩

def wsbL : List (WslRow Unit Unit Dig) := actRows tr pub 5 1 (wsbLeaf tr pub)
/-- Active `WSN` row indices. -/
def wsnIx : List Nat := actRows tr pub 6 (Wsn.c "act") id
def wsnF : List (WspF Dig) := (wsnIx tr pub).map (wsnRow tr pub)

/-- **The `WSB` leaf digests of phase `ph`**: index `i` is row `ph·2^D + i`. -/
def lv (D : Nat) (ph i : Nat) : Dig := rowDig tr 5 (ph * 2 ^ D + i) pub (fun j => Wsb.c "dg" j)
def wsLeaves (D ph : Nat) : List Dig := slice (lv tr pub D) ph D 0

end Rows

theorem actRows_id {β : Type} {tr : Trace Fp} {pub : List Fp} {t : Nat} {g : Expr} (row : Nat → β) :
    actRows tr pub t g row = (actRows tr pub t g id).map row := by
  unfold actRows
  rw [List.map_filterMap]
  congr 1; funext r
  split <;> rfl

section Dec
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem dec_wsbT : decT (vals tr 5 r pub wsbT) = (wsbLeaf tr pub r).ptM := by
  simp only [decT, wsbT, Wsb.vec]; dsplit
  simp only [WslRow.ptM, wsbLeaf, PT.mk.injEq]
  refine ⟨rfl, tn_zero, rfl, ?_, ?_⟩ <;> (rw [List.take_of_length_le (by simp)]; exact digOf_vec _)

theorem dec_wsnL : decT (vals tr 6 r pub wsnL) = (wsnRow tr pub r).inL := by
  simp only [decT, wsnL, Wsn.vec]; dsplit
  simp only [WspF.inL, wsnRow, PT.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> (rw [List.take_of_length_le (by simp)]; exact digOf_vec _)

theorem dec_wsnR : decT (vals tr 6 r pub wsnR) = (wsnRow tr pub r).inR := by
  simp only [decT, wsnR, Wsn.vec]; dsplit
  simp only [WspF.inR, wsnRow, PT.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> (rw [List.take_of_length_le (by simp)]; exact digOf_vec _)

theorem dec_wsnO : decT (vals tr 6 r pub wsnO) = (wsnRow tr pub r).outM := by
  simp only [decT, wsnO, Wsn.vec]; dsplit
  simp only [WspF.outM, wsnRow, PT.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> (rw [List.take_of_length_le (by simp)]; exact digOf_vec _)

theorem dec_wsnRS' : decR (vals tr 6 r pub wsnRS) = (0, (wsnRow tr pub r).r.oo) := by
  simp only [decR, wsnRS, Wsn.vec]; dsplit
  simp only [wsnRow, Prod.mk.injEq]
  refine ⟨tn_zero, ?_⟩
  rw [List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wsnRR : decR (vals tr 6 r pub wsnRR) = (ev tr 6 r pub (Wsn.c "nw"), (wsnRow tr pub r).r.oo) := by
  simp only [decR, wsnRR, Wsn.vec]; dsplit
  simp only [wsnRow, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [List.take_of_length_le (by simp)]; exact digOf_vec _

end Dec

/-! ## `WSN` row facts -/

section Wsn
variable {D : Nat} {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem wsn_mem (s : String) (hs : s ∈ ["act", "ph", "top"]) : bool (Wsn.c s) ∈ Wsn.constraints D := by
  unfold Wsn.constraints
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> simp
theorem wsn_mem_off : (1 - Wsn.c "act") * Wsn.c "top" ∈ Wsn.constraints D := by unfold Wsn.constraints; simp
theorem wsn_mem_topL : Wsn.c "top" * (Wsn.c "lvl" - K (D - 1)) ∈ Wsn.constraints D := by
  unfold Wsn.constraints; simp
theorem wsn_mem_topI : Wsn.c "top" * Wsn.c "idx" ∈ Wsn.constraints D := by unfold Wsn.constraints; simp

theorem wsn_flags (hc : ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0) :
    (ev tr 6 r pub (Wsn.c "act") = 0 ∨ ev tr 6 r pub (Wsn.c "act") = 1) ∧
    (ev tr 6 r pub (Wsn.c "top") = 0 ∨ ev tr 6 r pub (Wsn.c "top") = 1) ∧
    (ev tr 6 r pub (Wsn.c "ph") = 0 ∨ ev tr 6 r pub (Wsn.c "ph") = 1) ∧
    (ev tr 6 r pub (Wsn.c "act") = 0 → ev tr 6 r pub (Wsn.c "top") = 0) := by
  refine ⟨ev_bool (hold rfl hc (wsn_mem (D := D) "act" (by simp))),
    ev_bool (hold rfl hc (wsn_mem (D := D) "top" (by simp))),
    ev_bool (hold rfl hc (wsn_mem (D := D) "ph" (by simp))), fun h0 => ?_⟩
  exact FieldWsb.wsb_gate (ev_one_sub0 h0) (hold rfl hc (wsn_mem_off (D := D)))

theorem wsn_m_out (hc : ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0) :
    (Wsn.c "act" - Wsn.c "top").eval tr 6 r pub = 1 ↔
      ((Wsn.c "act").eval tr 6 r pub = 1 ∧ (!(wsnRow tr pub (id r)).r.top) = true) := by
  obtain ⟨ha, ht, -, hoff⟩ := wsn_flags hc
  simp only [evq, ev_sub, wsnRow, id, Bool.not_eq_true', decide_eq_false_iff_not]
  rcases ha with h | h
  · rw [h, hoff h]; simp
  · rcases ht with h' | h' <;> rw [h, h'] <;> simp

theorem wsn_m_s0 (hc : ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0) :
    (Wsn.c "top" * (1 - Wsn.c "ph")).eval tr 6 r pub = 1 ↔
      ((Wsn.c "act").eval tr 6 r pub = 1 ∧
        ((wsnRow tr pub r).r.top && decide ((wsnRow tr pub r).r.seg = 0)) = true) := by
  obtain ⟨ha, ht, hp, hoff⟩ := wsn_flags hc
  simp only [evq, ev_hmul, ev_sub, ev_one, wsnRow, Bool.and_eq_true, decide_eq_true_eq]
  rcases ha with h | h <;> rcases ht with h' | h' <;> rcases hp with h'' | h'' <;>
    simp [h, h', h''] <;> simp_all

theorem wsn_m_q0 (hc : ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0) :
    (Wsn.c "top" * Wsn.c "ph").eval tr 6 r pub = 1 ↔
      ((Wsn.c "act").eval tr 6 r pub = 1 ∧
        ((wsnRow tr pub r).r.top && decide ((wsnRow tr pub r).r.seg = 1)) = true) := by
  obtain ⟨ha, ht, hp, hoff⟩ := wsn_flags hc
  simp only [evq, ev_hmul, wsnRow, Bool.and_eq_true, decide_eq_true_eq]
  rcases ha with h | h <;> rcases ht with h' | h' <;> rcases hp with h'' | h'' <;>
    simp [h, h', h''] <;> simp_all

theorem wsn_top_pos (hc : ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0) (hD1 : 1 ≤ D) (hD : D ≤ 30)
    (ht : ev tr 6 r pub (Wsn.c "top") = 1) :
    ev tr 6 r pub (Wsn.c "lvl") + 1 = D ∧ ev tr 6 r pub (Wsn.c "idx") = 0 := by
  have h1 := eq_of_sub (FieldWsb.wsb_gate ht (hold rfl hc (wsn_mem_topL (D := D))))
  have h2 := FieldWsb.wsb_gate ht (hold rfl hc (wsn_mem_topI (D := D)))
  rw [show K (D - 1) = Expr.const (D - 1) from rfl, ev_const, Nat.mod_eq_of_lt (by omega)] at h1
  exact ⟨by omega, h2⟩

theorem wsn_rowF (hc : ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0) (hD1 : 1 ≤ D) (hD : D ≤ 30) :
    RowF D (wsnRow tr pub r) := by
  refine ⟨?_, ?_, ?_, rfl, ev_lt _, ev_lt _, ev_lt _, Or.inl rfl, fun h => ?_, fun h => ?_⟩
  · simp only [wsnRow]; rw [ev_hadd, ev_one]
  · simp only [wsnRow, sm, ev_mul, ev_const, Nat.reduceMod]
  · simp only [wsnRow, sm, ev_hadd, ev_one, ev_mul, ev_const, Nat.reduceMod]
    have := ev_lt (tr := tr) (t := 6) (r := r) (pub := pub) (Wsn.c "idx")
    omega
  · have : ev tr 6 r pub (Wsn.c "top") = 1 := by simpa [wsnRow] using h
    exact (wsn_top_pos hc hD1 hD this).1
  · have : ev tr 6 r pub (Wsn.c "top") = 1 := by simpa [wsnRow] using h
    exact (wsn_top_pos hc hD1 hD this).2

end Wsn

/-! ## `TREE` balance and the tree -/

section Tree
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hxt : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_TREE)

theorem wsn_hc (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 6 → ∀ e ∈ (Wsn.table D).constraints, e.eval tr 6 r pub = 0 :=
  holds_constr hH (by decide) full_wsn

include hH hxt in
/-- **`TREE` balance, decoded.** -/
theorem tree_traffic : (ptSendsF (wsbL tr pub) (wsnF tr pub)).Perm (ptRecvsF (wsnF tr pub)) := by
  have hc := wsn_hc hH
  have hp := (holds_perm hH B_TREE).map decT
  rw [busList_tree D extra nb np hxt true, busList_tree D extra nb np hxt false,
    tbl_one _ _ _ _ _ wsb_ts, tbl_one _ _ _ _ _ wsn_ts, tbl_nil' wsb_tr, tbl_two _ _ _ _ _ 6 _ _ wsn_tr] at hp
  simp only [List.nil_append, List.map_append] at hp
  have hp2 := hp.trans ((sel2_perm _ _ _ _).map decT)
  rw [List.map_append] at hp2
  have e1 := sel_dec (tr := tr) (t := 5) (pub := pub) 1 1 wsbT (wsbLeaf tr pub)
    (fun _ => true) decT WslRow.ptM (List.range (tr.height 5)) (fun r _ => by simp) (fun r _ _ _ => dec_wsbT)
  have e2 := sel_dec (tr := tr) (t := 6) (pub := pub) (Wsn.c "act" - Wsn.c "top") (Wsn.c "act") wsnO
    id (fun r => !(wsnRow tr pub r).r.top) decT (fun r => (wsnRow tr pub r).outM) (List.range (tr.height 6))
    (fun r hr => wsn_m_out (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wsnO)
  have e3 := sel_dec (tr := tr) (t := 6) (pub := pub) (Wsn.c "act") (Wsn.c "act") wsnL
    id (fun _ => true) decT (fun r => (wsnRow tr pub r).inL) (List.range (tr.height 6))
    (fun r _ => by simp) (fun r _ _ _ => dec_wsnL)
  have e4 := sel_dec (tr := tr) (t := 6) (pub := pub) (Wsn.c "act") (Wsn.c "act") wsnR
    id (fun _ => true) decT (fun r => (wsnRow tr pub r).inR) (List.range (tr.height 6))
    (fun r _ => by simp) (fun r _ _ _ => dec_wsnR)
  rw [e1, e2, e3, e4] at hp2
  simp only [filter_tt] at hp2
  have f1 : ((wsnF tr pub).filter fun x => !x.r.top) = ((wsnIx tr pub).filter fun r => !(wsnRow tr pub r).r.top).map (wsnRow tr pub) := by
    simp only [wsnF, List.filter_map]; rfl
  have f2 : ((wsnF tr pub).filter (·.r.tl)) = wsnF tr pub := List.filter_eq_self.2 (by simp [wsnF, wsnRow])
  have f3 : ((wsnF tr pub).filter (·.r.tr)) = wsnF tr pub := List.filter_eq_self.2 (by simp [wsnF, wsnRow])
  simp only [ptSendsF, ptRecvsF]
  rw [f1, f2, f3]
  simp only [wsnF, List.map_map]
  exact hp2

include hH in
theorem wsn_rows (hD1 : 1 ≤ D) (hD : D ≤ 30) :
    (∀ x ∈ wsnF tr pub, RowF D x) ∧ (wsnF tr pub).length ≤ 2 ^ 20 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    obtain ⟨r, hr, -, rfl⟩ := actRows_mem hr'
    exact wsn_rowF (wsn_hc hH r hr) hD1 hD
  · simp only [wsnF, List.length_map]
    refine Nat.le_trans actRows_length (Nat.pow_le_pow_right (by decide) ?_)
    exact holds_log hH (t := 6) (by decide) full_wsn

include hH in
/-- **Every decoded `WSN` row satisfies `WspOK (nodeH compress)`.** -/
theorem wsn_ok (hD1 : 1 ≤ D) (hD : D ≤ 30) (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf)) :
    ∀ x ∈ plain (wsnF tr pub), WspOK (nodeH compress) D x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hy
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hr'
  have hc := wsn_hc hH r hr
  have hperm := holds_perm hH B_IF384
  have hnode : rowDig tr 6 r pub (fun j => Wsn.c "o" j) =
      nodeH compress (rowDig tr 6 r pub (fun j => Wsn.c "l" j)) (rowDig tr 6 r pub (fun j => Wsn.c "r" j)) := by
    have hm := comp_mem hperm (by rw [full_len]; omega) (g := Wsn.c "act") (cid := Wsn.c "cid")
      (ws := ivW ++ nodeBlock (digW fun t => Wsn.c "l" t) (digW fun t => Wsn.c "r" t) ++
        digW (fun t => Wsn.c "o" t) ++ wordsOf (fun t => Wsn.c "ox" t) 2)
      (fun i hi => by rw [full_wsn]; exact List.mem_append_right _ hi) hr hA
    rw [node_dec] at hm
    obtain ⟨dl, dr, el, er, eo⟩ := comp_node hcomp hC (by simp [digW]) (by simp [digW]) (by simp [digW])
      (by simp [wordsOf]) hm
    rw [rowDig_of eo, rowDig_of el, rowDig_of er]
  have hrow := wsn_rowF hc hD1 hD
  refine ⟨fun h => by simp [wsnRow] at h, fun h => by simp [wsnRow] at h, hnode, hnode,
    fun h => hrow.topLvl h, fun h => hrow.topIdx h⟩

end Tree

/-! ## The roots -/

theorem countP_le_one {β : Type} (p : β → Bool) :
    ∀ {L : List β}, L.Nodup → (∀ a ∈ L, ∀ b ∈ L, p a = true → p b = true → a = b) → L.countP p ≤ 1
  | [], _, _ => by simp
  | x :: xs, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.countP_cons]
    by_cases hx : p x = true
    · have : xs.countP p = 0 := List.countP_eq_zero.2 fun b hb hpb =>
        hn.1 ((h x (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hx hpb) ▸ hb)
      simp [hx, this]
    · have := countP_le_one p hn.2 (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      simp [hx]; omega

theorem filter_map_single {β γ : Type} (L : List β) (g : β → γ) (p : γ → Bool) {q : γ}
    (h : (L.map g).filter p = [q]) : ∃ y, L.filter (fun b => p (g b)) = [y] ∧ g y = q := by
  rw [List.filter_map, List.map_eq_singleton_iff] at h
  obtain ⟨y, h1, h2⟩ := h
  exact ⟨y, h1, h2⟩

theorem wsbL_eq {tr : Trace Fp} {pub : List Fp} :
    wsbL tr pub = (List.range (tr.height 5)).map (wsbLeaf tr pub) := by
  unfold wsbL actRows
  rw [← List.filterMap_eq_map]
  congr 1

section Roots
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hxt : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_TREE)
  (hcomp : CompressOK compress)
  (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
  (hD1 : 1 ≤ D) (hD : D ≤ 20)
include hH hxt hcomp hC hD1 hD

/-- The tree's record premises (`WsTree`). -/
theorem tree_premises :
    (ptSends (wsbL tr pub) (plain (wsnF tr pub))).Perm (ptRecvs (plain (wsnF tr pub))) ∧
    (∀ x ∈ plain (wsnF tr pub), WspOK (nodeH compress) D x) ∧
    (∀ x ∈ plain (wsnF tr pub), x.tl = true ∧ x.tr = true) ∧
    (∀ l ∈ wsbL tr pub, l.dgO = lv tr pub D l.seg l.i) ∧
    (∀ s i, (wsbL tr pub).countP (fun l => decide (l.seg = s ∧ l.i = i)) ≤ 1) := by
  obtain ⟨hrow, hlen⟩ := wsn_rows hH hD1 (by omega)
  have hpt := tree_traffic hH hxt
  have hb := pos_bound hpt hrow hD hlen
  obtain ⟨e1, e2⟩ := pt_eq (wsl := wsbL tr pub) hrow hD hb
  have hcW := holds_constr hH (t := 5) (by decide) (full_wsb (D := D))
  have hlog := holds_log hH (t := 5) (by decide) (full_wsb (D := D))
  have hidx := FieldWsb.wsb_index hcW hlog (by omega)
  refine ⟨e1 ▸ e2 ▸ hpt, wsn_ok hH hD1 (by omega) hcomp hC, fun x hx => ?_, fun l hl => ?_, fun s i => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy
    simp [wsnRow]
  · rw [wsbL_eq] at hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
    have hr := List.mem_range.1 hr
    simp only [wsbLeaf, lv]
    congr 1
    rcases hidx r hr with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, b]; omega
    · rw [a]; omega
  · rw [wsbL_eq, List.countP_map]
    apply countP_le_one _ List.nodup_range
    intro a ha b hb pa pb
    simp only [Function.comp_def, wsbLeaf] at pa pb
    replace pa := of_decide_eq_true pa
    replace pb := of_decide_eq_true pb
    exact FieldWsb.wsb_row_inj hcW hlog (by omega) (List.mem_range.1 ha) (List.mem_range.1 hb)
      (pa.1.trans pb.1.symm) (pa.2.trans pb.2.symm)

/-- **The `WSN` roots**: the decoded INTAKE root message is `[(0, r0)]` with `r0` the root of the
phase-0 `WSB` leaves, and the FINAL one is `[(nw, rF)]` with `rF` the root of the phase-1 leaves. -/
theorem wsn_roots :
    (∃ r0, s0 tr pub = [(0, r0)] ∧ root (nodeH compress) D (wsLeaves tr pub D 0) = some r0) ∧
    (∃ nw rF, q0 tr pub = [(nw, rF)] ∧ root (nodeH compress) D (wsLeaves tr pub D 1) = some rF) := by
  obtain ⟨hbal, hok, hfull, hleaf, hdist⟩ := tree_premises hH hxt hcomp hC hD1 hD
  have hcW := holds_constr hH (t := 5) (by decide) (full_wsb (D := D))
  have hlog := holds_log hH (t := 5) (by decide) (full_wsb (D := D))
  have hc := wsn_hc hH
  have leafAt : ∀ ph, ph ≤ 1 → ∃ l ∈ wsbL tr pub, l.seg = ph := by
    intro ph hph
    obtain ⟨hr, hp, -⟩ := WsLen.wsb_pos hcW hlog (by omega) ph 0 hph (Nat.two_pow_pos D)
    rw [wsbL_eq]
    exact ⟨_, List.mem_map.2 ⟨_, List.mem_range.2 hr, rfl⟩, hp⟩
  have plainE : plain (wsnF tr pub) = (wsnIx tr pub).map fun r => (wsnRow tr pub r).r := by
    simp [plain, wsnF, List.map_map, Function.comp_def]
  constructor
  · obtain ⟨l, hl, hs⟩ := leafAt 0 (by omega)
    obtain ⟨q, -, hf, hroot⟩ := tree_root hbal hok hfull hleaf hdist hl
    rw [hs] at hf hroot
    rw [plainE] at hf
    obtain ⟨y, hy, rfl⟩ := filter_map_single _ _ _ hf
    refine ⟨_, ?_, hroot⟩
    have e := sel_dec (tr := tr) (t := 6) (pub := pub) (Wsn.c "top" * (1 - Wsn.c "ph")) (Wsn.c "act") wsnRS
      id (fun r => (wsnRow tr pub r).r.top && decide ((wsnRow tr pub r).r.seg = 0)) decR
      (fun r => (0, (wsnRow tr pub r).r.oo)) (List.range (tr.height 6))
      (fun r hr => wsn_m_s0 (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wsnRS')
    unfold s0
    rw [e]
    show List.map _ (List.filter _ (wsnIx tr pub)) = _
    rw [hy]; rfl
  · obtain ⟨l, hl, hs⟩ := leafAt 1 (by omega)
    obtain ⟨q, -, hf, hroot⟩ := tree_root hbal hok hfull hleaf hdist hl
    rw [hs] at hf hroot
    rw [plainE] at hf
    obtain ⟨y, hy, rfl⟩ := filter_map_single _ _ _ hf
    refine ⟨ev tr 6 y pub (Wsn.c "nw"), _, ?_, hroot⟩
    have e := sel_dec (tr := tr) (t := 6) (pub := pub) (Wsn.c "top" * Wsn.c "ph") (Wsn.c "act") wsnRR
      id (fun r => (wsnRow tr pub r).r.top && decide ((wsnRow tr pub r).r.seg = 1)) decR
      (fun r => (ev tr 6 r pub (Wsn.c "nw"), (wsnRow tr pub r).r.oo)) (List.range (tr.height 6))
      (fun r hr => wsn_m_q0 (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wsnRR)
    unfold q0
    rw [e]
    show List.map _ (List.filter _ (wsnIx tr pub)) = _
    rw [hy]; rfl

end Roots

/-! ## The final working set, with the tree build discharged -/

/-- **The final working set from `Holds`** (the `WSN` premises of `WsDecode3.ws_decoded_final`
discharged): with `ws0` / `wsF` the phase-0 / phase-1 `WSB` leaf digests (`wsLeaves`; by
`WsLen.wsb_leaves`, `wsLen` real leaves then zero padding), there is a segment count `nw` such that
`wsF` is `ws0` with each touched index holding the new digest of its last touching `WSL` row, whose
closing value is its entry's latest written value. -/
theorem ws_decoded_final2 {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
    {compress : List Nat → List Nat → List Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR compress)
    (hkd : ∀ l ∈ wsl tr pub, ∀ l' ∈ wsl tr pub, l.seg = l'.seg → l.kd = l'.kd → l.i = l'.i) :
    ∃ nw, wsLeaves tr pub D 1 = WsSeg.wsAt (wsl tr pub) (wsLeaves tr pub D 0) nw ∧
    (∀ l ∈ wsl tr pub, l.seg < nw ∧ l.i < 2 ^ D ∧
        (WsSeg.wsAt (wsl tr pub) (wsLeaves tr pub D 0) l.seg)[l.i]? = some l.dgO ∧
        (WsSeg.wsAt (wsl tr pub) (wsLeaves tr pub D 0) (l.seg + 1))[l.i]? = some l.dgN) ∧
    (∀ i, i < 2 ^ D → (∀ l ∈ wsl tr pub, l.i ≠ i) → (wsLeaves tr pub D 1)[i]? = (wsLeaves tr pub D 0)[i]?) ∧
    (∀ l ∈ wsl tr pub, (∀ l' ∈ wsl tr pub, l'.i = l.i → l'.seg ≤ l.seg) →
      (wsLeaves tr pub D 1)[l.i]? = some l.dgN) ∧
    (∀ l ∈ wsl tr pub, ∃ s : List (WsCost.Acc (List Nat)), s.Perm (accOf (wsa tr pub) l.key) ∧
      s.Pairwise (fun a b => b.t < a.t) ∧ l.ncur = WsCost.lastVal l.cur s ∧ l.idl = WsCost.lastT s ∧
      WsCost.Reads l.cur s) ∧
    (∀ a ∈ wsa tr pub, ∃ l ∈ wsl tr pub, l.key = a.key) ∧
    (∀ l ∈ wsl tr pub, l.i < WsLen.wsLen pub) := by
  have hx4 : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG :=
    fun T hT i hi => ⟨(hx T hT i hi).1, (hx T hT i hi).2.1, (hx T hT i hi).2.2.1, (hx T hT i hi).2.2.2.1⟩
  have hxt : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_TREE := fun T hT i hi => (hx T hT i hi).2.2.2.2
  obtain ⟨⟨r0, hs0, hr0⟩, ⟨nw, rF, hq0, hrF⟩⟩ := wsn_roots hH hxt hcomp hC hD1 hD
  exact ⟨nw, ws_decoded_final hH hx4 hcomp hC hD1 hD hCR hs0 hq0 (slice_length _ _ _ _) hr0
    (slice_length _ _ _ _) hrF hkd⟩

end StateM5a.WsDecode4
