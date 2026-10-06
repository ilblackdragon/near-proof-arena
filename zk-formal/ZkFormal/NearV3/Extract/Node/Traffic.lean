import ZkFormal.NearV3.Extract.Node.Global

/-!
# ZkFormal.Near.Extract.NodeTraffic — per-node messages (BYTES, DIGEST, PARENT, VSLOT)
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem ofNat_cv' (tr : Trace Fp) (r x : Nat) : Fp.ofNat (cv tr T_NODE r x) = tr.cell T_NODE r x := ofNat_cv tr T_NODE r x

theorem toFp_msgId (k i : Nat) : ((msgId k i : Nat) : Fp) = (k : Fp) + ((16 : Nat) : Fp) * ((i : Nat) : Fp) := by
  unfold msgId; rw [natCast_add, natCast_mul]

theorem gate_one (m : List Fp) : gate 1 m = [m] := by simp [gate]
theorem gate_zero (m : List Fp) : gate 0 m = [] := by simp [gate]

theorem emitAt_eq (id : Nat) (bytes : List Nat) :
    emitAt id 0 bytes = (List.range bytes.length).map fun i => [id, i, bytes.getD i 0] := by
  simp [emitAt]

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- BYTES sends of one node. -/
theorem nodeBytes (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp))
    (hpos : ∀ d, d < ℓ → tr.cell T_NODE (s + d) pos = ((d : Nat) : Fp)) :
    ((List.range' s ℓ).flatMap fun r => rowT tr pub r B_BYTES true).Perm
      ((emitAt (msgId K_NPRE n) 0 ((nodeVOf tr s).ser false) ++
        emitAt (msgId K_NPOST n) 0 ((nodeVOf tr s).ser true)).map Msg.toFp) := by
  obtain ⟨S1, S2⟩ := nodeSer hL hC
  rw [← S1, ← S2, emitAt_eq, emitAt_eq, rowsB_length, rowsB_length, List.map_append, List.map_map, List.map_map]
  have e : ((List.range' s ℓ).flatMap fun r => rowT tr pub r B_BYTES true) =
      (List.range ℓ).flatMap fun d =>
        (Msg.toFp ∘ fun i => [msgId K_NPRE n, i, (rowsB tr b s ℓ).getD i 0]) d ::
        [(Msg.toFp ∘ fun i => [msgId K_NPOST n, i, (rowsB tr pb s ℓ).getD i 0]) d] := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
    rw [rowT_bytes, segAct hL hC hd, gate_one, gate_one]
    have hnid : tr.cell T_NODE (s + d) nid = ((n : Nat) : Fp) := by rw [segConst hL hC (by simp [nodeConst]) hd, hn]
    simp only [Function.comp, Msg.toFp, rowsB, List.map_cons, List.map_nil, List.singleton_append, List.cons_append,
      List.nil_append]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
      List.getElem?_range hd]
    simp only [Option.map_some, Option.getD_some, hnid, hpos d hd, ← natCast_eq, toFp_msgId, ← cell_eq_cast]
  rw [e, map_eq_flatMap _ (Msg.toFp ∘ _), map_eq_flatMap _ (Msg.toFp ∘ _)]
  exact flatMap_append_perm (List.range ℓ) (fun d => [_]) (fun d => [_])

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem flatMap_flatMap' {α β γ : Type} (l : List α) (g : α → List β) (f : β → List γ) :
    (l.flatMap g).flatMap f = l.flatMap fun p => (g p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_append, ih]

theorem fp_mul3_zero_l {a b' c' : Fp} : 0 * b' * c' = 0 := by grind
theorem fp_add_zero_zero {a b' : Fp} (ha : a = 0) (hb : b' = 0) : a + b' = 0 := by rw [ha, hb]; decide

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem rowsFields {α : Type} (hC : NodeCtx tr s ℓ fl) (f : Nat → List α) :
    (List.range' s ℓ).flatMap f = fl.flatMap fun p => (List.range' (s + p.1) p.2).flatMap f := by
  have e := range'_segs fl 0 hC.fields.consec
  rw [hC.fields.cover, Nat.sub_zero] at e
  have e2 : List.range' s ℓ = (List.range' 0 ℓ).map (s + ·) := by
    rw [List.map_add_range']; simp
  rw [e2, List.flatMap_map, e, flatMap_flatMap']
  apply flatMap_congr'; intro p _
  rw [← List.map_add_range', List.flatMap_map]

/-- Rows that are not a field start emit nothing on the gated buses. -/
theorem quietRow (hC : NodeCtx tr s ℓ fl) {r : Nat} (h1 : s ≤ r) (h2 : r < s + ℓ) (hfs : tr.cell T_NODE r fs = 0) :
    rowT tr pub r B_DIGEST false = [] ∧ rowT tr pub r B_PARENT true = [] ∧ rowT tr pub r B_PARENT false = [] ∧
    rowT tr pub r B_VSLOT false = [] := by
  have hr : r < tr.height T_NODE := by have := hC.bound; omega
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  have hgP : tr.cell T_NODE r gP = 0 := by rw [G.1, hfs]; grind
  have hgD : tr.cell T_NODE r gD = 0 := by rw [M.2.1, hgP, hfs]; grind
  have hnf : tr.cell T_NODE r nf = 0 := bool01 hL hr (by simp [boolCols]) (fun h => by
    have := ((rowFacts hL hr).2.2.2.1 h).2.2.1; rw [hfs] at this; exact fp_zero_ne_one this)
  have hr0 : r ≠ 0 := by
    intro h0; subst h0
    have := (firstRow hL (by omega)).2.1; rw [hnf] at this; exact fp_zero_ne_one this
  have hgV : tr.cell T_NODE r gV = 0 := by rw [G.2.1, hnf]; grind
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rowT_digest, hgD, if_neg hr0]; simp [gate]
  · rw [rowT_parentS, hgP]; simp [gate]
  · rw [rowT_parentR, hnf, if_neg hr0, show (0 : Fp) - 0 = 0 by decide]; simp [gate]
  · rw [rowT_vslotR, hgV]; simp [gate]

/-- On a gated bus, a field emits only at its first row. -/
theorem fieldGated (hC : NodeCtx tr s ℓ fl) {p : Nat × Nat} (hp : p ∈ fl) {bb : Nat} {sd : Bool}
    (hq : ∀ r, s ≤ r → r < s + ℓ → tr.cell T_NODE r fs = 0 → rowT tr pub r bb sd = []) :
    (List.range' (s + p.1) p.2).flatMap (fun r => rowT tr pub r bb sd) = rowT tr pub (s + p.1) bb sd := by
  have hF := hC.fields.field p hp
  have hpos := hF.1.pos
  rw [show p.2 = 1 + (p.2 - 1) by omega, ← List.range'_append_1, List.range'_one, List.flatMap_append,
    List.flatMap_singleton]
  rw [flatMap_range'_nil _ _ _ (fun j hj => hq _ (by omega) (by have := hF.2; omega) (by
    have := hF.1.fs (1 + j) (by omega)
    exact bool01 hL (by have := hC.bound; have := hF.2; omega) (by simp [boolCols])
      (fun h => by rw [show s + p.1 + 1 + j = s + p.1 + (1 + j) by omega] at h; have := this.1 h; omega)))]
  simp

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- A field start other than the node start. -/
theorem innerStart (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o) :
    rowT tr pub (s + o) B_PARENT false = [] ∧ rowT tr pub (s + o) B_VSLOT false = [] ∧
    tr.cell T_NODE (s + o) gP = tr.cell T_NODE (s + o) sCH * tr.cell T_NODE (s + o) rv ∧
    tr.cell T_NODE (s + o) gD = tr.cell T_NODE (s + o) sCH * tr.cell T_NODE (s + o) rv +
      tr.cell T_NODE (s + o) sVH * tr.cell T_NODE (s + o) tv ∧ s + o ≠ 0 := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 hF.pos).2 rfl
  have hnf : tr.cell T_NODE (s + o) nf = 0 := zero_of hL hr (by simp [boolCols])
    (hC.seg.2.2.2.2.1 (s + o) (by omega) (by have := hF.pos; have := (hC.fields.field _ hm).2; simp at this; omega))
  have hr0 : s + o ≠ 0 := by omega
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  refine ⟨?_, ?_, by rw [G.1, hfs]; grind, by rw [M.2.1, G.1, hfs]; grind, hr0⟩
  · rw [rowT_parentR, hnf, if_neg hr0, show (0 : Fp) - 0 = 0 by decide]; simp [gate]
  · rw [rowT_vslotR, G.2.1, hnf, show (0 : Fp) * tr.cell T_NODE (s + o) tv = 0 by grind]; simp [gate]

/-- The node start (`TAG` row). -/
theorem tagStart (hC : NodeCtx tr s ℓ fl) :
    rowT tr pub s B_PARENT true = [] ∧
    rowT tr pub s B_DIGEST false =
      gate (if s = 0 then 1 else 0) ([(K_NPRE : Fp), tr.cell T_NODE s len] ++ (List.range 32).map fun i => pub.getD (PV_PRE + i) 0) ++
      gate (if s = 0 then 1 else 0) ([(K_NPOST : Fp), tr.cell T_NODE s len] ++ (List.range 32).map fun i => pub.getD (PV_POST + i) 0) ∧
    rowT tr pub s B_PARENT false = gate (if s = 0 then 0 else 1)
        [tr.cell T_NODE s nid, tr.cell T_NODE s depth, tr.cell T_NODE s len, tr.cell T_NODE s res] ∧
    rowT tr pub s B_VSLOT false = gate (tr.cell T_NODE s tv) [tr.cell T_NODE s nid] := by
  obtain ⟨hr, ha⟩ := nodeStart hL hC
  have hnf : tr.cell T_NODE s nf = 1 := by have := hC.seg.2.1; rwa [one_iff] at this
  obtain ⟨-, sT, hfs, -, -⟩ := (rowFacts hL hr).2.2.2.1 hnf
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  have hch : tr.cell T_NODE s sCH = 0 := stOnly hL hr ha sT (by simp [states]) (by simp [states]) (by decide)
  have hvh : tr.cell T_NODE s sVH = 0 := stOnly hL hr ha sT (by simp [states]) (by simp [states]) (by decide)
  have hgP : tr.cell T_NODE s gP = 0 := by rw [G.1, hch]; grind
  have hgD : tr.cell T_NODE s gD = 0 := by rw [M.2.1, hgP, hvh]; grind
  refine ⟨by rw [rowT_parentS, hgP]; simp [gate], by rw [rowT_digest, hgD]; simp [gate], ?_, ?_⟩
  · rw [rowT_parentR, hnf]
    by_cases h0 : s = 0
    · rw [if_pos h0, if_pos h0, show (1 : Fp) - 1 = 0 by decide]
    · rw [if_neg h0, if_neg h0, show (1 : Fp) - 0 = 1 by decide]
  · rw [rowT_vslotR, G.2.1, hnf, show (1 : Fp) * tr.cell T_NODE s tv = tr.cell T_NODE s tv by grind]

/-- A value window start (`VH`). -/
theorem vhStart (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (ho : 0 < o)
    (hv : tr.cell T_NODE (s + o) sVH = 1) :
    rowT tr pub (s + o) B_PARENT true = [] ∧
    rowT tr pub (s + o) B_DIGEST false =
      gate (tr.cell T_NODE (s + o) tv) ([(K_VPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) nid, ((72 : Nat) : Fp)] ++
        regW tr (s + o) reg) ++
      gate (tr.cell T_NODE (s + o) tv) ([(K_VPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) nid + ((1 : Nat) : Fp),
        ((72 : Nat) : Fp)] ++ regW tr (s + o) preg) := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have hch : tr.cell T_NODE (s + o) sCH = 0 := stOnly hL hr ha hv (by simp [states]) (by simp [states]) (by decide)
  obtain ⟨-, -, hgP, hgD, -⟩ := innerStart hL hC hm ho
  rw [hch] at hgP hgD; rw [hv] at hgD
  have hgP' : tr.cell T_NODE (s + o) gP = 0 := by rw [hgP]; grind
  have hgD' : tr.cell T_NODE (s + o) gD = tr.cell T_NODE (s + o) tv := by rw [hgD]; grind
  refine ⟨by rw [rowT_parentS, hgP']; simp [gate], ?_⟩
  rw [rowT_digest, hgD', if_neg (by omega)]
  rcases isBool hL hr (x := tv) (by simp [boolCols]) with ht | ht
  · rw [ht]; simp [gate]
  · obtain ⟨e1, e2⟩ := (winMisc hL hr).2.2.2 (by rw [hgD', hgP', ht]; decide)
    rw [ht, e1, e2]; simp [gate]; rfl

/-- A child window start (`CH`). -/
theorem chStartMsgs (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (ho : 0 < o)
    (hc : tr.cell T_NODE (s + o) sCH = 1) :
    rowT tr pub (s + o) B_PARENT true = gate (tr.cell T_NODE (s + o) rv)
      [tr.cell T_NODE (s + o) cid, tr.cell T_NODE (s + o) depth + ((1 : Nat) : Fp), tr.cell T_NODE (s + o) clen,
        tr.cell T_NODE (s + o) cres] ∧
    rowT tr pub (s + o) B_DIGEST false =
      gate (tr.cell T_NODE (s + o) rv) ([(K_NPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) cid,
        tr.cell T_NODE (s + o) clen] ++ regW tr (s + o) reg) ++
      gate (tr.cell T_NODE (s + o) rv) ([(K_NPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) cid + ((1 : Nat) : Fp),
        tr.cell T_NODE (s + o) clen] ++ regW tr (s + o) preg) := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have hvh : tr.cell T_NODE (s + o) sVH = 0 := stOnly hL hr ha hc (by simp [states]) (by simp [states]) (by decide)
  obtain ⟨-, -, hgP, hgD, -⟩ := innerStart hL hC hm ho
  rw [hc] at hgP hgD; rw [hvh] at hgD
  have hgP' : tr.cell T_NODE (s + o) gP = tr.cell T_NODE (s + o) rv := by rw [hgP]; grind
  have hgD' : tr.cell T_NODE (s + o) gD = tr.cell T_NODE (s + o) rv := by rw [hgD]; grind
  rw [rowT_parentS, hgP', rowT_digest, hgD', if_neg (by omega)]
  rcases isBool hL hr (x := rv) (by simp [boolCols]) with ht | ht
  · rw [ht]; simp [gate]
  · obtain ⟨e1, e2⟩ := (winMisc hL hr).2.2.1 (by rw [hgP', ht])
    rw [ht, e1, e2]; simp [gate]

end ZkFormal.NearV3.NodeProof3
