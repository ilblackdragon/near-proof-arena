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
    rowT tr pub r B_VPARENT true = [] ∧ rowT tr pub r B_BMAP true = [] ∧ rowT tr pub r B_BMAP false = [] ∧
    rowT tr pub r B_DUP false = [] := by
  have hr : r < tr.height T_NODE := by have := hC.bound; omega
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  have hgP : tr.cell T_NODE r gP = 0 := by rw [G.1, hfs]; grind
  have hgD : tr.cell T_NODE r gD = 0 := by rw [M.2.1, hgP, hfs]; grind
  have hgDp : tr.cell T_NODE r gDp = 0 := by rw [G.2.2.2.2.2.1, hgP, hgD]; grind
  have hgBm : tr.cell T_NODE r gBm = 0 := by rw [G.2.2.2.2.2.2.1, hfs]; grind
  have hnf : tr.cell T_NODE r nf = 0 := bool01 hL hr (by simp [boolCols]) (fun h => by
    have := ((rowFacts hL hr).2.2.2.1 h).2.2.1; rw [hfs] at this; exact fp_zero_ne_one this)
  have hgV : tr.cell T_NODE r gV = 0 := by rw [G.2.1, hnf]; grind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rowT_digest, hgD, hgDp]; simp [gate]
  · rw [rowT_parentS, hgP]; simp [gate]
  · rw [rowT_parentR, hnf]; simp [gate]
  · rw [rowT_vparentS, hgD, hgP, show (0 : Fp) - 0 = 0 by decide]; simp [gate]
  · rw [rowT_bmapS, hgBm]; simp [gate]
  · rw [rowT_bmapR, hgBm]; simp [gate]
  · rw [rowT_dupR, hgV]; simp [gate]

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

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- Gates at any field start. -/
theorem startGates {r : Nat} (hr : r < tr.height T_NODE) (hfs : tr.cell T_NODE r fs = 1) :
    tr.cell T_NODE r gP = tr.cell T_NODE r sCH * tr.cell T_NODE r rv ∧
    tr.cell T_NODE r gD = tr.cell T_NODE r sCH * tr.cell T_NODE r rv + tr.cell T_NODE r sVH * tr.cell T_NODE r tv ∧
    tr.cell T_NODE r gDp = tr.cell T_NODE r sCH * tr.cell T_NODE r rv +
      tr.cell T_NODE r sVH * tr.cell T_NODE r tv * tr.cell T_NODE r tw ∧
    tr.cell T_NODE r gBm = tr.cell T_NODE r sBM := by
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  refine ⟨by rw [G.1, hfs]; grind, by rw [M.2.1, G.1, hfs]; grind, ?_, by rw [G.2.2.2.2.2.2.1, hfs]; grind⟩
  rw [G.2.2.2.2.2.1, M.2.1, G.1, hfs]; grind

/-- A field start other than the node start: no `PARENT` / `DUP` receive. -/
theorem innerStart (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o) :
    rowT tr pub (s + o) B_PARENT false = [] ∧ rowT tr pub (s + o) B_DUP false = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have hnf : tr.cell T_NODE (s + o) nf = 0 := zero_of hL hr (by simp [boolCols])
    (hC.seg.2.2.2.2.1 (s + o) (by omega) (by have := hF.pos; have := (hC.fields.field _ hm).2; simp at this; omega))
  have G := linkGates hL hr
  simp only at G
  refine ⟨by rw [rowT_parentR, hnf]; simp [gate], ?_⟩
  rw [rowT_dupR, G.2.1, hnf, show (0 : Fp) * tr.cell T_NODE (s + o) dup = 0 by grind]; simp [gate]

/-- The node start (`TAG` row). -/
theorem tagStart (hC : NodeCtx tr s ℓ fl) :
    rowT tr pub s B_PARENT true = [] ∧ rowT tr pub s B_DIGEST false = [] ∧ rowT tr pub s B_VPARENT true = [] ∧
    rowT tr pub s B_BMAP true = [] ∧ rowT tr pub s B_BMAP false = [] ∧
    rowT tr pub s B_PARENT false =
      [[tr.cell T_NODE s nid, tr.cell T_NODE s tau, tr.cell T_NODE s depth, tr.cell T_NODE s len, tr.cell T_NODE s res]] ∧
    rowT tr pub s B_DUP false = gate (tr.cell T_NODE s dup)
      [(K_NPRE : Fp) + (16 : Nat) * tr.cell T_NODE s nid, tr.cell T_NODE s repE] := by
  obtain ⟨hr, ha⟩ := nodeStart hL hC
  have hnf : tr.cell T_NODE s nf = 1 := by have := hC.seg.2.1; rwa [one_iff] at this
  obtain ⟨-, sT, hfs, -, -⟩ := (rowFacts hL hr).2.2.2.1 hnf
  have G := linkGates hL hr
  simp only at G
  obtain ⟨g1, g2, g3, g4⟩ := startGates hL hr hfs
  have hch : tr.cell T_NODE s sCH = 0 := stOnly hL hr ha sT (by simp [states]) (by simp [states]) (by decide)
  have hvh : tr.cell T_NODE s sVH = 0 := stOnly hL hr ha sT (by simp [states]) (by simp [states]) (by decide)
  have hbm : tr.cell T_NODE s sBM = 0 := stOnly hL hr ha sT (by simp [states]) (by simp [states]) (by decide)
  simp only [hch, hvh] at g1 g2 g3; simp only [hbm] at g4
  have z1 : tr.cell T_NODE s gP = 0 := by rw [g1]; grind
  have z2 : tr.cell T_NODE s gD = 0 := by rw [g2]; grind
  have z3 : tr.cell T_NODE s gDp = 0 := by rw [g3]; grind
  refine ⟨by rw [rowT_parentS, z1]; simp [gate], by rw [rowT_digest, z2, z3]; simp [gate],
    by rw [rowT_vparentS, z1, z2, show (0 : Fp) - 0 = 0 by decide]; simp [gate],
    by rw [rowT_bmapS, g4]; simp [gate], by rw [rowT_bmapR, g4]; simp [gate],
    by rw [rowT_parentR, hnf]; simp [gate], ?_⟩
  rw [rowT_dupR, G.2.1, hnf, show (1 : Fp) * tr.cell T_NODE s dup = tr.cell T_NODE s dup by grind]

/-- A value window start (`VH`). -/
theorem vhStart (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (hv : tr.cell T_NODE (s + o) sVH = 1) :
    rowT tr pub (s + o) B_PARENT true = [] ∧ rowT tr pub (s + o) B_BMAP true = [] ∧ rowT tr pub (s + o) B_BMAP false = [] ∧
    rowT tr pub (s + o) B_DIGEST false =
      gate (tr.cell T_NODE (s + o) tv) ([(K_VPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) vid,
        tr.cell T_NODE (s + o) vlen] ++ regW tr (s + o) reg) ++
      gate (tr.cell T_NODE (s + o) tv * tr.cell T_NODE (s + o) tw)
        ([(K_VPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) vid + ((1 : Nat) : Fp),
        tr.cell T_NODE (s + o) vlen] ++ regW tr (s + o) preg) ∧
    rowT tr pub (s + o) B_VPARENT true = gate (tr.cell T_NODE (s + o) tv)
      [tr.cell T_NODE (s + o) vid, tr.cell T_NODE (s + o) vlen] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 hF.pos).2 rfl
  have hch : tr.cell T_NODE (s + o) sCH = 0 := stOnly hL hr ha hv (by simp [states]) (by simp [states]) (by decide)
  have hbm : tr.cell T_NODE (s + o) sBM = 0 := stOnly hL hr ha hv (by simp [states]) (by simp [states]) (by decide)
  obtain ⟨g1, g2, g3, g4⟩ := startGates hL hr hfs
  simp only [hch, hv] at g1 g2 g3; simp only [hbm] at g4
  have z1 : tr.cell T_NODE (s + o) gP = 0 := by rw [g1]; grind
  have e2 : tr.cell T_NODE (s + o) gD = tr.cell T_NODE (s + o) tv := by rw [g2]; grind
  have e3 : tr.cell T_NODE (s + o) gDp = tr.cell T_NODE (s + o) tv * tr.cell T_NODE (s + o) tw := by rw [g3]; grind
  refine ⟨by rw [rowT_parentS, z1]; simp [gate], by rw [rowT_bmapS, g4]; simp [gate],
    by rw [rowT_bmapR, g4]; simp [gate], ?_, ?_⟩
  · rw [rowT_digest, e2, e3]
    rcases isBool hL hr (x := tv) (by simp [boolCols]) with ht | ht
    · rw [ht, show (0 : Fp) * tr.cell T_NODE (s + o) tw = 0 by grind]; simp [gate]
    · obtain ⟨d1, d2⟩ := (winMisc hL hr).2.2.2 (by rw [e2, z1, ht]; decide)
      rw [ht, d1, d2, show (1 : Fp) * tr.cell T_NODE (s + o) tw = tr.cell T_NODE (s + o) tw by grind]
  · rw [rowT_vparentS, e2, z1, show tr.cell T_NODE (s + o) tv - 0 = tr.cell T_NODE (s + o) tv by grind]

/-- A child window start (`CH`). -/
theorem chStartMsgs (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (hc : tr.cell T_NODE (s + o) sCH = 1) :
    rowT tr pub (s + o) B_VPARENT true = [] ∧ rowT tr pub (s + o) B_BMAP true = [] ∧ rowT tr pub (s + o) B_BMAP false = [] ∧
    rowT tr pub (s + o) B_PARENT true = gate (tr.cell T_NODE (s + o) rv)
      [tr.cell T_NODE (s + o) cid, tr.cell T_NODE (s + o) tau, tr.cell T_NODE (s + o) depth + ((1 : Nat) : Fp),
        tr.cell T_NODE (s + o) clen, tr.cell T_NODE (s + o) cres] ∧
    rowT tr pub (s + o) B_DIGEST false =
      gate (tr.cell T_NODE (s + o) rv) ([(K_NPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) cid,
        tr.cell T_NODE (s + o) clen] ++ regW tr (s + o) reg) ++
      gate (tr.cell T_NODE (s + o) rv) ([(K_NPRE : Fp) + ((16 : Nat) : Fp) * tr.cell T_NODE (s + o) cid + ((1 : Nat) : Fp),
        tr.cell T_NODE (s + o) clen] ++ regW tr (s + o) preg) := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 hF.pos).2 rfl
  have hvh : tr.cell T_NODE (s + o) sVH = 0 := stOnly hL hr ha hc (by simp [states]) (by simp [states]) (by decide)
  have hbm : tr.cell T_NODE (s + o) sBM = 0 := stOnly hL hr ha hc (by simp [states]) (by simp [states]) (by decide)
  obtain ⟨g1, g2, g3, g4⟩ := startGates hL hr hfs
  simp only [hc, hvh] at g1 g2 g3; simp only [hbm] at g4
  have e1 : tr.cell T_NODE (s + o) gP = tr.cell T_NODE (s + o) rv := by rw [g1]; grind
  have e2 : tr.cell T_NODE (s + o) gD = tr.cell T_NODE (s + o) rv := by rw [g2]; grind
  have e3 : tr.cell T_NODE (s + o) gDp = tr.cell T_NODE (s + o) rv := by rw [g3]; grind
  refine ⟨by rw [rowT_vparentS, e1, e2, show tr.cell T_NODE (s + o) rv - tr.cell T_NODE (s + o) rv = 0 by grind]; simp [gate],
    by rw [rowT_bmapS, g4]; simp [gate], by rw [rowT_bmapR, g4]; simp [gate], ?_⟩
  rw [rowT_parentS, e1, rowT_digest, e2, e3]
  rcases isBool hL hr (x := rv) (by simp [boolCols]) with ht | ht
  · rw [ht]; simp [gate]
  · obtain ⟨d1, d2⟩ := (winMisc hL hr).2.2.1 (by rw [e1, ht])
    rw [ht, d1, d2]; simp [gate]

/-- A bitmap field start (`BM`). -/
theorem bmStartMsgs (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 2) ∈ fl) (hb : tr.cell T_NODE (s + o) sBM = 1) :
    rowT tr pub (s + o) B_PARENT true = [] ∧ rowT tr pub (s + o) B_DIGEST false = [] ∧ rowT tr pub (s + o) B_VPARENT true = [] ∧
    rowT tr pub (s + o) B_BMAP true = [[tr.cell T_NODE (s + o) nid, bmE.eval tr T_NODE (s + o) pub, tr.cell T_NODE (s + o) tb2, 0]] ∧
    rowT tr pub (s + o) B_BMAP false =
      [[tr.cell T_NODE (s + o) nid, bmE.eval tr T_NODE (s + o) pub, tr.cell T_NODE (s + o) tb2, tr.cell T_NODE (s + o) mBm]] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 hF.pos).2 rfl
  have hvh : tr.cell T_NODE (s + o) sVH = 0 := stOnly hL hr ha hb (by simp [states]) (by simp [states]) (by decide)
  have hch : tr.cell T_NODE (s + o) sCH = 0 := stOnly hL hr ha hb (by simp [states]) (by simp [states]) (by decide)
  obtain ⟨g1, g2, g3, g4⟩ := startGates hL hr hfs
  simp only [hch, hvh] at g1 g2 g3; simp only [hb] at g4
  have z1 : tr.cell T_NODE (s + o) gP = 0 := by rw [g1]; grind
  have z2 : tr.cell T_NODE (s + o) gD = 0 := by rw [g2]; grind
  have z3 : tr.cell T_NODE (s + o) gDp = 0 := by rw [g3]; grind
  exact ⟨by rw [rowT_parentS, z1]; simp [gate], by rw [rowT_digest, z2, z3]; simp [gate],
    by rw [rowT_vparentS, z1, z2, show (0 : Fp) - 0 = 0 by decide]; simp [gate],
    by rw [rowT_bmapS, g4]; simp [gate], by rw [rowT_bmapR, g4]; simp [gate]⟩

/-- Any other field start (`HPL`, `HPF`, `KEY`, `VLEN`, `MEM`): no gated message. -/
theorem plainStart (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (h1 : tr.cell T_NODE (s + o) sCH = 0) (h2 : tr.cell T_NODE (s + o) sVH = 0) (h3 : tr.cell T_NODE (s + o) sBM = 0) :
    rowT tr pub (s + o) B_PARENT true = [] ∧ rowT tr pub (s + o) B_DIGEST false = [] ∧
    rowT tr pub (s + o) B_VPARENT true = [] ∧ rowT tr pub (s + o) B_BMAP true = [] ∧
    rowT tr pub (s + o) B_BMAP false = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have hfs : tr.cell T_NODE (s + o) fs = 1 := by simpa using (hF.fs 0 hF.pos).2 rfl
  obtain ⟨g1, g2, g3, g4⟩ := startGates hL hr hfs
  simp only [h1, h2] at g1 g2 g3; simp only [h3] at g4
  have z1 : tr.cell T_NODE (s + o) gP = 0 := by rw [g1]; grind
  have z2 : tr.cell T_NODE (s + o) gD = 0 := by rw [g2]; grind
  have z3 : tr.cell T_NODE (s + o) gDp = 0 := by rw [g3]; grind
  exact ⟨by rw [rowT_parentS, z1]; simp [gate], by rw [rowT_digest, z2, z3]; simp [gate],
    by rw [rowT_vparentS, z1, z2, show (0 : Fp) - 0 = 0 by decide]; simp [gate],
    by rw [rowT_bmapS, g4]; simp [gate], by rw [rowT_bmapR, g4]; simp [gate]⟩

end ZkFormal.NearV3.NodeProof3
