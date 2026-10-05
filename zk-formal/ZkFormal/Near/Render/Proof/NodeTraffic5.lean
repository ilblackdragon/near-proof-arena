import ZkFormal.Near.Render.Proof.NodeTraffic4

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic5 — node traffic: EDGE, rows → fields

The EDGE traffic of a row is its gated edges `ge` with the counter (`RT_edge_sem`);
the gated edges of a node's rows are those of its fields (`ge_fields`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeTr
open NodeCells NodeGen NodeInfo

def gated : Option (Edge × Bool) → List Edge
  | some (e, true) => [e]
  | _ => []

/-- The gated edges of a row. -/
def ge (I : Info) (r : NRec) : List Edge := gated (edgeAOf I r) ++ gated (edgeBOf I r)

theorem edgeA_shape (I : Info) (r : NRec) {e : Edge} {g : Bool} (h : edgeAOf I r = some (e, g)) :
    e = [r.n, e.getD 1 0, e.getD 2 0, e.getD 3 0, e.getD 4 0] := by
  obtain ⟨n, pos, f, idx, b, pb⟩ := r
  simp only [edgeAOf] at h
  by_cases h0 : pos = 0 ∧ n = 0
  · rw [if_pos h0] at h; simp at h; obtain ⟨rfl, -⟩ := h; simp [h0.2]
  · rw [if_neg h0] at h
    cases f <;> simp only at h <;> (repeat' split at h) <;> simp at h <;> obtain ⟨rfl, -⟩ := h <;> rfl

theorem edgeB_shape (I : Info) (r : NRec) {e : Edge} {g : Bool} (h : edgeBOf I r = some (e, g)) :
    e = [r.n, 2 * r.idx + oddOf (I.nodeAt r.n) + 1, r.b % 16, e.getD 3 0, e.getD 4 0] ∧ r.f = .key := by
  obtain ⟨n, pos, f, idx, b, pb⟩ := r
  simp only [edgeBOf] at h
  cases f <;> simp only at h <;> (repeat' split at h) <;> simp at h <;> obtain ⟨rfl, -⟩ := h <;> exact ⟨rfl, rfl⟩

theorem loN_key (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (h : r.f = .key) : loN I u r = r.b % 16 := by
  have hn : r.f.nib = true := by rw [h]; rfl
  simp only [loN]
  rw [show (33 : Nat) = 33 + 0 from rfl, show (34 : Nat) = 33 + 1 from rfl, show (35 : Nat) = 33 + 2 from rfl,
    show (36 : Nat) = 33 + 3 from rfl, rc_lbit _ _ _ 0 (by decide), rc_lbit _ _ _ 1 (by decide),
    rc_lbit _ _ _ 2 (by decide), rc_lbit _ _ _ 3 (by decide)]
  simp only [hn, if_true, bitOf]
  omega

theorem part_edge (u : Std.HashMap Edge Nat) (s : Bool) (x : Option (Edge × Bool)) (a0 a1 a2 : Nat)
    (hx : ∀ e g, x = some (e, g) → e = [a0, a1, a2, e.getD 3 0, e.getD 4 0]) :
    (if Fp.ofNat (gateCell x) = 1 then [[Fp.ofNat a0, Fp.ofNat a1, Fp.ofNat a2, Fp.ofNat (edgeCell x u 3),
      Fp.ofNat (edgeCell x u 4), if s then 0 else Fp.ofNat (multCell x u)]] else []) =
      ((gated x).map fun e => e ++ [if s then 0 else u.getD e 0]).map Msg.toFp := by
  rcases x with _ | ⟨e, g⟩
  · simp [gateCell, gated, ofNat0']
  · have he := hx e g rfl
    cases g with
    | false => simp [gateCell, gated, ofNat0']
    | true =>
      simp only [gateCell, gated, ofNat1', if_true, edgeCell, multCell, List.map_cons, List.map_nil]
      have he' : [a0, a1, a2, e[3]?.getD 0, e[4]?.getD 0] = e := by
        rw [he]; rfl
      have hm : List.map Fp.ofNat e = [Fp.ofNat a0, Fp.ofNat a1, Fp.ofNat a2, Fp.ofNat (e[3]?.getD 0),
          Fp.ofNat (e[4]?.getD 0)] := by rw [← he']; rfl
      cases s <;> simp [Msg.toFp, ofNat0', hm]

theorem RT_edge_sem (I : Info) (u : Std.HashMap Edge Nat) (pub : List Fp) (r : NRec) (s : Bool) :
    RT I u pub r B_EDGE s = ((ge I r).map fun e => e ++ [if s then 0 else u.getD e 0]).map Msg.toFp := by
  rw [RT_edge, ge, List.map_append, List.map_append]
  congr 1
  · simp only [V, rc_gA, rc_nid, rc_aI, rc_aS, rc_aN, rc_aJ, rc_mA]
    refine part_edge u s _ r.n _ _ (fun e g h => ?_)
    have he := edgeA_shape I r h
    simp only [edgeCell, h]; exact he
  · simp only [V, rc_gB, rc_nid, rc_bN, rc_bJ, rc_mB, rc_idx, rc_odd]
    by_cases hk : r.f = .key
    · rw [loN_key I u r hk]
      exact part_edge u s _ r.n _ _ (fun e g h => (edgeB_shape I r h).1)
    · have : edgeBOf I r = none := by
        cases h : edgeBOf I r with
        | none => rfl
        | some eg => exact absurd (edgeB_shape I r h).2 hk
      simp [this, gateCell, gated, ofNat0']

end NodeTr

end ZkFormal.Near.Render
