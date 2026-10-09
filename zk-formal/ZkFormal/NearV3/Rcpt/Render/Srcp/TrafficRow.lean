import ZkFormal.NearV3.Rcpt.Render.Srcp.LocalProof

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

def regN (c : Nat → Nat) : List Nat := (List.range 32).map fun x => c (SrcpV3.reg x)

/-- Natural messages in the exact interaction order of one source row. -/
def rowN (c : Nat → Nat) (bb : Nat) (sd : Bool) : List Msg :=
  (if bb = B_BYTES ∧ sd = true ∧ c SrcpV3.sg = 1 then
    [[msgId K_SRC (c SrcpV3.q), 32 * c SrcpV3.wn + c SrcpV3.pw, c SrcpV3.b]] else []) ++
  (if bb = B_DIGEST ∧ sd = false ∧ c SrcpV3.gD = 1 then
    [[c SrcpV3.cId, c SrcpV3.cLen] ++ regN c] else []) ++
  (if bb = B_RCL ∧ sd = false ∧ c SrcpV3.rt = 1 then [[c SrcpV3.j, c SrcpV3.L]] else []) ++
  (if bb = B_SRC ∧ sd = false ∧ c SrcpV3.rt = 1 then
    [[c SrcpV3.j, c SrcpV3.dup] ++ regN c] else []) ++
  (if bb = B_SIZE ∧ sd = true ∧ c SrcpV3.gz = 1 then [[2, c SrcpV3.sz]] else [])

private theorem ofNat_one {v : Nat} (hv : v ≤ 1) : Fp.ofNat v = 1 ↔ v = 1 := by
  have hh : v = 0 ∨ v = 1 := by omega
  rcases hh with rfl | rfl <;> decide

/-- Row traffic is the field image of the executable natural messages. -/
theorem row_traffic {tr : Trace Fp} {tt r : Nat} {pub : List Fp} (c : Nat → Nat)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (c x))
    (hb : ∀ x ∈ boolCols, c x ≤ 1) (bb : Nat) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt r pub bb sd = (rowN c bb sd).map Msg.toFp := by
  have hreg : SrcpProof.regsF tr tt r = (regN c).map Fp.ofNat := by
    simp [SrcpProof.regsF, regN, hc, List.map_map, Function.comp_def]
  rw [SrcpProof.rowT, hreg]
  simp only [hc, ofNat_one (hb SrcpV3.sg (by decide)),
    ofNat_one (hb SrcpV3.gD (by decide)), ofNat_one (hb SrcpV3.rt (by decide)),
    ofNat_one (hb SrcpV3.gz (by decide)), rowN, List.map_append]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  simp only [List.append_assoc]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_)))
  all_goals split <;> simp_all [Msg.toFp, SrcpProof.ofNat_msgId,
    ← ofNat_add', ← ofNat_mul']
  all_goals rfl

end ZkFormal.NearV3.Render.SrcpGen
