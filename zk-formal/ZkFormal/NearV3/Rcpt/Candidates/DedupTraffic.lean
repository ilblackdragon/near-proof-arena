import ZkFormal.NearV3.Rcpt.Candidates.DedupDuplicateLocal
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficFrames

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.SrcpGen
open ZkFormal.Near.Dsl SrcpV3 SrcpProof

theorem candidate_rowT {tr : Trace Fp} {pub : List Fp} {tt : Nat} (r bb : Nat) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt r pub bb sd =
      (if bb = B_BYTES ∧ sd = true ∧ tr.cell tt r sg = 1 then
        [[(K_SRC : Fp) + (16 : Nat) * tr.cell tt r q, (32 : Nat) * tr.cell tt r wn + tr.cell tt r pw,
          tr.cell tt r b]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ tr.cell tt r gD = 1 then
        [[tr.cell tt r cId, tr.cell tt r cLen] ++ regsF tr tt r] else []) ++
      (if bb = B_RCL ∧ sd = false ∧ tr.cell tt r rt = 1 then [[tr.cell tt r j, tr.cell tt r L]] else []) ++
      (if bb = B_SRC ∧ sd = false ∧ tr.cell tt r rt = 1 then
        [[tr.cell tt r j, tr.cell tt r dup, tr.cell tt r DedupTable.repeated] ++ regsF tr tt r] else []) ++
      (if bb = B_SIZE ∧ sd = true ∧ tr.cell tt r gz = 1 then [[((2 : Nat) : Fp), tr.cell tt r sz]] else []) := by
  simp only [rowTraffic, DedupTable.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons, List.map_append,
    List.map_nil, eval_c, eval_k, eval_mid, eval_add, eval_smul, List.append_assoc, regs, List.map_map,
    Function.comp_def, regsF, List.cons_append, List.nil_append]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))) <;> (split <;> split <;> simp_all [eq_comm]) <;> first | rfl | grind

def rowN (c : Nat → Nat) (bb : Nat) (sd : Bool) : List Msg :=
  (if bb = B_BYTES ∧ sd = true ∧ c SrcpV3.sg = 1 then
    [[msgId K_SRC (c SrcpV3.q), 32 * c SrcpV3.wn + c SrcpV3.pw, c SrcpV3.b]] else []) ++
  (if bb = B_DIGEST ∧ sd = false ∧ c SrcpV3.gD = 1 then
    [[c SrcpV3.cId, c SrcpV3.cLen] ++ regN c] else []) ++
  (if bb = B_RCL ∧ sd = false ∧ c SrcpV3.rt = 1 then [[c SrcpV3.j, c SrcpV3.L]] else []) ++
  (if bb = B_SRC ∧ sd = false ∧ c SrcpV3.rt = 1 then
    [[c SrcpV3.j, c SrcpV3.dup, c DedupTable.repeated] ++ regN c] else []) ++
  (if bb = B_SIZE ∧ sd = true ∧ c SrcpV3.gz = 1 then [[2, c SrcpV3.sz]] else [])

private theorem ofNat_one {v : Nat} (hv : v ≤ 1) : Fp.ofNat v = 1 ↔ v = 1 := by
  have hh : v = 0 ∨ v = 1 := by omega
  rcases hh with rfl | rfl <;> decide

/-- Row traffic is the field image of the executable natural messages. -/
theorem row_traffic {tr : Trace Fp} {tt r : Nat} {pub : List Fp} (c : Nat → Nat)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (c x))
    (hb : ∀ x ∈ boolCols, c x ≤ 1) (bb : Nat) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt r pub bb sd = (rowN c bb sd).map Msg.toFp := by
  have hreg : SrcpProof.regsF tr tt r = (regN c).map Fp.ofNat := by
    simp [SrcpProof.regsF, regN, hc, List.map_map, Function.comp_def]
  rw [candidate_rowT, hreg]
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


/-- Repetition and terminal metadata do not alter the digest registers. -/
theorem regN_local (B : SrcpB) (before : Nat) (kind : Kind) (terminal repeated : Bool) :
    regN (localCells B before kind terminal repeated) = regN (frame B before kind).cell := by
  have he : regN (localCells B before kind terminal repeated) =
      regN ({frame B before kind with gz := terminal}).cell := by
    apply List.map_congr_left
    intro i hi
    have hne : SrcpV3.reg i ≠ 56 := by
      have := List.mem_range.mp hi
      simp only [SrcpV3.reg]
      omega
    simp only [localCells, hne, ↓reduceIte]
  rw [he, regN_gz]

/-- A skipped source header consumes its authenticated public record and receipt
length, but no source hash digest. Terminal headers also emit the final SIZE. -/
theorem root_messages (B : SrcpB) (before : Nat) (terminal repeated : Bool)
    (hl : B.root.length = 32) (bb : Nat) (sd : Bool) :
    rowN (localCells B before .root terminal repeated) bb sd =
      (if bb = B_DIGEST ∧ sd = false ∧ B.dup = false then
        [digMsg (msgId K_SRC B.qe) B.le B.root] else []) ++
      (if bb = B_RCL ∧ sd = false then [[B.j, B.L]] else []) ++
      (if bb = B_SRC ∧ sd = false then
        [[B.j, B.dup.toNat, repeated.toNat] ++ B.root] else []) ++
      (if bb = B_SIZE ∧ sd = true ∧ terminal = true then [[2, before + B.L]] else []) := by
  have hregs : (frame B before .root).regs = B.root := by
    cases hd : B.dup <;> simp [frame, hd, rootFrame]
  have hreg : regN (localCells B before .root terminal repeated) = B.root := by
    rw [regN_local, regN_full _ (by rw [hregs]; exact hl), hregs]
  simp only [rowN, hreg]
  cases hd : B.dup <;> cases terminal <;> cases repeated
  all_goals simp [localCells, frame, hd, rootFrame, Frame.cell,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.gz, SrcpV3.q, SrcpV3.wn, SrcpV3.pw,
    SrcpV3.b, SrcpV3.cId, SrcpV3.cLen, SrcpV3.j, SrcpV3.L, SrcpV3.dup,
    SrcpV3.sz, DedupTable.repeated, digMsg]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
