import ZkFormal.Near.Extract.Statements
import ZkFormal.Near.Extract.BusCount
import ZkFormal.Sha.Compose

/-!
# ZkFormal.Near.Extract.ShaFacts — `ShaFactsStmt` from L5's statements

L5's `sha_digest_contract` (proved from L5's sublemma statements) in the
form the NEAR linking uses.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha NearSpec

theorem mem_of_count_pos {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : 0 < l.count a) : a ∈ l := List.count_pos_iff.mp h

theorem count_pos_of_mem {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : a ∈ l) : 0 < l.count a := List.count_pos_iff.mpr h

theorem sha_is_bytes (q : Nat) (hq : q < 16) :
    (Sha.Table.interactions B_BYTES B_DIGEST)[q]! ∈ Sha.Table.interactions B_BYTES B_DIGEST ∧
    ((Sha.Table.interactions B_BYTES B_DIGEST)[q]!).bus = B_BYTES ∧
    ((Sha.Table.interactions B_BYTES B_DIGEST)[q]!).send = false ∧
    ((Sha.Table.interactions B_BYTES B_DIGEST)[q]!).mult = [Expr.col (Layout.colF q) false] := by
  have hl : q < (Sha.Table.interactions B_BYTES B_DIGEST).length := by
    simp [Sha.Table.interactions]; omega
  have he : (Sha.Table.interactions B_BYTES B_DIGEST)[q]! = (Sha.Table.interactions B_BYTES B_DIGEST)[q] := by
    simp [getElem!_def, List.getElem?_eq_getElem hl]
  rw [he]
  refine ⟨List.getElem_mem hl, ?_⟩
  simp [Sha.Table.interactions, List.getElem_append, hq, Sha.Table.E.c]

def shaDigestI : Interaction := (Sha.Table.interactions B_BYTES B_DIGEST)[16]!

theorem sha_mem {i : Interaction} (hi : i ∈ Sha.Table.interactions B_BYTES B_DIGEST) :
    (i.bus = B_BYTES ∧ i.send = false) ∨ i = shaDigestI := by
  simp only [Sha.Table.interactions, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hi
  rcases hi with ⟨q, -, rfl⟩ | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr rfl

theorem shaDigestI_bus : shaDigestI.bus = B_DIGEST ∧ shaDigestI.send = true := ⟨rfl, rfl⟩

theorem shaFacts_of (hB : BlockStmt) (hIV : IVStmt) (hC : ChainStmt) (hF : FrameStmt)
    (hIO : DigestIoStmt) : ShaFactsStmt := by
  intro tr pub hL
  refine ⟨?_, ?_, ?_⟩
  · intro b m hb
    simp only [shaCounts, tableBusCount_eq]
    apply List.count_eq_zero_of_not_mem
    intro hm
    simp only [List.mem_flatMap, rowTraffic, List.mem_range] at hm
    obtain ⟨r, -, i, hi, hm⟩ := hm
    rcases sha_mem hi with ⟨-, hs⟩ | rfl
    · simp [hs] at hm
    · simp [shaDigestI_bus.1, Ne.symm hb] at hm
  · intro b m hb
    simp only [shaCounts, tableBusCount_eq]
    apply List.count_eq_zero_of_not_mem
    intro hm
    simp only [List.mem_flatMap, rowTraffic, List.mem_range] at hm
    obtain ⟨r, -, i, hi, hm⟩ := hm
    rcases sha_mem hi with ⟨hbb, -⟩ | rfl
    · simp [hbb, Ne.symm hb] at hm
    · simp [shaDigestI_bus.2] at hm
  · intro m hm
    simp only [shaCounts, tableBusCount_eq] at hm
    have hm := mem_of_count_pos hm
    simp only [List.mem_flatMap, rowTraffic, List.mem_range] at hm
    obtain ⟨d, hd, i, hi, hmi⟩ := hm
    by_cases hbs : i.bus = B_DIGEST ∧ i.send = true
    · rw [if_pos hbs] at hmi
      obtain ⟨hpos, rfl⟩ := List.mem_replicate.mp hmi
      -- the active send is the digest interaction, so its bit is 1
      have hi16 : i = shaDigestI := by
        rcases sha_mem hi with ⟨-, hs⟩ | h
        · rw [hbs.2] at hs; cases hs
        · exact h
      subst hi16
      have hmult : tr.cell T_SHA d Layout.colDmult = 1 := by
        refine Classical.byContradiction fun hne => hpos ?_
        simp [shaDigestI, Interaction.multNat, Interaction.multNat.go, Sha.Table.interactions,
          Expr.eval, Expr.evalWith, rowEnv, Sha.Table.E.c, hne]
      obtain ⟨m', dg, -, hdg, hmsg, hbytes⟩ :=
        sha_digest_contract hB hIV hC hF hIO hL B_BYTES B_DIGEST hd hmult
      refine ⟨tr.cell T_SHA d Layout.colId, m', ?_, ?_⟩
      · rw [show shaDigestI = (Sha.Table.interactions B_BYTES B_DIGEST)[16]! from rfl, hmsg, hdg]
      · intro j hj
        obtain ⟨r, hr, q, hq, hfq, hmq⟩ := hbytes j hj
        simp only [shaCounts, tableBusCount_eq]
        apply count_pos_of_mem
        simp only [List.mem_flatMap, rowTraffic, List.mem_range]
        obtain ⟨hmem, hbus, hsend, hmul⟩ := sha_is_bytes q hq
        refine ⟨r, hr, _, hmem, ?_⟩
        rw [if_pos ⟨hbus, hsend⟩]
        have hgd : (m'.getD j 0) = m'[j]! := by
          rw [List.getD_eq_getElem?_getD, getElem!_def]; cases m'[j]? <;> rfl
        rw [hgd, ← hmq]
        apply List.mem_replicate.mpr
        refine ⟨?_, rfl⟩
        rw [Interaction.multNat, hmul]
        simp [Interaction.multNat.go, Expr.eval, Expr.evalWith, rowEnv, hfq]
    · rw [if_neg hbs] at hmi; simp at hmi

end ZkFormal.Near
