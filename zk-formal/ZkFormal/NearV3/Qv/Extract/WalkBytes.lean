import ZkFormal.NearV3.Qv.Extract.WalkMetadata

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem walk_bit {r i : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r walk=1) (hi : i<8) :
    tr.cell tt r (Candidates.ValueTable.reg i)=0 ∨ tr.cell tt r (Candidates.ValueTable.reg i)=1 := by
  have he : Expr.mul (c walk) (Dsl.bool (c (Candidates.ValueTable.reg i)))∈constraints := by
    have hm := List.mem_map_of_mem
      (f:=fun i => Expr.mul (c walk) (Dsl.bool (c (Candidates.ValueTable.reg i)))) (List.mem_range.mpr hi)
    unfold constraints
    simp only [List.mem_append,hm,true_or,or_true]
  have hh := con hL hr he
  simp only [eval_mul,eval_c,eval_bool,ha] at hh
  apply bool_cases
  simpa only [Lean.Grind.Semiring.one_mul] using hh

theorem walk_nibble {r : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r walk=1)
    (off : Nat) (ho : off+4≤8) :
    ∃ n : Nat, n<16 ∧ (nibble off).eval tr tt r pub=(n:Fp) := by
  have hb : ∀ b, b<4 → tr.cell tt r (Candidates.ValueTable.reg (off+b))=0 ∨
      tr.cell tt r (Candidates.ValueTable.reg (off+b))=1 := fun b hb => walk_bit hL hr ha (by omega)
  refine ⟨bitsVal (fun b => cv tr tt r (Candidates.ValueTable.reg b)) off 4,?_,?_⟩
  · exact bitsVal_lt _ _ _ (fun b hb' => cv_bool (hb b hb'))
  · exact eval_bits tr tt r pub Candidates.ValueTable.reg off 4 hb

/-- Every walk key cell is a canonical byte, derived from the eight constrained bits. -/
theorem walk_byte {r : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r walk=1) :
    cv tr tt r wb<256 := by
  obtain ⟨low,hlow,helow⟩ := walk_nibble hL hr ha 0 (by decide)
  obtain ⟨high,hhigh,hehigh⟩ := walk_nibble hL hr ha 4 (by decide)
  have hh := con hL hr (e:=eqG (c walk) (c wb) (.add (nibble 0) (smul 16 (nibble 4))))
    (by simp [constraints])
  simp only [eval_eqG,eval_c,eval_add,eval_smul,ha,helow,hehigh] at hh
  have he : tr.cell tt r wb=((low+16*high:Nat):Fp) := by
    rw [natCast_add,natCast_mul]
    grind
  have hn : low+16*high<256 := by omega
  have hp : low+16*high<P := by unfold P; omega
  simpa only [cv,he,toNat_natCast,Nat.mod_eq_of_lt hp] using hn

/-- The queue-key tag and length are determined by accepted AIR constraints. -/
theorem walk_key_shape {s len : Nat} (hfit : s+len≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len) :
    (cv tr tt s wb=7 ∧ len=1) ∨ (cv tr tt s wb=13 ∧ len=1) ∨
    (cv tr tt s wb=10 ∧ len=1) ∨ (cv tr tt s wb=16 ∧ len=9) := by
  have hlen := hs.1
  have hr : s<tr.height tt := by omega
  have hh := walk_header hL hfit hs
  have hl := walk_kind_length hL hfit hs
  rcases isBool hL hr (x:=lo) (by simp [walkBools]) with hlo | hlo <;>
    rcases isBool hL hr (x:=hi) (by simp [walkBools]) with hhi | hhi
  all_goals rw [hlo,hhi] at hh
  · have he : tr.cell tt s wb=(7:Nat) := by grind
    exact Or.inl ⟨by simp [cv,he,toNat_natCast,P],hl.2 (Or.inl hlo)⟩
  · have he : tr.cell tt s wb=(10:Nat) := by grind
    exact Or.inr (Or.inr (Or.inl ⟨by simp [cv,he,toNat_natCast,P],hl.2 (Or.inl hlo)⟩))
  · have he : tr.cell tt s wb=(13:Nat) := by grind
    exact Or.inr (Or.inl ⟨by simp [cv,he,toNat_natCast,P],hl.2 (Or.inr hhi)⟩)
  · have he : tr.cell tt s wb=(16:Nat) := by grind
    exact Or.inr (Or.inr (Or.inr ⟨by simp [cv,he,toNat_natCast,P],hl.1 ⟨hlo,hhi⟩⟩))

end ZkFormal.NearV3.Qv.Extract
