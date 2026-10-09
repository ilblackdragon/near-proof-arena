import ZkFormal.NearV3.Assembly.RcptTerminalRows

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The native RC list header: destination shard u64 followed by receipt count u32. -/
def headerStream (own : Nat) (plan : ListPlan) : List Fp :=
  (u64 own++u32 plan.inputs.length).map (fun b=>Fp.ofNat b.toNat)

def headerStreamAux (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if reg 0≤col ∧ col<reg 32 then registerCell (headerStream own plan) row.index col else
  if col=b then (headerStream own plan).getD row.index 0 else
  tokenHeaderAux before fallback plan row col

theorem headerStream_length (own : Nat) (plan : ListPlan) :
    (headerStream own plan).length=12 := by simp [headerStream,u64,u32,leN]

theorem header_stream_reg (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord)
    (j : Nat) (hj : j<32) :
    headerCell (headerStreamAux own before fallback) plan row (reg j)=
      (headerStream own plan).getD (row.index+j) 0 := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22 ∨ j=23 ∨ j=24 ∨ j=25 ∨ j=26 ∨ j=27 ∨ j=28 ∨ j=29 ∨ j=30 ∨ j=31 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl

theorem header_stream_byte (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord) :
    headerCell (headerStreamAux own before fallback) plan row b=
      (headerStream own plan).getD row.index 0 := rfl

theorem header_stream_token (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord)
    (j : Nat) (hj : j<16) :
    headerCell (headerStreamAux own before fallback) plan row (tok j)=
      Fp.ofNat (((u128 (before plan)).getD j 0).toNat) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl

theorem header_stream_shift (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord)
    (j : Nat) (hj : j<31) :
    headerCell (headerStreamAux own before fallback) plan (advance row) (reg j)=
      headerCell (headerStreamAux own before fallback) plan row (reg (j+1)) := by
  rw [header_stream_reg _ _ _ _ _ _ (by omega),header_stream_reg _ _ _ _ _ _ (by omega)]
  simp only [advance]
  congr 1
  omega

/-- All 31 original register-shift equations on generated consecutive header rows. -/
theorem header_stream_shift_constraints (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord) (pub : List Fp) :
    ∀e∈shiftConstraints,e.eval
      ⟨fun _=>1,fun _ pos col=>headerCell (headerStreamAux own before fallback) plan
        (if pos=0 then row else advance row) col⟩ 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul3,eval_not,eval_sub,eval_c,eval_n]
  change _*_* (headerCell (headerStreamAux own before fallback) plan (advance row) (reg j)-
    headerCell (headerStreamAux own before fallback) plan row (reg (j+1)))=0
  rw [header_stream_shift _ _ _ _ _ _ hj']
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
