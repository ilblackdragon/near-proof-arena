import ZkFormal.NearV3.Candidates.ProcConcatRows
namespace ZkFormal.NearV3.Candidates.ProcConcatKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry ProcConcatRows

theorem cell_cast (rs : List Run) (t r c : Nat) :
    (trace rs).cell t r c=Fp.ofNat ((atRow rs r).cell c) := by
  rfl

theorem act_cast (rs : List Run) (t r : Nat) :
    (trace rs).cell t r Proc.act=if r<(rows rs).length then 1 else 0 := by
  rw [cell_cast]
  change Fp.ofNat ((atRow rs r).act)=_
  rw [active]
  split <;> rfl

/-- The native initial instance starts at tau zero; later instances will be
assembled after its rows, rather than incorrectly reusing an isFirst row. -/
theorem kind_constraints (rs : List Run) (htau : ∀ R rest,rs=R::rest → R.tau=0)
    (hrows : (rows rs).length+1≤2^22) (t r : Nat) (pub : List Fp)
    (hr : r<2^22) : ∀ e ∈ Proc.cKind, e.eval (trace rs) t r pub=0 := by
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  intro e he
  simp only [Proc.cKind,List.mem_append] at he
  rcases he with he | he
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.1 he
    have hb := (flags rs r).1 c hc
    change Fp.ofNat ((atRow rs r).cell c)*(Fp.ofNat ((atRow rs r).cell c) + -(1 : Fp))=0
    rcases ofNat_bit hb with h | h <;> rw [h] <;> grind
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · change (trace rs).cell t r Proc.act + -((trace rs).cell t r Proc.kK+
        ((trace rs).cell t r Proc.kH+(trace rs).cell t r Proc.kE))=0
      simp only [cell_cast]
      change Fp.ofNat ((atRow rs r).act) + -(Fp.ofNat ((atRow rs r).kK)+
        (Fp.ofNat ((atRow rs r).kH)+Fp.ofNat ((atRow rs r).kE)))=0
      rw [shape]
      change (((atRow rs r).kK+(atRow rs r).kH+(atRow rs r).kE : Nat) : Fp)+
        -(((atRow rs r).kK : Fp)+(((atRow rs r).kH : Fp)+((atRow rs r).kE : Fp)))=0
      grind
    · change (if r+1=2^22 then (1 : Fp) else 0)*(trace rs).cell t r Proc.act=0
      rw [act_cast]
      by_cases hl : r+1=2^22
      · rw [if_pos hl,if_neg (by omega)]
        grind
      · rw [if_neg hl]; grind
    · change ((if r+1=2^22 then (0 : Fp) else 1)*(1 + -(trace rs).cell t r Proc.act))*
        (trace rs).cell t ((r+1)%2^22) Proc.act=0
      rw [act_cast,act_cast]
      by_cases hl : r+1=2^22
      · rw [if_pos hl]; grind
      · rw [if_neg hl,Nat.mod_eq_of_lt (by omega)]
        by_cases ha : r<(rows rs).length
        · rw [if_pos ha]; grind
        · rw [if_neg ha,if_neg (by omega)]; grind
    · change (if r=0 then (1 : Fp) else 0)*
        ((trace rs).cell t r Proc.act*(1 + -(trace rs).cell t r Proc.kK))=0
      by_cases h0 : r=0
      · subst r
        rw [if_pos rfl,cell_cast,cell_cast,first]
        cases rs <;> simp [padPV,zeroV,keyV,PV.cell,Proc.act,Proc.kK,cast_eq] <;> grind
      · rw [if_neg h0]; grind
    · change (if r=0 then (1 : Fp) else 0)*(trace rs).cell t r Proc.kc=0
      by_cases h0 : r=0
      · subst r
        rw [if_pos rfl,cell_cast,first]
        cases rs <;> change (1 : Fp)*0=0 <;> grind
      · rw [if_neg h0]; grind
    · change (if r=0 then (1 : Fp) else 0)*(trace rs).cell t r Proc.tau=0
      by_cases h0 : r=0
      · subst r
        rw [if_pos rfl,cell_cast,first]
        cases rs with
        | nil => change (1 : Fp)*0=0; grind
        | cons R rest =>
          change (1 : Fp)*Fp.ofNat R.tau=0
          rw [htau R rest rfl]
          rfl
      · rw [if_neg h0]; grind
end ZkFormal.NearV3.Candidates.ProcConcatKind
