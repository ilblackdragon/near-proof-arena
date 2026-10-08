import ZkFormal.NearV3.Candidates.ProcPriorMemoryLiftLocal
import ZkFormal.NearV3.Candidates.ProcPriorRowNext
import ZkFormal.NearV3.Candidates.ProcPriorEventNext
namespace ZkFormal.NearV3.Candidates.ProcPriorCells
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ProcPriorMemoryTable

def bit (b : Bool) : Fp := if b then 1 else 0

def cell (a : ProcPriorRows.Row) (t : Nat) (sm : Bool) (iv : Fp) : Nat → Fp
  | 0 => 1
  | 1 => Fp.ofNat t
  | 2 => Fp.ofNat a.event.link
  | 3 => Fp.ofNat a.event.stamp
  | 4 => bit a.event.query
  | 5 => Fp.ofNat a.event.lo
  | 6 => bit a.event.hi
  | 7 => Fp.ofNat a.before.1
  | 8 => bit a.before.2
  | 9 => bit sm
  | 10 => iv
  | _ => 0

def env (cur nxt : Nat → Fp) (first last trans : Fp) : Env Fp where
  ofNat := Fp.ofNat
  add := (·+·)
  mul := (·*·)
  neg := (-·)
  col := fun c nx => if nx then nxt c else cur c
  pub := fun _ => 0
  isFirst := first
  isLast := last
  isTransition := trans

theorem bit_bool (b : Bool) : bit b * (bit b - 1)=0 := by cases b <;> simp [bit] <;> grind

theorem active_boolean (a : ProcPriorRows.Row) (t : Nat) (sm : Bool) (iv : Fp)
    (nxt : Nat → Fp) (first last trans : Fp) (c : Nat)
    (hc:c∈[act,query,hi,beforeHi,same]) :
    (ZkFormal.Chacha.Table.boolC c).evalWith (env (cell a t sm iv) nxt first last trans)=0 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  all_goals simp [ZkFormal.Chacha.Table.boolC,sub,k,ZkFormal.Chacha.Table.E.c,
    Expr.evalWith,env,cell,act,query,hi,beforeHi,same,bit]
  all_goals have hone : Fp.ofNat 1 = (1:Fp) := rfl
  all_goals try (split <;> grind)
  all_goals grind

/-- The field delta is zero exactly when the canonical link indices agree. -/
theorem link_delta (a b : Nat) (ha:a<4096) (hb:b<4096) :
    (Fp.ofNat b-Fp.ofNat a=0) ↔ a=b := by
  constructor
  · intro h
    have he:Fp.ofNat b=Fp.ofNat a := by grind
    have hn:=congrArg Fp.toNat he
    simp only [Fp.toNat_ofNat] at hn
    have hap:a<P := by
      have hp:P>4096:=by decide +kernel
      omega
    have hbp:b<P := by
      have hp:P>4096:=by decide +kernel
      omega
    simpa [Nat.mod_eq_of_lt hap,Nat.mod_eq_of_lt hbp] using hn.symm
  · intro h; subst b; grind

theorem delta_inverse (a b : Nat) (ha:a<4096) (hb:b<4096) :
    (Fp.ofNat b-Fp.ofNat a)*(Fp.ofNat b-Fp.ofNat a)⁻¹=1-bit (decide (a=b)) := by
  by_cases h:a=b
  · subst b; simp [bit]; grind
  · have hd:(Fp.ofNat b-Fp.ofNat a)≠0 := fun he=>h ((link_delta a b ha hb).mp he)
    rw [Fp.mul_inv_cancel hd]
    simp [bit,h]
    grind

end ZkFormal.NearV3.Candidates.ProcPriorCells
