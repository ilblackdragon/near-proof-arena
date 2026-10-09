import ZkFormal.NearV3.Sched.Complete.ProcRows
import ZkFormal.NearV3.Sched.Complete.Cmp
namespace ZkFormal.NearV3.Candidates.ProcBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def GateBits (V : PV) : Prop := V.kK≤1 ∧ V.kH≤1 ∧ V.cg≤1 ∧ V.kE≤1 ∧ V.pm≤1

theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide

theorem key_bits (R : Run) (k : Nat) : GateBits (keyV R k) := by
  simp [GateBits,keyV,zeroV]

theorem header_bits (R : Run) (rd : RoundD) : GateBits (hdrV R rd) := by
  simp [GateBits,hdrV,baseV,zeroV,b2n_le]

theorem entry_bits (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat) :
    GateBits (entV R rd es i) := by
  simp [GateBits,entV,baseV,zeroV,b2n_le]

theorem padding_bits : GateBits padPV := by simp [GateBits,padPV,zeroV]

theorem native_bits (V : PV) (hv : GateBits V) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat (V.cell c)) :
    ∀ i ∈ Proc.interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub=0 ∨ b.eval tr t r pub=1 := by
  have kk := ofNat_bit hv.1
  have kh := ofNat_bit hv.2.1
  have cg := ofNat_bit hv.2.2.1
  have ke := ofNat_bit hv.2.2.2.1
  have pm := ofNat_bit hv.2.2.2.2
  simp only [Proc.interactions,List.forall_mem_cons,List.forall_mem_nil]
  simp [ZkFormal.Chacha.Table.E.c,Expr.eval,Expr.evalWith,rowEnv,hc,
    PV.cell,Proc.kK,Proc.kH,Proc.cg,Proc.kE,Proc.pm,kk,kh,cg,ke,pm]
theorem tail_bits (R : Run) : GateBits (tailV R) := by
  simp [GateBits,tailV,zeroV]

theorem records_bits (R : Run) : ∀ V ∈ procVs R, GateBits V := by
  intro V hv
  simp only [procVs,List.mem_append] at hv
  rcases hv with hv | hv
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
    exact key_bits R k
  · obtain ⟨rd,hrd,hv⟩ := List.mem_flatMap.1 hv
    simp only [roundVs,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact header_bits R rd
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
      exact entry_bits R rd _ k

def Flags (V : PV) : Prop := ∀ c ∈ Proc.boolCols, V.cell c ≤ 1

theorem key_flags (R : Run) (k : Nat) : Flags (keyV R k) := by
  simp [Flags,Proc.boolCols,Proc.act,Proc.kK,Proc.kH,Proc.kE,Proc.kl,Proc.zk,Proc.lastf,Proc.cS,Proc.cR,Proc.cL,Proc.ok,Proc.za,Proc.pm,Proc.le,Proc.cg,PV.cell,keyV,zeroV,b2n_le]

theorem header_flags (R : Run) (rd : RoundD) : Flags (hdrV R rd) := by
  simp [Flags,Proc.boolCols,Proc.act,Proc.kK,Proc.kH,Proc.kE,Proc.kl,Proc.zk,Proc.lastf,Proc.cS,Proc.cR,Proc.cL,Proc.ok,Proc.za,Proc.pm,Proc.le,Proc.cg,PV.cell,hdrV,baseV,zeroV,b2n_le]

theorem entry_flags (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat) : Flags (entV R rd es i) := by
  simp [Flags,Proc.boolCols,Proc.act,Proc.kK,Proc.kH,Proc.kE,Proc.kl,Proc.zk,Proc.lastf,Proc.cS,Proc.cR,Proc.cL,Proc.ok,Proc.za,Proc.pm,Proc.le,Proc.cg,PV.cell,entV,baseV,zeroV,b2n_le]

theorem tail_flags (R : Run) : Flags (tailV R) := by
  simp [Flags,Proc.boolCols,Proc.act,Proc.kK,Proc.kH,Proc.kE,Proc.kl,Proc.zk,Proc.lastf,Proc.cS,Proc.cR,Proc.cL,Proc.ok,Proc.za,Proc.pm,Proc.le,Proc.cg,PV.cell,tailV,zeroV]

theorem padding_flags : Flags padPV := by
  simp [Flags,Proc.boolCols,Proc.act,Proc.kK,Proc.kH,Proc.kE,Proc.kl,Proc.zk,Proc.lastf,Proc.cS,Proc.cR,Proc.cL,Proc.ok,Proc.za,Proc.pm,Proc.le,Proc.cg,PV.cell,padPV,zeroV]

theorem records_flags (R : Run) : ∀ V ∈ procVs R, Flags V := by
  intro V hv
  simp only [procVs,List.mem_append] at hv
  rcases hv with hv | hv
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
    exact key_flags R k
  · obtain ⟨rd,hrd,hv⟩ := List.mem_flatMap.1 hv
    simp only [roundVs,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact header_flags R rd
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
      exact entry_flags R rd _ k

end ZkFormal.NearV3.Candidates.ProcBits
