import ZkFormal.NearV3.Candidates.ProcScanRequestQuietCells
import ZkFormal.NearV3.Candidates.ProcScanRequestBitCells
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBools
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

private theorem bool_bound (b:Bool) : b2n b≤1 := by cases b <;> decide

theorem low_bits (R:Run)(c:CReq)(rho jj cv i:Nat)(hi:i<6) :
    (row R c rho jj cv)[Dist.bt1 i]! ≤1 := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  simp only [Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0] at hp hf
  have hs:i=0 ∨i=1 ∨i=2 ∨i=3 ∨i=4 ∨i=5:=by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
  · rw [hp.2.2.2.1];exact bool_bound _
  · rw [hp.2.2.2.2.1];exact bool_bound _
  · rw [hp.2.2.2.2.2.1];exact Complete.bit_le _ _
  · rw [hp.2.2.2.2.2.2.1];exact Complete.bit_le _ _
  · rw [hf.1];exact bool_bound _
  · rw [hf.2.2.2.2];exact bool_bound _

theorem kind_columns (R:Run)(c:CReq)(rho jj cv:Nat) :
    ∀col∈[Dist.act,Dist.kP,Dist.kS,Dist.kSh,Dist.kGH,Dist.kC,Dist.zc,Dist.al,
      Dist.e1,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.eI],(row R c rho jj cv)[col]! ≤1 := by
  have hz:=ProcScanRequestQuietCells.zeros R c rho jj cv
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  simp only [Scan.act,Scan.kS] at hc
  simp only [List.forall_mem_cons]
  rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
  simp only [hc.1,h0,hc.2.1,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
  simp

theorem all_columns (R:Run)(c:CReq)(rho jj cv:Nat) :
    ∀col∈Dist.boolCols,(row R c rho jj cv)[col]! ≤1 := by
  simp only [Dist.boolCols,List.forall_mem_append,List.forall_mem_map,List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨kind_columns R c rho jj cv,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · exact fun i hi=>low_bits R c rho jj cv i hi
  · intro i hi;rw [ProcScanRequestQuietCells.unused_bits R c rho jj cv i hi];omega
  · intro i hi
    have h:=(ProcScanRequestBitCells.quotients R c rho jj cv i hi).1
    simp only [Scan.qb0] at h
    rw [h];exact Complete.bit_le _ _
  · intro i hi
    have h:=(ProcScanRequestBitCells.quotients R c rho jj cv i hi).2
    simp only [Scan.qb1] at h
    rw [h];exact Complete.bit_le _ _
  · intro i hi
    have h:=(ProcScanRequestBitCells.remainders R c rho jj cv i hi).1
    simp only [Scan.rb0] at h
    rw [h];exact Complete.bit_le _ _
  · intro i hi
    have h:=(ProcScanRequestBitCells.remainders R c rho jj cv i hi).2
    simp only [Scan.rb1] at h
    rw [h];exact Complete.bit_le _ _

theorem own_columns (R:Run)(c:CReq)(rho jj cv:Nat) :
    ∀col∈Scan.ownBool,(row R c rho jj cv)[col]! ≤1 := by
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  have hf:=ProcScanRequestCells.flags R c rho jj cv
  have hu:=ProcScanRequestQuietCells.uses R c rho jj cv
  simp only [Scan.ownBool,List.forall_mem_cons]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · rw [hc.2.2.1];exact bool_bound _
  · rw [hf.2.1];exact bool_bound _
  · rw [hu.1];exact bool_bound _
  · rw [hu.2];exact bool_bound _
end ZkFormal.NearV3.Candidates.ProcScanRequestBools
