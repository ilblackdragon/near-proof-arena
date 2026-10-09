import ZkFormal.NearV3.Candidates.ProcCodecPriorReadTraffic
import ZkFormal.NearV3.Candidates.ProcCodecPriorReadCells
import ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecPriorReadRecord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPhysicalPadding
open ProcPriorCodecSideCarry ProcPriorCodecNativeHash SchedSetAll

def message (tau k v : Nat) : List Fp :=
  [Fp.ofNat tau,Fp.ofNat k,Fp.ofNat (v%16777216),Fp.ofNat (if 16777216≤v then 1 else 0)]

theorem record (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (t : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t (5+24*k+8*f+g) pub 68 false =
      if f=2 ∧ g=2 then
        [message R.tau k (ProcCodecPriorReadCells.prior I present k)] else [] := by
  rw [ProcCodecPriorReadTraffic.codec_row]
  change List.replicate (if cells out.rows (5+24*k+8*f+g) fA*cells out.rows (5+24*k+8*f+g) e2=1 then 1 else 0)
    [cells out.rows (5+24*k+8*f+g) tau,cells out.rows (5+24*k+8*f+g) kidx,
     cells out.rows (5+24*k+8*f+g) apR,cells out.rows (5+24*k+8*f+g) bigR]=_
  have hl:=generated_length I R present vidV gb fwd out h
  have hlt:5+24*k+8*f+g<out.rows.size := by omega
  rw [ProcCodecPhysicalRows.active_cells out.rows _ hlt]
  dsimp only
  obtain ⟨hfa,h2,hidx,hv⟩:=ProcCodecPriorReadCells.position I R present vidV gb fwd out h k f g hk hf hg
  simp only [hfa,h2,hidx]
  have hz:Fp.ofNat 0=0 := rfl
  have ho:Fp.ofNat 1=1 := rfl
  by_cases hs:f=2 ∧ g=2
  · have hab:=hv hs
    simp only [if_pos hs,if_pos hs.1,ho,Lean.Grind.Semiring.one_mul,ite_true,List.replicate_one]
    have hi:=ProcCodecGeneratedInstance.generated I R present vidV gb fwd out h
      out.rows[5+24*k+8*f+g]! (by apply Array.mem_toList_iff.mpr; rw [getElem!_pos out.rows _ hlt]; exact Array.getElem_mem hlt)
    have ht:=hi tau (by decide +kernel)
    have ht' : out.rows[5+24*k+8*f+g]![tau]! =R.tau := by
      rw [ht]
      simp [instanceValue,instanceCells,lookup,tau,pres,vid,act,nn,NN,base,fair,itz,zt]
    simp only [ht',hab.1,hab.2,message]
  · simp only [ite_eq_right hs,hz,Lean.Grind.Semiring.mul_zero,
      show (0:Fp)≠1 by decide +kernel,ite_false,List.replicate_zero]
end ZkFormal.NearV3.Candidates.ProcCodecPriorReadRecord
