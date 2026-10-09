import ZkFormal.NearV3.Candidates.ProcCodecPublicIdTraffic
import ZkFormal.NearV3.Candidates.ProcCodecPublicIdCells
import ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecPublicIdRecord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPhysicalPadding
open ProcPriorCodecSideCarry ProcPriorCodecNativeHash SchedSetAll

def idMessage (tau sender id : Nat) : List Fp :=
  ProcCodecPublicIdTraffic.message (Fp.ofNat tau) (Fp.ofNat sender)
    (fun i=>Fp.ofNat ((bytesLE id 8).getD i 0))

theorem record (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (t : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t (5+24*k+8*f+g) pub 70 true =
      if f=0 ∧ g=0 ∧ k%R.n=0 then
        [idMessage R.tau (k/R.n) (I.ids.getD (k/R.n) 0)] else [] := by
  rw [ProcCodecPublicIdTraffic.codec_row]
  change List.replicate (if cells out.rows (5+24*k+8*f+g) rs*cells out.rows (5+24*k+8*f+g) nzb=1 then 1 else 0)
    (ProcCodecPublicIdTraffic.message (cells out.rows (5+24*k+8*f+g) tau)
      (cells out.rows (5+24*k+8*f+g) srcC) (fun i=>cells out.rows (5+24*k+8*f+g) (prbit i)))=_
  have hl:=generated_length I R present vidV gb fwd out h
  have hlt:5+24*k+8*f+g<out.rows.size := by omega
  rw [ProcCodecPhysicalRows.active_cells out.rows _ hlt]
  dsimp only
  obtain ⟨hsrc,hrs,hnzb⟩:=ProcCodecPublicIdCells.position I R present vidV gb fwd out h k f g hk hf hg
  simp only [hrs,hnzb,hsrc]
  have hz:Fp.ofNat 0=0 := rfl
  have ho:Fp.ofNat 1=1 := rfl
  by_cases hs:f=0 ∧ g=0 ∧ k%R.n=0
  · obtain ⟨rfl,rfl,hr⟩:=hs
    simp only [hr,true_and,ite_true,hz,ho,Lean.Grind.Semiring.one_mul,List.replicate_one]
    have hi:=ProcCodecGeneratedInstance.generated I R present vidV gb fwd out h
      out.rows[5+24*k+8*0+0]! (by apply Array.mem_toList_iff.mpr; rw [getElem!_pos out.rows _ hlt]; exact Array.getElem_mem hlt)
    have ht:=hi tau (by decide +kernel)
    have ht' : out.rows[5+24*k+8*0+0]![tau]! =R.tau := by
      rw [ht]
      simp [instanceValue,instanceCells,lookup,tau,pres,vid,act,nn,NN,base,fair,itz,zt]
    rw [ht']
    have hb:∀i<8,out.rows[5+24*k+8*0+0]![prbit i]! =(bytesLE (I.ids.getD (k/R.n) 0) 8).getD i 0 := by
      intro i hi
      simpa only [Nat.zero_add] using (ProcPriorCodecSenderCells.position I R present vidV gb fwd out h k 0 hk (by decide)).2 i hi
    simp only [idMessage,ProcCodecPublicIdTraffic.message,hb 0 (by decide),hb 1 (by decide),hb 2 (by decide),
      hb 3 (by decide),hb 4 (by decide),hb 5 (by decide),hb 6 (by decide),hb 7 (by decide)]
  · simp only [ite_eq_right hs]
    simp only [hz,Lean.Grind.Semiring.mul_zero,show (0:Fp)≠1 by decide +kernel,ite_false,List.replicate_zero]
end ZkFormal.NearV3.Candidates.ProcCodecPublicIdRecord
