import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundPublicId
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

theorem receive_same : ProcPriorCodecActual.interactions[7]! =Codec.interactions[7]! := rfl
theorem send_same : ProcPriorCodecActual.interactions[8]! =Codec.interactions[8]! := rfl

theorem receive_member : ProcPriorCodecActual.interactions[7]!∈ProcPriorCodecActual.interactions :=
  by
    rw [getElem!_pos _ _ (by decide)]
    exact List.getElem_mem (by decide)
theorem send_member : ProcPriorCodecActual.interactions[8]!∈ProcPriorCodecActual.interactions :=
  by
    rw [getElem!_pos _ _ (by decide)]
    exact List.getElem_mem (by decide)

/-- Every corrected sender byte retains the original authenticated SDL
receive/send pair. Its publicID request is downstream of this authentication. -/
theorem sender_row {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hS:cv tr t r fS=1) :
    (ProcPriorCodecActual.interactions[7]!).multNat tr t r pub=1 ∧
    (ProcPriorCodecActual.interactions[8]!).multNat tr t r pub=1 ∧
    (ProcPriorCodecActual.interactions[7]!).msgVal tr t r pub=
      [cv tr t r tau,cv tr t r klo,cv tr t r khi,cv tr t r g,cv tr t r bpost].map Fp.ofNat ∧
    (ProcPriorCodecActual.interactions[8]!).msgVal tr t r pub=
      [cv tr t r tau+1,cv tr t r klo,cv tr t r khi,cv tr t r g,cv tr t r bpost].map Fp.ofNat := by
  have hk:=ProcPriorCodecSoundGeometry.kinds hL hr
  have hR:cv tr t r fR=0 := by omega
  have ho:oE.eval tr t r pub=Fp.ofNat (cv tr t r g) := ev_of (by
    simp only [oE,zev_add,zev_smul,zev_c,cur_cv,hR]
    omega)
  rw [receive_same,send_same,i7_def,i8_def]
  refine ⟨?_,?_,?_,?_⟩
  · apply mult_of (e:=.add (c fS) (c fR)) rfl
    simp only [zev_add,zev_c,cur_cv,hS,hR]
    rfl
  · apply mult_of (e:=.add (c fS) (c fR)) rfl
    simp only [zev_add,zev_c,cur_cv,hS,hR]
    rfl
  · simp only [Interaction.msgVal,List.map_cons,List.map_nil,ev_c,ho]
  · have ht:(Expr.add (c tau) (k 1)).eval tr t r pub=Fp.ofNat (cv tr t r tau+1) := ev_of (by
      simp only [zev_add,zev_c,zev_k,cur_cv]
      omega)
    simp only [Interaction.msgVal,List.map_cons,List.map_nil,ev_c,ho,ht]

/-- Actual corrected start geometry provides all eight live SDL receives;
no independent sender-phase list or room bound is supplied. -/
theorem start_receives {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r rs=1) : ∀i,i<8→
    r+i<tr.height t ∧ (ProcPriorCodecActual.interactions[7]!).multNat tr t (r+i) pub=1 ∧
    (ProcPriorCodecActual.interactions[7]!).msgVal tr t (r+i) pub=
      [cv tr t (r+i) tau,cv tr t (r+i) klo,cv tr t (r+i) khi,i,cv tr t (r+i) bpost].map Fp.ofNat := by
  intro i hi
  obtain ⟨hri,hS,hg,_,_⟩:=ProcPriorCodecSoundGeometry.sender_walk hL hr hs i hi
  have hh:=sender_row hL hri hS
  exact ⟨hri,hh.1,by simpa only [hg] using hh.2.2.1⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlRows
