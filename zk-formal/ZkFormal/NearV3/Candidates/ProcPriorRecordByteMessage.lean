import ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordByteMessage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable

def offsetNat (tr:Trace Fp) (t r:Nat):Nat :=
  8*(cv tr t r receiver+2*cv tr t r amount)+3*(cv tr t r midLimb+2*cv tr t r topLimb)

theorem message (tr:Trace Fp) (t r j:Nat) (pub:List Fp) (hj:j<3) :
    (ProcPriorRecordPhysicalBytes.verticalByte j).msgVal tr t r pub=
      [Fp.ofNat (cv tr t r tau),Fp.ofNat (cv tr t r record),
       Fp.ofNat (offsetNat tr t r+j),Fp.ofNat (cv tr t r (byte0+j))] := by
  have hc (x:Nat):tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  have ck (n:Nat):(n:Fp)=Fp.ofNat n:=rfl
  have casesj:j=0 ∨ j=1 ∨ j=2:=by omega
  rcases casesj with rfl|rfl|rfl <;>
    simp [ProcPriorRecordPhysicalBytes.verticalByte,ProcPriorRecordLinear.interactions,
      ProcPriorRecordTable.interactions,ProcPriorVertical4Linear.interaction,
      Interaction.msgVal,offset,offsetNat,Expr.eval,c,k,ProcPriorVertical4Linear.expression,Expr.evalWith,rowEnv,byte0,byte1,byte2,
      hc,ck 8,ck 3,ck 2,ck 1,ZkFormal.Near.ofNat_add',ZkFormal.Near.ofNat_mul']
theorem offset_bound {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (j:Nat) (hj:j<3) (ht:j=2→cv tr t r topLimb=0) :
    offsetNat tr t r+j<24 := by
  have hw:=ProcPriorRecordGeometry.words_bound hL hr hs
  have he:=ProcPriorRecordGeometry.limbs_eq hL hr hs
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  unfold offsetNat
  by_cases hj2:j=2
  · have hz:=ht hj2
    omega
  · omega

end ZkFormal.NearV3.Candidates.ProcPriorRecordByteMessage
