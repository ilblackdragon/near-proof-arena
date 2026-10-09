import ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordPacked
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem top_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ht:cv tr t r topLimb=1) :cv tr t r byte2=0 := by
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs (.mul (c topLimb) (c byte2)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c topLimb) (c byte2))=2013265921*q at hq
  zs hq [ht]
  have hb:=Codec.lt (tr:=tr) (t:=t) r byte2
  omega

/-- Byte bounds turn the packed field equality into a natural24-bit limb. -/
theorem limb (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (g x:Nat) (hx:(g=firstLimb ∧ x=lo) ∨ (g=midLimb ∧ x=mid) ∨ (g=topLimb ∧ x=hi))
    (hg:cv tr t r g=1)
    (h0:cv tr t r byte0<256) (h1:cv tr t r byte1<256) (h2:cv tr t r byte2<256) :
    cv tr t r x=cv tr t r byte0+256*cv tr t r byte1+65536*cv tr t r byte2 ∧
      cv tr t r x<16777216 := by
  have hm:(.mul (c g) (sub (c x) packed))∈constraints:=by
    rcases hx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [constraints]
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs _ hm
  change zev (tenv tr t r pub) (.mul (c g) (sub (c x) packed))=2013265921*q at hq
  zs hq [hg,packed]
  have hb:=Codec.lt (tr:=tr) (t:=t) r x
  have he:cv tr t r x=cv tr t r byte0+256*cv tr t r byte1+65536*cv tr t r byte2:=by omega
  exact ⟨he,by omega⟩

theorem top (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ht:cv tr t r topLimb=1)
    (h0:cv tr t r byte0<256) (h1:cv tr t r byte1<256) :
    cv tr t r hi=cv tr t r byte0+256*cv tr t r byte1 ∧ cv tr t r hi<65536 := by
  have hz:=top_zero hL hr hs ht
  have hl:=limb hL hr hs topLimb hi (by simp) ht h0 h1 (by omega)
  constructor <;> omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordPacked
