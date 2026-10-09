import ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
import ZkFormal.NearV3.Candidates.ProcPriorSummary
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordSummarySound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

def word (tr:Trace Fp) (t r:Nat):Nat:=
  cv tr t r lo+16777216*cv tr t r mid+281474976710656*cv tr t r hi

theorem big_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (hm:cv tr t r mid<16777216) (hh:cv tr t r hi<65536) :
    cv tr t r big=0 ↔ cv tr t r mid=0 ∧ cv tr t r hi=0 := by
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int):=rfl
  have hwi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1:=by omega
  have hb:=ProcPriorRecordSound.flag hL hr hs big (by simp)
  constructor
  · intro hz
    obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs
      (.mul (words false) (.mul (.add (c mid) (c hi)) (notE (c big)))) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul (words false) (.mul (.add (c mid) (c hi)) (notE (c big))))=2013265921*q at hq
    zs hq [words,cur,notE,hz]
    rw [hwi] at hq
    constructor <;> omega
  · rintro ⟨hm0,hh0⟩
    obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs
      (.mul (words false) (sub (.mul (.add (c mid) (c hi)) (c bigInv)) (c big))) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul (words false) (sub (.mul (.add (c mid) (c hi)) (c bigInv)) (c big)))=2013265921*q at hq
    zs hq [words,cur,hm0,hh0]
    rw [hwi] at hq
    omega

theorem low_exact (hl:cv tr t r lo<16777216) :
    ProcPriorSummary.low (word tr t r)=cv tr t r lo := by
  unfold ProcPriorSummary.low word
  omega

theorem big_exact (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (hl:cv tr t r lo<16777216) (hm:cv tr t r mid<16777216) (hh:cv tr t r hi<65536) :
    ProcPriorSummary.big (word tr t r)=decide (cv tr t r big=1) := by
  have hz:=big_zero hL hr hs hw hm hh
  have hb:=ProcPriorRecordSound.flag hL hr hs big (by simp)
  unfold ProcPriorSummary.big word
  congr 1
  apply propext
  omega

theorem increase_exact (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (hl:cv tr t r lo<16777216) (hm:cv tr t r mid<16777216) (hh:cv tr t r hi<65536)
    (fair:Nat) :
    (if cv tr t r big=1 then 4500000 else min (cv tr t r lo+fair) 4500000)=
      min (min (word tr t r+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  rw [←ProcPriorSummary.increase_exact]
  unfold ProcPriorSummary.increase
  rw [low_exact hl,big_exact hL hr hs hw hl hm hh]
  simp
end ZkFormal.NearV3.Candidates.ProcPriorRecordSummarySound
