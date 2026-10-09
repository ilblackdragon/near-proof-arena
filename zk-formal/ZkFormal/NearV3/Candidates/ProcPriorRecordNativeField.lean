import ZkFormal.NearV3.Candidates.ProcPriorRecordNativeWord
import ZkFormal.NearV3.Candidates.ProcPriorRecordFieldBytes
import ZkFormal.NearV3.Candidates.ProcPriorRecordWordLayout
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordNativeField
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open NearSpec.Bandwidth
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

def selected (tr:Trace Fp) (t r:Nat) (link:LinkAllowance):Nat:=
  if cv tr t r sender=1 then link.sender else if cv tr t r receiver=1 then link.receiver else link.allowance

theorem digits (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (link:LinkAllowance)
    (hbytes:∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=
      (link.encode.getD (ProcPriorRecordWordLayout.base tr t r+j) 0).toNat) :
    ∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=ProcPriorRecordLimbs.digit (selected tr t r link) j := by
  have hword:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1:=
    (ProcPriorRecordWordLayout.layout hL hr hs hf 0 (by decide)).2.2.1
  intro j hj
  rw [hbytes j hj]
  by_cases hsend:cv tr t r sender=1
  · have hrecv:cv tr t r receiver=0:=by omega
    have hamt:cv tr t r amount=0:=by omega
    simpa [selected,hsend,ProcPriorRecordWordLayout.base,hrecv,hamt] using ProcPriorRecordFieldBytes.sender link j hj
  · by_cases hrecv:cv tr t r receiver=1
    · have hamt:cv tr t r amount=0:=by omega
      simpa [selected,hsend,hrecv,ProcPriorRecordWordLayout.base,hamt] using ProcPriorRecordFieldBytes.receiver link j hj
    · have hr0:cv tr t r receiver=0:=by omega
      have hamt:cv tr t r amount=1:=by omega
      simpa [selected,hsend,hrecv,ProcPriorRecordWordLayout.base,hr0,hamt] using ProcPriorRecordFieldBytes.allowance link j hj

theorem bound (link:LinkAllowance) (hok:LinkOk link):selected tr t r link<18446744073709551616 := by
  obtain ⟨hs,hr,ha⟩:=hok
  unfold selected
  split <;> try assumption
  split <;> assumption

theorem word (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (link:LinkAllowance) (hok:LinkOk link)
    (hbytes:∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=
      (link.encode.getD (ProcPriorRecordWordLayout.base tr t r+j) 0).toNat) :
    ProcPriorRecordSummarySound.word tr t r=selected tr t r link :=
  ProcPriorRecordNativeWord.word hL hr hs hf _ (bound link hok) (digits hL hr hs hf link hbytes)
/-- Native decoding supplies the u64 bounds. The remaining byte association
premise identifies this one decoded record across all eight physical bytes. -/
theorem decoded (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (bs:NearSpec.Bytes) (st:State)
    (hd:State.decode bs=some st) (link:LinkAllowance) (hm:link∈st.links)
    (hbytes:∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=
      (link.encode.getD (ProcPriorRecordWordLayout.base tr t r+j) 0).toNat) :
    ProcPriorRecordSummarySound.word tr t r=selected tr t r link ∧
      ProcPriorSummary.low (selected tr t r link)=cv tr t (r+2) lo ∧
      ProcPriorSummary.big (selected tr t r link)=decide (cv tr t (r+2) big=1) ∧
      ∀fair:Nat,(if cv tr t (r+2) big=1 then 4500000 else min (cv tr t (r+2) lo+fair) 4500000)=
        min (min (selected tr t r link+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  have hok:LinkOk link:=(ProcPriorDecode.decode_exact bs st hd).2.1 link hm
  exact ⟨word hL hr hs hf link hok hbytes,
    ProcPriorRecordNativeWord.top_summary hL hr hs hf _ (bound link hok) (digits hL hr hs hf link hbytes)⟩

end ZkFormal.NearV3.Candidates.ProcPriorRecordNativeField
