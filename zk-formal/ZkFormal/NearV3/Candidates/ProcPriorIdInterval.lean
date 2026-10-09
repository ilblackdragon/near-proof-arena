import ZkFormal.NearV3.Candidates.ProcPriorStageOrder
import ZkFormal.NearV3.Candidates.ProcPriorVerticalIdRows
namespace ZkFormal.NearV3.Candidates.ProcPriorIdInterval
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem last_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (stage 1)=1)
    (hn:cv tr t (r+1) (stage 1)=1) :cv tr t r last=0 := by
  have hb:=hL.bool (show r<tr.height t by omega) (ProcPriorVerticalMemorySound.window_member
    (Table.boolC last) (by simp [windows]))
  by_cases hz:cv tr t r last=0
  · exact hz
  · have hl:cv tr t r last=1:=by omega
    have ha:=ProcPriorStageOrder.advance hL hr hl 1 (by decide)
    simp only [Nat.reduceAdd] at ha
    have hp:=ProcPriorStageOrder.partition hL hr
    omega

theorem rank (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) :cv tr t r (stage 1)=1 ↔ ProcPriorStageOrder.rank tr t r=1 := by
  have hp:=ProcPriorStageOrder.partition hL hr
  unfold ProcPriorStageOrder.rank
  omega

theorem stage_interval (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    {a b q:Nat} (ha:a≤q) (hq:q≤b) (hb:b<tr.height t)
    (hsa:cv tr t a (stage 1)=1) (hsb:cv tr t b (stage 1)=1) :cv tr t q (stage 1)=1 := by
  have hlo:=ProcPriorStageOrder.monotone hL ha (by omega)
  have hhi:=ProcPriorStageOrder.monotone hL hq hb
  have hea:=(rank hL (show a<tr.height t by omega)).mp hsa
  have heb:=(rank hL hb).mp hsb
  exact (rank hL (by omega)).mpr (by omega)

theorem active_interval (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    {a b:Nat} (hab:a≤b) (hb:b<tr.height t)
    (hsa:cv tr t a (stage 1)=1) (hsb:cv tr t b (stage 1)=1)
    (ha:cv tr t b ProcPriorIdTable.act=1) :cv tr t a ProcPriorIdTable.act=1 := by
  induction b with
  | zero=>have he:a=0:=by omega
          subst a;exact ha
  | succ b ih=>
    by_cases he:a=b+1
    · subst a;exact ha
    · have hs:=stage_interval hL (show a≤b by omega) (show b≤b+1 by omega) hb hsa hsb
      have hl:=last_zero hL hb hs hsb
      have hp:=ProcPriorIdSoundRows.active_prev (ProcPriorVerticalIdRows.row_local hL hb hs hl) hb ha
      exact ih (by omega) (by omega) hs hp
end ZkFormal.NearV3.Candidates.ProcPriorIdInterval
