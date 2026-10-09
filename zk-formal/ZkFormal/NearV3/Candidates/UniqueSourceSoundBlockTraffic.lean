import ZkFormal.NearV3.Candidates.UniqueSourceSoundBlocks
namespace ZkFormal.NearV3.Candidates.UniqueSourceSoundBlockTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates SrcpV3 DedupProof
open UniqueSourceSoundShadow UniqueSourceSoundSize

theorem row_shadow (tr : Trace Fp) (tt r : Nat) :
    rowSize (shadow tr) tt r=rowSize tr tt r := by
  simp [rowSize,shadow,sz,rt,dup,L,sf,sg,lf]
  rfl

theorem prefix_shadow (tr : Trace Fp) (tt n : Nat) :
    prefixSize (shadow tr) tt n=prefixSize tr tt n := by
  have hh : rowSize (shadow tr) tt=rowSize tr tt := funext (row_shadow tr tt)
  simp only [prefixSize,hh]

/-- The corrected SIZE send is exactly the charge of the same source blocks
used by receipt/hash semantic extraction, not an unrelated prefix witness. -/
theorem chain_traffic {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table 24) tr tt pub)
    {bs : List SrcpB} {stop : Nat} (hs : BlockChain (shadow tr) tt 0 bs stop) :
    (List.range (tr.height tt)).flatMap (fun r=>rowTraffic DedupTable.interactions tr tt r pub B_SIZE true)=
      [Msg.toFp [2,UniqueSourceCharge.size bs]] ∧
    (List.range (tr.height tt)).flatMap (fun r=>rowTraffic DedupTable.interactions tr tt r pub B_SIZE false)=[] := by
  obtain ⟨K,hK,hKH,ha,hp,hsend,hrecv⟩:=UniqueSourceSoundSizeTraffic.size_traffic h
  have hl:=old_local h
  have he : 0<stop ∧ stop≤tr.height tt := hs.bound
  have hlast : tr.cell tt (stop-1) rt=1 ∨ tr.cell tt (stop-1) sg=1 := by
    simpa [shadow,rt,sg,sz] using hs.last_active hl
  have hpad : ∀r,stop≤r→r<tr.height tt→tr.cell tt r rt=0 ∧ tr.cell tt r sg=0 := by
    simpa [shadow,Trace.height,rt,sg,sz] using hs.padding
  have heK : stop=K := by
    apply Nat.le_antisymm
    · apply Classical.byContradiction
      intro hn
      have hh:=hp (stop-1) (by omega) (by omega)
      rcases hlast with hh'|hh' <;> simp_all
    · apply Classical.byContradiction
      intro hn
      have hh:=hpad stop (by omega) (by omega)
      have hac:=ha stop (by omega)
      rcases hac with hh'|hh' <;> simp_all
  have hc:=UniqueSourceSoundBlocks.chain_size hl hs
  have heq : prefixSize (shadow tr) tt K=UniqueSourceCharge.size bs := by
    simpa only [Nat.sub_zero,UniqueSourceSoundBlocks.chargeSpan,Nat.zero_add,heK,prefixSize] using hc
  rw [prefix_shadow] at heq
  exact ⟨by simpa only [heq] using hsend,hrecv⟩
end ZkFormal.NearV3.Candidates.UniqueSourceSoundBlockTraffic
