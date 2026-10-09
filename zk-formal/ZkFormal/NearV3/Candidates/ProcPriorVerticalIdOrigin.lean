import ZkFormal.NearV3.Candidates.ProcPriorVerticalIdRows
namespace ZkFormal.NearV3.Candidates.ProcPriorVerticalIdOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear ProcPriorVerticalIdRows
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem origin (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 1)=1) (ha:cv tr t r ProcPriorIdTable.act=1)
    (hf:cv tr t r ProcPriorIdTable.found=1) :
    ∃q,q<r ∧ cv tr t q (stage 1)=1 ∧ cv tr t q ProcPriorIdTable.act=1 ∧
      cv tr t q ProcPriorIdTable.isPublic=1 ∧
      cv tr t r ProcPriorIdTable.index=cv tr t q ProcPriorIdTable.ordinal := by
  induction r with
  | zero=>
    have hz:=first_zero hL hr hs hf
    have hh:=hL 0 hr _ (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c first) (k 1))) (by simp [windows]))
    have hc:tr.cell t 0 first=0:=by
      rw [←Fp.ofNat_toNat (tr.cell t 0 first)];change Fp.ofNat (cv tr t 0 first)=0;rw [hz];rfl
    change (1:Fp)*(tr.cell t 0 first + -1)=0 at hh
    rw [hc] at hh
    have hn:((1:Fp)*(0+ -1))≠0:=by decide +kernel
    exact (hn hh).elim
  | succ r ih=>
    obtain ⟨hstage,hl⟩:=predecessor hL hr hs hf
    obtain ⟨hactive,hprev⟩:=ProcPriorIdSoundRows.previous (row_local hL hr hstage hl) hr ha hf
    rcases hprev with ⟨hfound,hindex⟩|⟨hpublic,hindex⟩
    · obtain ⟨q,hq,hqs,hqa,hqp,hqi⟩:=ih (by omega) hstage hactive hfound
      exact ⟨q,by omega,hqs,hqa,hqp,hindex.trans hqi⟩
    · exact ⟨r,by omega,hstage,hactive,hpublic,hindex⟩
end ZkFormal.NearV3.Candidates.ProcPriorVerticalIdOrigin
