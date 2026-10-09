import ZkFormal.NearV3.Candidates.ProcPriorIdFirstCarry
import ZkFormal.NearV3.Candidates.ProcPriorIdKeyOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorIdFirstOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear ProcPriorVerticalIdRows
open ProcPriorIdKeyOrigin (packed)
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem origin (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 1)=1) (ha:cv tr t r ProcPriorIdTable.act=1)
    (hf:cv tr t r ProcPriorIdTable.found=1) :
    ∃q,q<r ∧ cv tr t q (stage 1)=1 ∧ cv tr t q ProcPriorIdTable.act=1 ∧
      cv tr t q ProcPriorIdTable.isPublic=1 ∧ cv tr t q ProcPriorIdTable.found=0 ∧
      cv tr t r ProcPriorIdTable.index=cv tr t q ProcPriorIdTable.ordinal ∧
      packed tr t r=packed tr t q ∧
      cv tr t r ProcPriorIdTable.keyMid=cv tr t q ProcPriorIdTable.keyMid ∧
      cv tr t r ProcPriorIdTable.keyLo=cv tr t q ProcPriorIdTable.keyLo := by
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
    obtain ⟨hactive,hprev⟩:=ProcPriorIdFirstCarry.previous (row_local hL hr hstage hl) hr ha hf
    obtain ⟨ht,hm,hlow⟩:=ProcPriorIdKeyCarry.key_step (row_local hL hr hstage hl) hr ha hf
    have hpack:packed tr t (r+1)=packed tr t r := by
      simpa only [ProcPriorIdTable.top,k,Expr.eval,Expr.evalWith,rowEnv,
        Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt hr,packed] using ht
    rcases hprev with ⟨hfound,hindex⟩|⟨hpublic,hzero,hindex⟩
    · obtain ⟨q,hq,hqs,hqa,hqp,hqzero,hqi,hqt,hqm,hql⟩:=ih (by omega) hstage hactive hfound
      exact ⟨q,by omega,hqs,hqa,hqp,hqzero,hindex.trans hqi,hpack.trans hqt,hm.trans hqm,hlow.trans hql⟩
    · exact ⟨r,by omega,hstage,hactive,hpublic,hzero,hindex,hpack,hm,hlow⟩
end ZkFormal.NearV3.Candidates.ProcPriorIdFirstOrigin
