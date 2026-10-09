import ZkFormal.NearV3.Candidates.ProcSound.Rows
import ZkFormal.NearV3.Candidates.ProcBoundaryLocal
import ZkFormal.NearV3.Sched.Link.ProcRows
namespace ZkFormal.NearV3.Candidates.ProcSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched

theorem local_of_table {tr : Trace Fp} {tp : Nat} {pub : List Fp}
    (h : TableLocal ProcBoundaryRepair.table tr tp pub) : PLocal tr tp pub :=
  h.constr

theorem hdrAt_eq (tr : Trace Fp) (tp f i : Nat) : hdrAt tr tp f i=Proc.hdrAt tr tp f i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [hdrAt_succ,Proc.hdrAt_succ,ih]

theorem inst_compat {tr : Trace Fp} {tp f m : Nat} (I : Inst tr tp f m) :
    Proc.Inst tr tp f m := by
  constructor
  · simpa only [HI,Proc.HI,hdrAt_eq] using I.hdr
  · simpa only [BEnd,Proc.BEnd,hdrAt_eq] using I.fin
  · simpa only [hdrAt_eq] using I.first
  · simpa only [hdrAt_eq] using I.chain

/-- Physical candidate legality recovers the existing semantic instance record,
including the header seed binding. Empty instances require no equality to the
next instance's seed. -/
theorem physical_instance {tr : Trace Fp} {tp f : Nat} {pub : List Fp}
    (h : TableLocal ProcBoundaryRepair.table tr tp pub)
    (hf : f<tr.height tp) (hk : cv tr tp f Proc.kK=1) (hc : cv tr tp f Proc.kc=0) :
    ∃ m,Proc.Inst tr tp f m := by
  have hH : tr.height tp≤2^22 := Nat.pow_le_pow_right (by decide) h.log_le
  obtain ⟨m,hI⟩ := inst_exists (local_of_table h) hH hf hk hc
  exact ⟨m,inst_compat hI⟩
end ZkFormal.NearV3.Candidates.ProcSound
