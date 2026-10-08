import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Sched ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private def digestInteractions (xs : List Interaction) : List Interaction :=
  xs.filter (fun x=>decide (x.bus=B_DIGEST ∧ x.send=false))

private theorem row_filtered (xs : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    Near.rowTraffic xs tr t r pub B_DIGEST false=
      (digestInteractions xs).flatMap (fun x=>List.replicate (x.multNat tr t r pub) (x.msgVal tr t r pub)) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    by_cases hb:x.bus=B_DIGEST <;> by_cases hs:x.send=false
    all_goals simp [Near.rowTraffic,digestInteractions,hb,hs] at ih ⊢
    all_goals exact ih

/-- All Codec repairs preserve the sole original DIGEST receiver exactly. -/
theorem repaired_digest_interactions :
    digestInteractions ProcPriorCodecActual.table.interactions=digestInteractions Codec.interactions := by
  decide +kernel

theorem repaired_digest_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    Near.rowTraffic ProcPriorCodecActual.table.interactions tr t r pub B_DIGEST false=
      Near.rowTraffic Codec.interactions tr t r pub B_DIGEST false := by
  rw [row_filtered,row_filtered,repaired_digest_interactions]

theorem repaired_digest_count (tr : Trace Fp) (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions tr t pub B_DIGEST false msg=
      tableBusCount Codec.interactions tr t pub B_DIGEST false msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  simp only [repaired_digest_row]

end ZkFormal.NearV3.Assembly.CodecDigest
