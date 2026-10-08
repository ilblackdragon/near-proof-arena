import ZkFormal.NearV3.Candidates.ShaHeight.Packed
import ZkFormal.NearV3.Candidates.NativeShaBinBalance

namespace ZkFormal.NearV3.Candidates.PackedShaBins
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Rcpt.Candidates

private def select (f : Nat→Trace Fp) : Trace Fp :=
  ⟨fun t=>(f t).log t,fun t r c=>(f t).cell t r c⟩

private theorem select_eval (f : Nat→Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (select f) t r pub=e.eval (f t) t r pub := by
  unfold Expr.eval
  congr 1

private theorem select_count (f : Nat→Trace Fp) (is : List Interaction)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount is (select f) t pub bus send msg=tableBusCount is (f t) t pub bus send msg := by
  have h:=HorizontalTraffic.count_map id is (select f) (f t) t pub bus send msg rfl
    (by intro r i hi e he; exact select_eval f t r pub e)
  simpa only [show HorizontalTraffic.mapI id=id from funext HorizontalTraffic.mapI_id,List.map_id] using h

private theorem select_local (T : Air.Table) (f : Nat→Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal T (f t) t pub) : TableLocal T (select f) t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rw [select_eval]
    exact h.constr r hr e he
  · intro r hr i hi b hb
    rw [select_eval]
    exact h.bits r hr i hi b hb

/-- Every allocated SHA bin uses the same log-22 clock and width-512 renderer. -/
def trace (bins : List (List Sha.Gen.Msg)) : Trace Fp :=
  select (fun t=>ShaHeight.packedTrace (bins.getD t []))

theorem clock (bins : List (List Sha.Gen.Msg)) (t : Nat) : (trace bins).log t=22 := rfl

private theorem eval_bin (bins : List (List Sha.Gen.Msg)) (t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (trace bins) t r pub=e.eval (ShaHeight.packedTrace (bins.getD t [])) t r pub :=
  select_eval _ t r pub e

private theorem packed_bin_count (bins : List (List Sha.Gen.Msg)) (is : List Interaction)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount is (trace bins) t pub bus send msg=
      tableBusCount is (ShaHeight.packedTrace (bins.getD t [])) t pub bus send msg :=
  select_count _ is t pub bus send msg

private theorem honest_bin_count (bins : List (List Sha.Gen.Msg)) (is : List Interaction)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount is (Sha.honestTrace (bins.getD t [])) t pub bus send msg=
      tableBusCount is (shaBinTrace bins) t pub bus send msg :=
  (select_count (fun t=>Sha.honestTrace (bins.getD t [])) is t pub bus send msg).symm

theorem complete (bins : List (List Sha.Gen.Msg)) (t : Nat) (pub : List Fp)
    (hok : Sha.MsgsOk (bins.getD t [])) :
    TableLocal (ShaCarryKinds.table B_BYTES B_DIGEST) (trace bins) t pub :=
  select_local _ _ t pub (ShaHeight.packed_local (bins.getD t []) hok t B_BYTES B_DIGEST pub)

theorem count (bins : List (List Sha.Gen.Msg)) (t : Nat) (pub : List Fp)
    (hok : Sha.MsgsOk (bins.getD t [])) (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions (trace bins) t pub bus send msg=
      tableBusCount (Sha.Table.interactions B_BYTES B_DIGEST) (shaBinTrace bins) t pub bus send msg := by
  rw [packed_bin_count,ShaHeight.packed_count _ hok,honest_bin_count]

/-- Physical union count for packed tables; all bins share byte/digest buses. -/
def unionCount (bins : List (List Sha.Gen.Msg)) (pub : List Fp) (ts : List Nat)
    (send : Bool) (bus : Nat) (msg : List Fp) : Nat :=
  ts.foldr (fun t total=>tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
    (trace bins) t pub bus send msg+total) 0

theorem union_count (bins : List (List Sha.Gen.Msg)) (pub : List Fp) (ts : List Nat)
    (hok : ∀t∈ts,Sha.MsgsOk (bins.getD t [])) (send : Bool) (bus : Nat) (msg : List Fp) :
    unionCount bins pub ts send bus msg=shaUnionCount (shaBinTrace bins) pub ts send bus msg := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [unionCount,List.foldr_cons,shaUnionCount]
    rw [count bins t pub (hok t (by simp)) bus send msg]
    change shaCountAt (shaBinTrace bins) pub t send bus msg + _ = _
    rw [show ts.foldr _ 0=shaUnionCount (shaBinTrace bins) pub ts send bus msg from
      ih (fun u hu=>hok u (by simp [hu]))]

end ZkFormal.NearV3.Candidates.PackedShaBins
