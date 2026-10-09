import NearSpecV3.Logged.WasmHR

/-! # The seven storage host functions: mirror = original (`HP_hostCallL`) -/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

set_option maxHeartbeats 2000000 in
theorem HP_yieldCreate (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (a : Vector Nat 9) :
    HP σ g t (yieldCreateWithIdHL a) (yieldCreateWithIdH a) := by
  unfold yieldCreateWithIdHL yieldCreateWithIdH
  hp

set_option maxHeartbeats 2000000 in
theorem HP_storage_write (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "storage_write" = some y) (hx : hostCall "storage_write" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_1] at hy; rw [hostCall.eq_35] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  hp

theorem HP_storage_read (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "storage_read" = some y) (hx : hostCall "storage_read" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_2] at hy; rw [hostCall.eq_36] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  hp

theorem HP_storage_remove (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "storage_remove" = some y) (hx : hostCall "storage_remove" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_3] at hy; rw [hostCall.eq_37] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  hp

theorem HP_storage_has_key (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "storage_has_key" = some y) (hx : hostCall "storage_has_key" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_4] at hy; rw [hostCall.eq_38] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  hp


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem HP_yield_create_with_id (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "promise_yield_create_with_id" = some y) (hx : hostCall "promise_yield_create_with_id" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_5] at hy; rw [hostCall.eq_64] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  refine HP_bind (HP_liftH (by cr) (by cr) ht) ?_
  intro a t' ht'
  exact HP_yieldCreate hσ t' ht' a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem HP_yield_resume (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "promise_yield_resume" = some y) (hx : hostCall "promise_yield_resume" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_6] at hy; rw [hostCall.eq_62] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem HP_yield_resume_with_yield_id (hσ : StoreAgrees σ g) (t : St) (ht : StOK σ t) (y : HMM Unit) (x : HM Unit)
    (hy : hostCallL "promise_yield_resume_with_yield_id" = some y) (hx : hostCall "promise_yield_resume_with_yield_id" = some x) : HP σ g t y x := by
  rw [hostCallL.eq_7] at hy; rw [hostCall.eq_68] at hx
  have hy2 := Option.some.inj hy; have hx2 := Option.some.inj hx; clear hy hx; subst hy2 hx2
  hp


end
end NearSpecV3.Logged.W
