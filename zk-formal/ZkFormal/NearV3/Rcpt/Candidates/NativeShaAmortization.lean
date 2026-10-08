import ZkFormal.NearV3.Rcpt.Candidates.NativeShortValues
import ZkFormal.Near.Spec.PruneLemmas

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Amortized message cost, retaining the block-padding constant. -/
theorem rowsOf_affine (n : Nat) : 16*ZkFormal.Near.Render.rowsOf n≤5*n+288 := by
  unfold ZkFormal.Near.Render.rowsOf
  omega

private theorem slot_reference (s : Slot) (hw : slotOk s=true) :
    36*(slotVal s).length≤s.valueRef.length := by
  cases s with
  | val v => simp [slotVal,Slot.valueRef,u32,leN_length,sha256]
  | ref n h => simp [slotVal]

/-- Actual occurrence byte charge, written per node to support tree induction. -/
def occurrenceCharge (os : List PTrie) : Nat :=
  (os.map (fun t => (nodeEnc t).length + ((ownVals t).map List.length).sum)).sum

def occurrenceUnits (os : List PTrie) : Nat :=
  (os.map (fun t => 43+36*(ownVals t).length)).sum

private theorem slot_charge (s : Option Slot)
    (hw : (match s with | some v => slotOk v | none => true)=true) :
    36*(optSlotVal s).length ≤ (match s with | none => 0 | some v => v.valueRef.length) := by
  cases s with
  | none => simp [optSlotVal]
  | some s => exact slot_reference s hw

mutual
theorem tree_reference_payment : ∀t : PTrie,t.wf=true →
    occurrenceUnits (occs t)≤occurrenceCharge (occs t)+32
  | .hash _,_ => by simp [occs,occurrenceUnits,occurrenceCharge]
  | .leaf k s m,hw => by
    have hs : slotOk s=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.1.2
    have h := slot_reference s hs
    simp only [occs,occurrenceUnits,occurrenceCharge,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,Nat.add_zero,ownVals,nodeEnc,List.length_append,
      List.length_cons,List.length_nil,u32,u64,leN_length]
    try simp only [u16,u32,u64,optSlotVal] at *
    omega
  | .ext k c m,hw => by
    have hc : c.wf=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.1.2
    have hi := tree_reference_payment c hc
    have hh := ZkFormal.Near.Prune.hashOf_length c hc
    simp only [occs,occurrenceUnits,occurrenceCharge,List.map_cons,List.sum_cons,
      ownVals,List.length_nil,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero,
      nodeEnc,List.length_append,List.length_cons,u32,u64,leN_length,hh]
    simp only [occurrenceUnits,occurrenceCharge,ownVals,nodeEnc,u32,u64,u16,optSlotVal] at hi
    try simp only [u16,u32,u64,optSlotVal] at *
    omega
  | .branch s cs m,hw => by
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hi := kids_reference_payment cs 16 hw.1.2
    have hs := slot_charge s hw.1.1
    cases s with
    | none =>
      simp only [occs,occurrenceUnits,occurrenceCharge,List.map_cons,List.sum_cons,
        ownVals,optSlotVal,List.length_nil,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero,
        nodeEnc,List.length_append,List.length_cons,u16,u64,leN_length]
      simp only [occurrenceUnits,occurrenceCharge,ownVals,nodeEnc,u32,u64,u16,optSlotVal] at hi
      try simp only [u16,u32,u64,optSlotVal] at *
      omega
    | some s =>
      simp only [occs,occurrenceUnits,occurrenceCharge,List.map_cons,List.sum_cons,
        ownVals,optSlotVal,nodeEnc,List.length_append,List.length_cons,List.length_nil,
        u16,u64,leN_length]
      simp only [occurrenceUnits,occurrenceCharge,ownVals,nodeEnc,u32,u64,u16,optSlotVal] at hi
      simp only [optSlotVal] at hs
      try simp only [u16,u32,u64,optSlotVal] at *
      omega
theorem kids_reference_payment : ∀cs : Kids, ∀w, Kids.wf cs w=true →
    occurrenceUnits (kOccs cs)≤occurrenceCharge (kOccs cs)+(Kids.hashes cs).length
  | .nil,_,_ => by simp [kOccs,occurrenceUnits,occurrenceCharge,Kids.hashes]
  | .none cs,w,hw => by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    exact kids_reference_payment cs (w-1) hw.2
  | .some c cs,w,hw => by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    have ht := tree_reference_payment c hw.1.2
    have hr := kids_reference_payment cs (w-1) hw.2
    have hh := ZkFormal.Near.Prune.hashOf_length c hw.1.2
    simp only [kOccs,occurrenceUnits,occurrenceCharge,List.map_append,List.sum_append,
      Kids.hashes,List.length_append,hh]
    unfold occurrenceUnits occurrenceCharge at ht hr
    try simp only [u16,u32,u64,optSlotVal] at *
    omega
end

def occurrenceShaRows (os : List PTrie) : Nat :=
  (os.map (fun t => 2*ZkFormal.Near.Render.rowsOf (nodeEnc t).length +
    hashRows ((ownVals t).map List.length))).sum

theorem occurrence_rows_payment (os : List PTrie) :
    344*occurrenceShaRows os≤215*occurrenceCharge os+288*occurrenceUnits os := by
  induction os with
  | nil => simp [occurrenceShaRows,occurrenceCharge,occurrenceUnits]
  | cons t os ih =>
    have hn := rowsOf_affine (nodeEnc t).length
    have hv := hashRows_bound ((ownVals t).map List.length)
    have hc := List.length_filter_le (fun n : Nat => decide (n<43)) ((ownVals t).map List.length)
    simp only [List.length_map] at hc
    unfold shortCount at hv
    simp only [occurrenceShaRows,occurrenceCharge,occurrenceUnits,List.map_cons,List.sum_cons] at *
    omega

theorem occurrence_charge_eq (t : PTrie) : occurrenceCharge (occs t)=unfoldedBytesT t := by
  unfold unfoldedBytesT NearSpecV3.valsOf
  have enc : NearSpecV3.nodeEnc = nodeEnc := rfl
  have own : NearSpecV3.ownVals = ownVals := funext Assembly.native_ownVals_eq
  simp only [Assembly.native_occs_eq,own,enc]
  generalize occs t = os
  induction os with
  | nil => simp [occurrenceCharge]
  | cons t os ih =>
    simp only [occurrenceCharge,List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,
      List.sum_append] at *
    omega

/-- Structural amortization pays all per-message overhead from actual value
references and child hashes, with one fixed root allowance. Empty values are
conservatively hashed in this bound although actual VPRE omits them. -/
theorem tree_sha_amortized (t : PTrie) (hw : t.wf=true) :
    344*occurrenceShaRows (occs t)≤503*unfoldedBytesT t+9216 := by
  have hp := occurrence_rows_payment (occs t)
  have hr := tree_reference_payment t hw
  rw [occurrence_charge_eq] at hp hr
  omega

theorem forest_sha_amortized (ts : List PTrie) (hw : ∀t∈ts,t.wf=true) :
    344*(ts.map (fun t => occurrenceShaRows (occs t))).sum≤
      503*Assembly.preBytes ts+9216*ts.length := by
  induction ts with
  | nil => simp [Assembly.preBytes]
  | cons t ts ih =>
    have ht := tree_sha_amortized t (hw t (by simp))
    have hi := ih (fun t ht => hw t (by simp [ht]))
    simp only [List.map_cons,List.sum_cons,Assembly.preBytes,List.length_cons,
      Nat.mul_add,Nat.mul_one] at *
    omega

/-- Numeric bound for actual accepted prestate occurrence encodings, hashing
nodes twice and values once. Final updated post serializations are separate. -/
theorem accepted_forest_sha_bound {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ()) :
    ∃m : Assembly.MainExecutionV3, ∃steps : List Assembly.ImplicitStepV3, ∃last : Bytes,
      m.NativeValid k w ∧
      Assembly.ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      ((m.pre::steps.map Assembly.ImplicitStepV3.pre).map
        (fun t => occurrenceShaRows (occs t))).sum≤2925275 := by
  obtain ⟨m,steps,last,hm,_,hv,_,hs,_,hgood⟩ := Assembly.checkD0a_native_trace hk hw hc
  have hb := Assembly.checkD0a_preBytes hk hw hc hm hv
  have hp := forest_sha_amortized (m.pre::steps.map Assembly.ImplicitStepV3.pre) hgood
  simp only [List.length_cons,List.length_map] at hp
  unfold B0 at hb
  exact ⟨m,steps,last,hm,hv,by omega⟩

end ZkFormal.NearV3.Rcpt.Candidates
