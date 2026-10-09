import ZkFormal.NearV3.Assembly.WitnessSize
import ZkFormal.NearV3.Public.NativeSourceOverhead

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly

/-- Payload bytes alone, as counted by the current node/value SIZE accumulators. -/
def transitionPayload (t : Transition) : Nat := (t.values.map List.length).sum

def transitionRecordCount (t : Transition) : Nat := t.values.length

def transitions (w : StateWitness) : List Transition := w.main::w.implicit

def witnessPayload (w : StateWitness) : Nat := ((transitions w).map transitionPayload).sum

def witnessRecordCount (w : StateWitness) : Nat := ((transitions w).map transitionRecordCount).sum

private theorem borsh_payload_charge (xs : List Bytes) :
    (xs.map (fun b => (borshBytes b).length)).sum=(xs.map List.length).sum+4*xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,borshBytes,List.length_append,
      u32,leN,List.length_cons,List.length_nil] at *
    omega

/-- Each private stored record has a four-byte length prefix in addition to its
payload. Empty records also pay this prefix. -/
theorem transition_encoding_charge (t : Transition)
    (hb : t.blockHash.length=32) (hp : t.postStateRoot.length=32) :
    (ZkFormal.V3.encodeTransition t).length=
      transitionPayload t+4*transitionRecordCount t+69 := by
  simp only [ZkFormal.V3.encodeTransition,ReexecV3D0.encTr,List.length_append,
    encList,concatAll_size,borsh_payload_charge,hb,hp,
    u8,u32,leN,List.length_cons,List.length_nil,transitionPayload,transitionRecordCount]
  omega

private theorem transitions_charge (ts : List Transition)
    (h : ∀ t∈ts,t.blockHash.length=32 ∧ t.postStateRoot.length=32) :
    (ts.map (fun t => (ZkFormal.V3.encodeTransition t).length)).sum=
      (ts.map transitionPayload).sum+4*(ts.map transitionRecordCount).sum+69*ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := transition_encoding_charge t (h t (by simp)).1 (h t (by simp)).2
    have hi := ih (fun t ht => h t (by simp [ht]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Exact complete witness accounting with the source dictionary vector kept
explicit. No advertised overhead is presumed to cover private record prefixes. -/
theorem witness_encoding_charge (w : StateWitness)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32) :
    (ZkFormal.V3.encodeSW w).length=
      witnessPayload w+4*witnessRecordCount w+
      (encList ZkFormal.V3.encodeEntry w.entries).length+
      w.innerBytes.length+69*w.implicit.length+220 := by
  have hh := transitions_charge (transitions w) ht
  simp only [transitions,List.map_cons,List.sum_cons,List.length_cons] at hh
  simp only [ZkFormal.V3.encodeSW,List.length_append,he,ha,
    encList,concatAll_size,ReexecV3D0.zeros8,ReexecV3D0.sig0,
    u8,u32,leN,List.length_cons,List.length_nil,List.length_replicate,
    witnessPayload,witnessRecordCount,transitions,List.map_cons,List.sum_cons]
  omega

/-- Source SIZE plus its exact deterministic overhead gives the complete formula.
The additional `4*witnessRecordCount` is not included in current payload SIZE. -/
theorem witness_source_charge (w : StateWitness) (N sourceSize : Nat)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (encList ZkFormal.V3.encodeEntry w.entries).length=sourceSize+44*N+4) :
    (ZkFormal.V3.encodeSW w).length=
      witnessPayload w+sourceSize+4*witnessRecordCount w+
      (224+w.innerBytes.length+44*N+69*w.implicit.length) := by
  rw [witness_encoding_charge w he ha ht,hd]
  omega

/-- Exact overhead required when node/value SIZE continue counting payload only.
Its private record-count term must be authenticated separately by candidate AIR. -/
def nativeWitnessOverhead (w : StateWitness) (N : Nat) : Nat :=
  224+w.innerBytes.length+44*N+69*w.implicit.length+4*witnessRecordCount w

/-- A truthful, authenticated overhead gives the desired full encoded-witness
bound. Unlike a bare public u32, this value includes every actual private prefix. -/
theorem authenticated_witness_paid {w : StateWitness} {p : Prep} {N sourceSize : Nat}
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (encList ZkFormal.V3.encodeEntry w.entries).length=sourceSize+44*N+4)
    (hr : Public.RootsSized p) (ho : nativeWitnessOverhead w N<256^4)
    {v : SizeV}
    (hv : SizeWf (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp
      (Public.preparedBytes p (nativeWitnessOverhead w N))) v)
    (hpayload : witnessPayload w≤v.x0+v.x1) (hsource : sourceSize=v.x2)
    (hwrap : nativeWitnessOverhead w N+v.x0+v.x1+v.x2+2^24≤ZkFormal.Algebra.P) :
    (ZkFormal.V3.encodeSW w).length≤8388608 := by
  have hh := hv.tot_le
  rw [Public.prepared_ovhNat p _ hr ho] at hh
  have hb := hh hwrap
  have hc := witness_source_charge w N sourceSize he ha ht hd
  unfold nativeWitnessOverhead at hb
  omega

end ZkFormal.NearV3.Rcpt.Candidates
