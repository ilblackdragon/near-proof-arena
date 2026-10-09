import ZkFormal.NearV3.Assembly.UpsertShaDigests

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- Fill retained renderer root fields from the actual native input/output. -/
def nativeRootBase (base : Render.UpsInst) (root : PTrie) (run : TreeRun) : Render.UpsInst :=
  {base with mid:=root.hashOf.map UInt8.toNat,post:=run.output.hashOf.map UInt8.toNat}

def rootedNativeInstance (recordId : PTrie→Nat) (base : Render.UpsInst) (root : PTrie)
    (run : TreeRun) (v : Bytes) (Qs : List Render.UpsPartI) : Render.UpsInst :=
  nativeInstance recordId (nativeRootBase base root run) root run v Qs

@[simp] theorem rootedNativeInstance_roots (recordId : PTrie→Nat) (base : Render.UpsInst)
    (root : PTrie) (run : TreeRun) (v : Bytes) (Qs : List Render.UpsPartI) :
    (rootedNativeInstance recordId base root run v Qs).mid=root.hashOf.map UInt8.toNat ∧
    (rootedNativeInstance recordId base root run v Qs).post=run.output.hashOf.map UInt8.toNat :=
  ⟨rfl,rfl⟩

@[simp] theorem rootedNativeInstance_tau (recordId : PTrie→Nat) (base : Render.UpsInst)
    (root : PTrie) (run : TreeRun) (v : Bytes) (Qs : List Render.UpsPartI) :
    (rootedNativeInstance recordId base root run v Qs).tau=base.tau := rfl

@[simp] theorem rootedNativeInstance_nQ (recordId : PTrie→Nat) (base : Render.UpsInst)
    (root : PTrie) (run : TreeRun) (v : Bytes) (Qs : List Render.UpsPartI) :
    nQ (rootedNativeInstance recordId base root run v Qs)=Qs.length := by
  simp [rootedNativeInstance,nativeInstance,signedInstance,positionedInstance,nQ]

/-- Root digest consumed by the rooted instance has a concrete honest SHA job
at exactly its renderer's final node index. -/
theorem rootedNativeInstance_digest (recordId : PTrie→Nat) (baseI : Render.UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→Render.UpsPartI) {Qs : List Render.UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) :
    let I := rootedNativeInstance recordId baseI root run v Qs
    [upsertJobId I.tau (nQ I),(nodeEnc run.output).length]++I.post ∈
      ZkFormal.Sha.Gen.expectedDigests (upsertShaJobs I.tau v run) := by
  dsimp only
  rw [rootedNativeInstance_tau,rootedNativeInstance_nQ,
    encodeNativeParts_length recordId hr base he]
  exact upsertShaJobs_root_digest hr baseI.tau

/-- Every rooted encoded part retains the exact concrete SHA preimage. -/
theorem rootedNativeInstance_part_shaJob (recordId : PTrie→Nat) (baseI : Render.UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→Render.UpsPartI) {Qs : List Render.UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    ∃ M, (upsertShaJobs baseI.tau v run)[k+1]?=some M ∧
      M.id=upsertJobId baseI.tau (k+1) ∧
      M.bytes=(part (rootedNativeInstance recordId baseI root run v Qs) k).q :=
  nativeInstance_part_shaJob_exact recordId (nativeRootBase baseI root run) hr hw base he k hk

end ZkFormal.NearV3.Assembly
