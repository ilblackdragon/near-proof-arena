import ZkFormal.NearV3.Render.Ups.NativePartPlan
import ZkFormal.NearV3.Render.Ups.EncodedSourceBytes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

/-- The actual per-index encoded part, with its native source/output witness. -/
theorem encodeTreeParts_at (base : Nat→UpsPartI) :
    ∀ (parts : List TreePart) (offset : Nat) (Qs : List UpsPartI) (k : Nat) (part : TreePart),
    encodeTreeParts base offset parts=some Qs → parts[k]?=some part →
    ∃ Q, Qs[k]?=some Q ∧ encodeTreePart (base (offset+k)) part=some Q
  | [], _, _, _, _, _, hp => by simp at hp
  | p::ps, offset, Qs, k, part, he, hp => by
    cases hQ : encodeTreePart (base offset) p with
    | none => simp [encodeTreeParts,hQ] at he
    | some Q =>
      cases hQs : encodeTreeParts base (offset+1) ps with
      | none => simp [encodeTreeParts,hQ,hQs] at he
      | some tail =>
        simp [encodeTreeParts,hQ,hQs] at he
        subst Qs
        cases k with
        | zero => simp at hp; subst part; exact ⟨Q,rfl,by simpa using hQ⟩
        | succ k =>
          obtain ⟨R,hr,henc⟩ := encodeTreeParts_at base ps (offset+1) tail k part hQs hp
          exact ⟨R,hr,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using henc⟩

/-- Per-index metadata constructor; the fallback is unreachable for a live emitted part. -/
def nativePartBase (recordId : PTrie→Nat) (root : PTrie) (run : TreeRun)
    (base : Nat→UpsPartI) (k : Nat) : UpsPartI :=
  match run.parts[k]? with
  | none => base k
  | some part => positionedPart recordId (fdepth root [0,15]-1) run k part (base k)

def encodeNativeParts (recordId : PTrie→Nat) (root : PTrie) (run : TreeRun)
    (base : Nat→UpsPartI) : Option (List UpsPartI) :=
  encodeTreeParts (nativePartBase recordId root run base) 0 run.parts

/-- Native success constructs the whole positional byte table; no encoding-success premise. -/
theorem encodeNativeParts_total (recordId : PTrie→Nat) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (base : Nat→UpsPartI) :
    ∃ Qs, encodeNativeParts recordId root run base=some Qs ∧
      Qs.map UpsPartI.kind=run.parts.map (fun p => p.kind.ix) ∧ Qs.length=run.parts.length :=
  encodeTreeParts_total _ run.parts 0 (traceUpsert_nodeParts root [0,15] v run hr)

/-- Every live part of the executable whole-table encoding has a full native plan proof
once its ordinary byte semantics have been constructed. -/
theorem encodedNativeParts_plan (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeNativeParts recordId root run base=some Qs)
    (hl : Qs.length=run.parts.length)
    (hb : ∀ Q∈Qs,ByteInput (positionedInstance recordId baseI root run v Qs) Q)
    (k : Nat) (hk : k<Qs.length) :
    PartOk (positionedInstance recordId baseI root run v Qs) k (Qs.getD k default) := by
  have hparts : k<run.parts.length := by omega
  let part := run.parts[k]'hparts
  have hp : run.parts[k]?=some part := List.getElem?_eq_getElem hparts
  obtain ⟨Q,hQ,henc⟩ := encodeTreeParts_at (nativePartBase recordId root run base) run.parts 0 Qs k part he hp
  have hbase : nativePartBase recordId root run base (0+k)=
      positionedPart recordId (fdepth root [0,15]-1) run k part (base k) := by simp [nativePartBase,hp]
  rw [hbase] at henc
  have hdata := hb Q (List.mem_of_getElem? hQ)
  have hout := encoded_nativePart_ok recordId baseI hr Qs k part hp (base k) Q henc hdata
  simpa only [List.getD_eq_getElem?_getD,hQ,Option.getD_some] using hout
end ZkFormal.NearV3.Render.UpsGen
