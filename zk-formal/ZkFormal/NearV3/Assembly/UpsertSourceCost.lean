import ZkFormal.NearV3.Render.Ups.TreePartCount
import ZkFormal.NearV3.Spec.Occs
import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.QueueSeed

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def sourceByteCharge (run : TreeRun) : Nat :=
  (run.parts.map (fun p => (nodeEnc p.source).length)).sum

def nodeByteCharge (t : PTrie) : Nat :=
  ((occs t).map (fun t => (nodeEnc t).length)).sum

def kidsByteCharge (cs : Kids) : Nat :=
  ((kOccs cs).map (fun t => (nodeEnc t).length)).sum

@[simp] theorem sourceByteCharge_push (run : TreeRun) (p : TreePart) :
    sourceByteCharge (pushPart run p)=sourceByteCharge run+(nodeEnc p.source).length := by
  simp [sourceByteCharge,pushPart]

theorem leafSplit_source_charge (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    sourceByteCharge (leafSplitRun k s m key v)≤4*(nodeEnc (.leaf k s m)).length := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [sourceByteCharge,terminalRun,wrapRun,pushPart] <;> omega

theorem extSplit_source_charge (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    sourceByteCharge (extSplitRun k c m key v)≤4*(nodeEnc (.ext k c m)).length := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,sourceByteCharge,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [sourceByteCharge,terminalRun,wrapRun,pushPart] <;> omega

mutual
/-- Repeated split sources are charged at most four times. All ancestors are
charged to their actual occurrence; no hash-based deduplication is assumed. -/
theorem traceUpsert_source_charge : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → sourceByteCharge run≤4*nodeByteCharge t
  | .hash _,_,_,_,hr => by simp [traceUpsert] at hr
  | .leaf k s m,key,v,run,hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      subst key
      simp [sourceByteCharge,terminalRun,nodeByteCharge,occs] <;> omega
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run
      simpa [nodeByteCharge,occs] using leafSplit_source_charge k s m key v
  | .ext k c m,key,v,run,hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      have h := extSplit_source_charge k c m key v
      simp only [nodeByteCharge,occs,List.map_cons,List.sum_cons]
      unfold nodeByteCharge at h
      omega
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          have h := traceUpsert_source_charge c _ v inner hc
          simp only [sourceByteCharge_push,nodeByteCharge,occs,List.map_cons,List.sum_cons]
          unfold nodeByteCharge at h
          omega
  | .branch bv cs m,[],v,run,hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    simp [sourceByteCharge,terminalRun,nodeByteCharge,occs] <;> omega
  | .branch bv cs m,n::key,v,run,hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have h := traceKids_source_charge (.branch bv cs m) (n::key) cs n key v inner hc
      simp only [sourceByteCharge_push,nodeByteCharge,occs,List.map_cons,List.sum_cons]
      unfold kidsByteCharge at h
      omega
 theorem traceKids_source_charge : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run →
    sourceByteCharge run.inner≤4*kidsByteCharge cs+(nodeEnc source).length
  | _,_,.nil,_,_,_,_,hr => by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    simp [sourceByteCharge,terminalRun] <;> omega
  | source,whole,.some c rest,0,key,v,run,hr => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert c key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        have h := traceUpsert_source_charge c key v inner hc
        simp only [kidsByteCharge,kOccs,List.map_append,List.sum_append]
        unfold nodeByteCharge at h
        omega
  | source,whole,.none rest,n+1,key,v,run,hr => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_source_charge source whole rest n key v inner hc
  | source,whole,.some c rest,n+1,key,v,run,hr => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have h := traceKids_source_charge source whole rest n key v inner hc
      simp only [kidsByteCharge,kOccs,List.map_append,List.sum_append]
      unfold kidsByteCharge at h
      omega
end
/-- Charge all actual source occurrences to the native A7 byte measure. -/
theorem nodeByteCharge_le_unfolded (t : PTrie) : nodeByteCharge t≤unfoldedBytesT t := by
  simp only [nodeByteCharge,unfoldedBytesT,native_occs_eq]
  exact Nat.le_add_right _ _

theorem nativeUpserts_source_charge (runs : List (PTrie × TreeRun))
    (hr : ∀ x∈runs, ∃ key v,traceUpsert x.1 key v=some x.2) :
    (runs.map (fun x => sourceByteCharge x.2)).sum≤4*preBytes (runs.map Prod.fst) := by
  induction runs with
  | nil => simp [preBytes]
  | cons x xs ih =>
    obtain ⟨key,v,h⟩ := hr x (by simp)
    have hs := traceUpsert_source_charge x.1 key v x.2 h
    have hn := nodeByteCharge_le_unfolded x.1
    have ht := ih (fun y hy => hr y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,preBytes,List.map_map] at ht ⊢
    omega

end ZkFormal.NearV3.Assembly
