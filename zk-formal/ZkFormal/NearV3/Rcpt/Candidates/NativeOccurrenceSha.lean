import ZkFormal.NearV3.Assembly.ForestNodeBytes
import ZkFormal.Near.Render.Proof.ShaFit2

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly Render.UpsGen

theorem seedValues_bytes_length : ∀ vid bs,
    ((seedValuesFrom vid bs).map (fun v => v.bytes.length)).sum =
      (bs.map List.length).sum
  | _, [] => by simp [seedValuesFrom]
  | vid, b::bs => by
    simp [seedValuesFrom,seedValue,seedValues_bytes_length (vid+1) bs]

theorem forest_occurrence_bytes (ts : List PTrie) (hw : ∀t∈ts,t.wf=true) :
    ((forestStoreViews ts).nodes.map (fun s => (s.v.ser false).length)).sum +
    ((forestStoreViews ts).values.map (fun v => v.bytes.length)).sum = preBytes ts := by
  have hn := congrArg (fun xs : List (List Nat) => (xs.map List.length).sum)
    (forestNodes_bytes false 0 0 0 ts hw)
  simp only [List.map_map,List.length_map,Function.comp_def] at hn
  simp only [forestStoreViews,seedValues_bytes_length,hn,forestBytes]
  clear hn hw
  have enc : NearSpecV3.nodeEnc = nodeEnc := rfl
  induction ts with
  | nil => simp [preBytes]
  | cons t ts ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,preBytes,List.map_cons,
      List.sum_cons,NearSpecV3.unfoldedBytesT,native_occs_eq,native_valsOf_eq,enc] at *
    omega

/-- Small-message overhead is retained explicitly; byte accounting alone cannot
pay for arbitrary nonempty tiny value blobs. -/
def shortCount (ls : List Nat) : Nat := (ls.filter (fun n => n<43)).length

def hashRows (ls : List Nat) : Nat := (ls.map ZkFormal.Near.Render.rowsOf).sum

theorem hashRows_bound (ls : List Nat) :
    8*hashRows ls ≤ 5*ls.sum+144*shortCount ls := by
  induction ls with
  | nil => simp [hashRows,shortCount]
  | cons n ns ih =>
    have h := ZkFormal.Near.Render.rowsOf_bound n
    by_cases hn : n<43 <;>
      simp [hashRows,shortCount,hn] at * <;> omega

/-- Correlated pre/post-node and value charging for the actual forest seed.
Values with length zero may be retained in this conservative list; actual VPRE
traffic omits them. The two node length lists agree in the store-only seed. -/
theorem forest_hash_charge (ts : List PTrie) (hw : ∀t∈ts,t.wf=true) :
    let ns := (forestStoreViews ts).nodes.map (fun s => (s.v.ser false).length)
    let vs := (forestStoreViews ts).values.map (fun v => v.bytes.length)
    8*(2*hashRows ns+hashRows vs) ≤
      10*preBytes ts+288*shortCount ns+144*shortCount vs := by
  dsimp only
  have he := forest_occurrence_bytes ts hw
  have hn := hashRows_bound ((forestStoreViews ts).nodes.map (fun s => (s.v.ser false).length))
  have hv := hashRows_bound ((forestStoreViews ts).values.map (fun v => v.bytes.length))
  omega

/-- The unchanged checker bounds the combined occurrence bytes, rather than
separately allowing both node bytes and value bytes to spend the same budget. -/
theorem accepted_occurrence_bytes {B : Nat} {cb wb : Bytes} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    let ts := m.pre::steps.map ImplicitStepV3.pre
    ((forestStoreViews ts).nodes.map (fun s => (s.v.ser false).length)).sum +
    ((forestStoreViews ts).values.map (fun v => v.bytes.length)).sum ≤ B := by
  have hgood : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    simp only [List.mem_cons,List.mem_map] at ht
    rcases ht with rfl | ⟨e,he,rfl⟩
    · rw [hm.pre]
      exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
    · exact (hv.input_facts e he).2.2
  dsimp only
  rw [forest_occurrence_bytes _ hgood]
  exact checkD0a_preBytes hk hw hc hm hv

end ZkFormal.NearV3.Rcpt.Candidates
