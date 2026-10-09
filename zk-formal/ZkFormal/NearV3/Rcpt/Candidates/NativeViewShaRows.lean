import ZkFormal.NearV3.Rcpt.Candidates.NativePostShaLength
import ZkFormal.NearV3.Assembly.SourceSemantics

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly Render.UpsGen

private theorem sum_map_add {α : Type} (xs : List α) (f g : α→Nat) :
    (xs.map (fun x => f x+g x)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; omega

private theorem hashRows_append (a b : List Nat) : hashRows (a++b)=hashRows a+hashRows b := by
  simp [hashRows]

private theorem seed_value_lengths : ∀ vid bs,
    (seedValuesFrom vid bs).map (fun v => v.bytes.length)=bs.map List.length
  | _,[] => rfl
  | vid,b::bs => by simp [seedValuesFrom,seedValue,seed_value_lengths (vid+1) bs]

/-- Conservative row count of both actual node hash families and all values;
empty VPRE messages may be removed later without increasing this count. -/
def nodeValueShaRows (ns : List NodeS3) (vs : List ValE) : Nat :=
  nodePairShaRows ns+hashRows (vs.map (fun v => v.bytes.length))

private theorem occurrence_rows_split (os : List PTrie) :
    occurrenceShaRows os=2*hashRows (os.map (fun t => (nodeEnc t).length))+
      hashRows ((os.flatMap ownVals).map List.length) := by
  induction os with
  | nil => simp [occurrenceShaRows,hashRows]
  | cons t os ih =>
    simp only [occurrenceShaRows,List.map_cons,List.sum_cons] at ih ⊢
    simp only [List.flatMap_cons,List.map_append,List.map_cons,
      hashRows,List.sum_cons,List.sum_append] at ih ⊢
    omega

private theorem forest_rows_split (ts : List PTrie) :
    (ts.map (fun t => occurrenceShaRows (occs t))).sum=
      2*hashRows ((ts.flatMap occs).map (fun t => (nodeEnc t).length))+
      hashRows ((forestBytes ts).map List.length) := by
  induction ts with
  | nil => simp [hashRows,forestBytes]
  | cons t ts ih =>
    have ht := occurrence_rows_split (occs t)
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,
      hashRows_append,forestBytes,valsOf] at *
    omega

/-- Exact correspondence for the concrete assembled native execution views.
This is a length/row identity; it does not assert AIR validity of the seed. -/
theorem native_view_sha_rows (k : WalkD0) (w : StateWitness) (m : MainExecutionV3)
    (steps : List ImplicitStepV3)
    (hw : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true) :
    let x := nativeExecutionViews k w m steps
    nodeValueShaRows x.nodes x.values=
      ((m.pre::steps.map ImplicitStepV3.pre).map (fun t => occurrenceShaRows (occs t))).sum := by
  let ts := m.pre::steps.map ImplicitStepV3.pre
  change nodeValueShaRows (forestNodes 0 0 0 ((runtimePairs m steps).map Prod.fst))
      (seedValuesFrom 0 (forestBytes ((runtimePairs m steps).map Prod.fst)))=_
  rw [runtimePairs_pre]
  have hp := congrArg (fun xs : List (List Nat) => hashRows (xs.map List.length))
    (forestNodes_bytes true 0 0 0 ts hw)
  have hn := congrArg (fun xs : List (List Nat) => hashRows (xs.map List.length))
    (forestNodes_bytes false 0 0 0 ts hw)
  simp only [List.map_map,Function.comp_def,List.length_map] at hp hn
  unfold nodeValueShaRows nodePairShaRows
  rw [sum_map_add]
  simp only [hashRows,List.map_map,Function.comp_def] at hp hn
  rw [hn,hp,seed_value_lengths,forest_rows_split]
  simp only [ts,hashRows,List.map_map,Function.comp_def] at *
  omega

/-- Updated digest windows may be arbitrary; only the same native occurrence
lengths and the ordinary node well-formedness are needed for workload equality. -/
theorem updated_native_rows (ns : List NodeS3) (vs : List ValE) (ts : List PTrie)
    (hn : NodeWf3 ns)
    (hpre : ns.map (fun s => (s.v.ser false).length)=
      (ts.flatMap occs).map (fun t => (nodeEnc t).length))
    (hv : vs.map (fun v => v.bytes.length)=(forestBytes ts).map List.length) :
    nodeValueShaRows ns vs=(ts.map (fun t => occurrenceShaRows (occs t))).sum := by
  unfold nodeValueShaRows
  rw [node_pair_rows ns hn,hpre,hv,forest_rows_split]

theorem accepted_native_view_sha_bound {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ()) :
    ∃m : MainExecutionV3, ∃steps : List ImplicitStepV3, ∃last : Bytes,
      m.NativeValid k w ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      let x := nativeExecutionViews k w m steps
      nodeValueShaRows x.nodes x.values≤2925275 := by
  obtain ⟨m,steps,last,hm,_,hv,_,hs,_,hgood⟩ := checkD0a_native_trace hk hw hc
  have hb := checkD0a_preBytes hk hw hc hm hv
  have hp := forest_sha_amortized (m.pre::steps.map ImplicitStepV3.pre) hgood
  have he := native_view_sha_rows k w m steps hgood
  simp only [List.length_cons,List.length_map] at hp
  unfold B0 at hb
  exact ⟨m,steps,last,hm,hv,by dsimp only at he ⊢; omega⟩

end ZkFormal.NearV3.Rcpt.Candidates
