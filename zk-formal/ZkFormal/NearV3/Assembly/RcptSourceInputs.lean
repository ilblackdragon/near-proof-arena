import ZkFormal.NearV3.Assembly.RcptNativeFlags
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRouting
import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near Rcpt.Candidates

private theorem flatten_map_eq {α β : Type} (xs : List α) (f : α→List β) :
    (xs.map f).flatten=xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih]

/-- One raw authenticated list per prepared occurrence, in its actual shuffled
order. Equal-key occurrences and empty lists are retained. -/
def sourceInputLists (ctx : ApplyCtx) (sources : List SrcList) (entries : List ProofEntry) : List (List Input) :=
  nativeInputs ctx (sources.map (fun s=>(sourceEntry entries s).receipts))

theorem sourceInputLists_length (ctx : ApplyCtx) (sources : List SrcList) (entries : List ProofEntry) :
    (sourceInputLists ctx sources entries).length=sources.length := by
  simp [sourceInputLists,nativeInputs]

theorem sourceInputLists_receipts (ctx : ApplyCtx) (sources : List SrcList) (entries : List ProofEntry) :
    (sourceInputLists ctx sources entries).map (List.map Input.receipt)=
      sources.map (fun s=>(sourceEntry entries s).receipts) := by
  simp [sourceInputLists,nativeInputs,nativeInput,List.map_map,Function.comp_def]

/-- Native acceptance removes the routing filter from every selected raw list;
this connects the concrete renderer input batch to the actual executed batch. -/
theorem sourceInputLists_applied {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness} (ctx : ApplyCtx)
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) :
    (sourceInputLists ctx p.lists w.entries).flatten.map Input.receipt=appliedReceipts k w := by
  obtain ⟨k',w',hk',hw',hv,hr⟩ := relD0a_sources_verified ha
  have hek := Except.ok.inj (hk'.symm.trans hk)
  have hew := Except.ok.inj (hw'.symm.trans hw)
  subst k'; subst w'
  have hs := prepD0_source_lists hp hk
  have hf := preparedSourceLists_raw_routing hv hr hs
  rw [sourceInputLists,nativeInputs_receipts,flatten_map_eq]
  rw [←preparedSourceLists_applied hv hs]
  rw [←flatten_map_eq,←flatten_map_eq]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro s hmem
  unfold sourceReceipts
  symm
  apply List.filter_eq_self.mpr
  intro r hr
  exact beq_iff_eq.mpr (hf s hmem r hr)

/-- The same accepted source selection pins every RC preimage's shard header. -/
theorem sourceInputLists_toShard {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) :
    ∀s∈p.lists,(sourceEntry w.entries s).proof.toShard=k.H.shardId := by
  obtain ⟨k',w',hk',hw',hv,_⟩ := relD0a_sources_verified ha
  have hek := Except.ok.inj (hk'.symm.trans hk)
  have hew := Except.ok.inj (hw'.symm.trans hw)
  subst k'; subst w'
  intro s hs
  obtain ⟨e,he,_,ht,_⟩ := preparedSourceLists_authenticated w.entries k.H.shardId k.sourceBlks hv
    (prepD0_source_lists hp hk) s hs
  simpa [sourceEntry,he] using ht

end ZkFormal.NearV3.Assembly.RcptSkeleton
