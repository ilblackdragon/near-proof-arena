import ZkFormal.NearV3.Candidates.SortGeneralTraffic
namespace ZkFormal.NearV3.Candidates.NativeSortIds
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Near.Render Assembly ZkFormal.Air ZkFormal.Algebra

/-- The physical repaired sort receives the original indexed receipt bytes.
Sorting changes order only; empty input is covered by the silent native trace. -/
theorem traffic (rs : List Receipt) (hn:rs.length≤8192) (t : Nat) (pub : List Fp) :
    TableTraffic SortEmpty.table.interactions (trace rs) t pub (sortTraffic (input rs)) := by
  by_cases he:rs=[]
  · subst rs
    intro bus msg
    simp only [trace,ite_true,SortEmpty.empty_count]
    simp [input,sortTraffic,cnt]
  · have h:=SortGeneral.traffic (sorted rs) (by rw [length];exact hn) t pub
    rw [trace,if_neg he]
    intro bus msg
    obtain ⟨hs,hr⟩:=h bus msg
    refine ⟨hs,?_⟩
    rw [hr]
    by_cases hb:bus=B_RIDS
    · simp only [sortTraffic,hb,ite_true]
      exact ((List.Perm.flatMap_right
        (fun x : Nat×List Nat=>(List.range 32).map (fun j=>[x.1,j,x.2.getD j 0]))
        (permutation rs)).map Msg.toFp).count_eq msg
    · simp [sortTraffic,hb]

/-- Acceptance supplies all size, uniqueness and byte-validity obligations for
the same physical sort trace and its full original receipt-ID inventory. -/
theorem accepted_traffic {cb wb raw : Bytes} {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hr:decodeStateWitness raw=.ok w)
    (hc:checkD0a B0 cb wb=.ok ()) (hm:m.NativeValid k w) (t : Nat) (pub : List Fp) :
    TableLocal SortEmpty.table (trace (appliedReceipts k w)) t pub ∧
    TableTraffic SortEmpty.table.interactions (trace (appliedReceipts k w)) t pub
      (sortTraffic (input (appliedReceipts k w))) := by
  refine ⟨accepted_trace hk hw hr hc hm t pub,?_⟩
  have hrel:RelD0a B0 cb wb:=(relD0a_iff B0 cb wb).mpr hc
  have hg:(m.ctx k).gasLimit≤maxGasLimitD0:=by
    change k.slotB2.gasLimit≤maxGasLimitD0
    simpa only [a1,hk,decide_eq_true_eq] using hrel.2.1
  have hn:=applyNewChunk_receipt_bound hm.run hg
  exact traffic _ (by omega) t pub

end ZkFormal.NearV3.Candidates.NativeSortIds
