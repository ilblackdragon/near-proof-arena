import ZkFormal.NearV3.Candidates.SortGeneralTrace
import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Assembly.SourceResult
namespace ZkFormal.NearV3.Candidates.NativeSortIds
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Near.Render Assembly

def input (rs : List Receipt) : List (Nat×List Nat):=
  rs.zipIdx.map (fun x=>(x.2,x.1.receiptId.map UInt8.toNat))
def sorted (rs : List Receipt) : List (Nat×List Nat):=(input rs).foldr insertSorted []

theorem permutation (rs : List Receipt) : (sorted rs).Perm (input rs) := perm_sorted _

theorem length (rs : List Receipt) : (sorted rs).length=rs.length := by
  rw [(permutation rs).length_eq]
  simp [input]

theorem bytes (rs : List Receipt) (hw:∀r∈rs,r.wf=true) :
    ∀x∈sorted rs,x.2.length=32 ∧ ∀b∈x.2,b<256 := by
  intro x hx
  obtain ⟨⟨r,i⟩,hr,rfl⟩:=List.mem_map.mp ((permutation rs).mem_iff.mp hx)
  have hr:r∈rs:=List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hr)
  have hw:=hw r hr
  have hl:r.receiptId.length=32:=by
    simp only [Receipt.wf,Bool.and_eq_true,beq_iff_eq] at hw
    grind only
  constructor
  · simpa using hl
  · intro b hb
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hb
    exact b.toNat_lt

theorem values (rs : List Receipt) :
    (input rs).map (fun x=>leVal x.2)=rs.map (fun r=>leNat r.receiptId) := by
  simp only [input,List.map_map,Function.comp_def]
  have he:(fun x:Receipt×Nat=>leVal (x.1.receiptId.map UInt8.toNat))=
      (fun x=>leNat x.1.receiptId):=by funext x;exact leVal_toNats _
  rw [he]
  have hh:rs.zipIdx.map Prod.fst=rs:=by
    rw [List.zipIdx_eq_zip_range']
    exact List.map_fst_zip (by simp)
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map (fun r:Receipt=>leNat r.receiptId)) hh

theorem strict (rs : List Receipt) (hw:∀r∈rs,r.wf=true)
    (hn:(rs.map Receipt.receiptId).Nodup) :
    (sorted rs).Pairwise (fun a b=>leVal a.2<leVal b.2) := by
  have hd:((input rs).map (fun x=>leVal x.2)).Nodup:=by
    rw [values]
    unfold List.Nodup at hn ⊢
    rw [List.pairwise_map] at hn ⊢
    apply hn.imp_of_mem
    intro a b ha hb hne he
    apply hne
    apply leNat_inj _ _ _ he
    have hwa:=hw a ha
    have hwb:=hw b hb
    simp only [Receipt.wf,Bool.and_eq_true,beq_iff_eq] at hwa hwb
    grind only
  have hd:=((permutation rs).map (fun x=>leVal x.2)).nodup_iff.mpr hd
  unfold List.Nodup at hd
  rw [List.pairwise_map] at hd
  exact (pairwise_sorted _).imp₂ (fun a b h1 h2=>Nat.lt_of_le_of_ne h1 h2) hd

theorem accepted {cb wb raw : Bytes} {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hr:decodeStateWitness raw=.ok w)
    (hc:checkD0a B0 cb wb=.ok ()) :
    (∀x∈sorted (appliedReceipts k w),x.2.length=32 ∧ ∀b∈x.2,b<256) ∧
    (sorted (appliedReceipts k w)).Pairwise (fun a b=>leVal a.2<leVal b.2) := by
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩:=ReexecV3D0.bind_ok' hc
  cases u
  exact ⟨bytes _ (appliedReceipts_wf hr),strict _ (appliedReceipts_wf hr) (checkD0_applied_nodup hk hw hc)⟩
end ZkFormal.NearV3.Candidates.NativeSortIds
