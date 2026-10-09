import ZkFormal.NearV3.Rcpt.Candidates.PreparedRouting
import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
import ZkFormal.NearV3.Assembly.SourceResult

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 Render.SrcpGen

/-- Every occurrence of a repeated prepared key has an empty raw receipt list,
including its first occurrence. All premises come from unchanged D0a and real decoding. -/
theorem relD0a_repeated_empty {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    {j : Nat} (hj : j < p.lists.length) (hrepeated : sourceRepeated p.lists j = true) :
    (entryAt p.lists w.entries j).receipts = [] := by
  obtain ⟨k, sw, hk, hsw, hv, hr⟩ := relD0a_sources_verified h
  have hd : decodeW wb = .ok w := by simp [decodeW, hf, hw, bind, Except.bind]
  have hew := Except.ok.inj (hsw.symm.trans hd)
  subst sw
  have hps := Assembly.prepD0_source_lists hp hk
  have hroute := preparedSourceLists_raw_routing hv hr hps
  have happ := preparedSourceLists_applied hv hps
  have hc : checkD0 cb wb = .ok () := by
    have hh := h.1
    unfold RelD0 acceptsD0 at hh
    cases he : checkD0 cb wb with
    | error err => simp [he] at hh
    | ok u => cases u; rfl
  have hn := Assembly.checkD0_applied_nodup hk hd hc
  have hpn : ((p.lists.flatMap (sourceReceipts w.entries k.H.shardId k.L)).map Receipt.receiptId).Nodup := by
    rw [happ]
    exact hn
  let receipts : Bytes → List Receipt := fun key =>
    ((lookupLast key w.entries).getD ⟨[],[],⟨0,0,[]⟩⟩).receipts
  let route : Receipt → Bool := fun r => k.L.shardOf r.receiverId == k.H.shardId
  have hnk : (((p.lists.map SrcList.key).flatMap fun key =>
      (receipts key).filter route).map Receipt.receiptId).Nodup := by
    rw [List.flatMap_map]
    exact hpn
  have hm : p.lists.getD j ⟨[],0,[]⟩ ∈ p.lists := by
    rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩]
    exact List.getElem_mem hj
  have hrs : ∀ r ∈ receipts (p.lists.getD j ⟨[],0,[]⟩).key, route r = true := by
    intro r hr'
    have he := hroute _ hm r hr'
    simpa only [route, beq_iff_eq] using he
  have hcount : 2 ≤ (p.lists.map SrcList.key).count (p.lists.getD j ⟨[],0,[]⟩).key := by
    simpa only [sourceRepeated, decide_eq_true_eq] using hrepeated
  exact repeated_receipts_empty _ _ receipts route hcount hrs hnk

/-- The candidate's repeated-bit length constraint is complete on every actual valid input. -/
theorem relD0a_repeated_L12 {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    {j : Nat} (hj : j < p.lists.length) (hrepeated : sourceRepeated p.lists j = true) :
    (block p.lists w.entries j).L = 12 := by
  have he := relD0a_repeated_empty h hp hf hw hj hrepeated
  simp only [block, blockOfProof, he]
  simp [encodeReceipts, concatAll, u64, u32, leN]

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
