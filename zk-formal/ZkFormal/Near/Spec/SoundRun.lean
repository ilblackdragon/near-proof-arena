import ZkFormal.Near.Spec.SoundAccount

/-!
# ZkFormal.Near.Spec.SoundRun — the batch run on the record trie

`accAt c e r` is the accumulator of `runBatch` before receipt `r` (trie
`trieOf e.ns (e.valsAt r)`, the first `r` outcomes and refunds, `r·G` gas,
`tokAt r` tokens).  `step`: receipt `r` takes `accAt r` to `accAt (r+1)`;
`run`: the whole batch ends in `accAt n`.
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1

namespace Sound

/-- The accumulator before receipt `r`. -/
def accAt (c : Claim) (e : Ext) (r : Nat) : Acc :=
  ⟨trieOf e.ns (e.valsAt r), (List.range r).map (e.outcomeOf c),
   (List.range r).flatMap (e.refundOf c), r * Params.G, e.tokAt c r⟩

theorem valsAt_succ (e : Ext) (r : Nat) :
    e.valsAt (r + 1) = upd (e.valsAt r) (e.slot r)
      (Account.encode { e.acc0 (e.slot r) with
        amount := e.amtAt (e.slot r) r + (e.rc r).deposit }) := by
  funext j
  by_cases h : j = e.slot r
  · subst h; simp [Ext.valsAt, Ext.amtAt, upd]
  · have h' : e.slot r ≠ j := fun x => h x.symm
    simp [Ext.valsAt, Ext.amtAt, upd, h, h']

variable {c : Claim} {e : Ext}

theorem acc0_decode (hg : Good c e) {k : Nat} {nr : NodeRec} (hk : e.ns[k]? = some nr)
    (ht : nr.touched = true) : Account.decode (e.vals0 k) = some (e.acc0 k) := by
  have := hg.vals_v1 k nr hk ht
  cases h : Account.decode (e.vals0 k) with
  | none => rw [h] at this; simp at this
  | some a => simp [Ext.acc0, h]

/-- The pre-state trie is the trie of `valsAt 0`. -/
theorem trie_init (hg : Good c e) : trieOf e.ns e.vals0 = trieOf e.ns (e.valsAt 0) := by
  apply treeOf_congr
  intro j _ nr hj ht
  exact (encode_decode (acc0_decode hg hj ht)).symm

theorem step (hg : Good c e) (r : Nat) (hr : r < e.rs.length) :
    applyReceipt c.ctx (accAt c e r) (e.rc r) = some (accAt c e (r + 1)) := by
  obtain ⟨d, hd0, hd⟩ := hg.shape.depth
  have hok := hg.rcpt_ok r hr
  obtain ⟨⟨nr, hnr, ht⟩, hget, hset⟩ := walkTo_get_set hg.shape d hd0 hd hg.nodes_wf
    (e.valsAt r) (e.slot r)
    (Account.encode { e.acc0 (e.slot r) with
      amount := e.amtAt (e.slot r) r + (e.rc r).deposit }) (hg.walks r hr)
  have hA := acc0_decode hg hnr ht
  obtain ⟨_, hl, hch, hsu, _⟩ := decode_wf hA
  have hdec : Account.decode (e.valsAt r (e.slot r)) =
      some { e.acc0 (e.slot r) with amount := e.amtAt (e.slot r) r } :=
    decode_encode _ (by have := hok.amt_lt; simp only; omega) hl hch hsu
  rw [← valsAt_succ] at hset
  have h1 := hok.amt_lt
  have h2 := hok.tot_lt
  have h3 := hok.stake
  have h4 := hok.burnt_lt
  have h5 := hok.surplus_lt
  have h6 := hok.tok_lt
  simp only [burntOf, surplusOf, burnPrice] at h4 h5 h6
  simp only [applyReceipt, accAt, Claim.ctx, hget, hdec]
  simp only [Nat.not_le.mpr h1, Nat.not_le.mpr h2, ↓reduceIte]
  have hs : (decide (e.amtAt (e.slot r) r + (e.rc r).deposit + (e.acc0 (e.slot r)).locked ≥
      Params.storageAmountPerByte * (e.acc0 (e.slot r)).storageUsage) ||
      decide ((e.acc0 (e.slot r)).storageUsage ≤ Params.zeroBalanceStorageLimit)) = true := by
    rcases h3 with h3 | h3 <;> simp [h3]
  simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.not_le.mpr h6]
  rw [hset]
  split
  · rename_i hc
    exact absurd hc (by
      simp only [Bool.or_eq_true, not_or]; exact ⟨by simpa using h4, by simpa using h5⟩)
  simp only [Option.some.injEq]
  simp only [List.range_succ, List.map_append, List.flatMap_append, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Ext.outcomeOf, Ext.refundOf, Ext.tokAt,
    burntOf, surplusOf, burnPrice, Nat.succ_mul]
  rfl

theorem run (hg : Good c e) :
    ∀ m r, r + m = e.rs.length → applyAll c.ctx (accAt c e r) (e.rs.drop r) =
      some (accAt c e e.rs.length)
  | 0, r, h => by
    simp only [Nat.add_zero] at h; subst h; simp [applyAll]
  | m + 1, r, h => by
    have hr : r < e.rs.length := by omega
    rw [List.drop_eq_getElem_cons hr]
    have hrc : e.rs[r] = e.rc r := by simp [Ext.rc, hr]
    rw [hrc]
    simp only [applyAll, step hg r hr]
    exact run hg m (r + 1) (by omega)

theorem runBatch_eq (hg : Good c e) :
    runBatch c.ctx (trieOf e.ns e.vals0) e.rs = some (accAt c e e.rs.length) := by
  have := run hg e.rs.length 0 (by omega)
  simp only [List.drop_zero] at this
  rw [runBatch, trie_init hg]
  exact this

end Sound

end ZkFormal.Near
