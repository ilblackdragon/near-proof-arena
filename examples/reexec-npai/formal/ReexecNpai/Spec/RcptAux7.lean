import ReexecNpai.Spec.RcptAux6

/-!
# Receipts phase, part 7: Lean-level facts about the receipts section
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

namespace RcptProof

theorem take_rOff {pb : NearSpec.Bytes} {n : Nat} {rs : List Receipt}
    (hdec : readMany decReceipt n (pb.drop 4) = some (rs, pb.drop (rOff rs n)))
    (h4 : 4 ≤ pb.length) (hcnt : NearSpec.leNat (sl pb 0 4) = n) :
    pb.take (rOff rs n) = encodeReceipts rs := by
  obtain ⟨hcat, hlen⟩ := readMany_decReceipt_some hdec
  have hr : rOff rs n = 4 + (concatAll (rs.map Receipt.encode)).length := by
    simp only [rOff]; rw [List.take_of_length_le (by omega)]
  rw [hr, List.take_add, hcat, List.take_left']
  · have h44 : (sl pb 0 4).length = 4 := sl_length_of (by omega)
    have := leN_leNat (sl pb 0 4)
    rw [h44, hcnt] at this
    simp only [encodeReceipts, u32, hlen, this, sl, List.drop_zero]
  · rfl

theorem rid_bytes {pb : NearSpec.Bytes} {rs : List Receipt} {T : NearSpec.Bytes}
    (hcat : pb.drop 4 = concatAll (rs.map Receipt.encode) ++ T) (hsl : rs.all Receipt.inSlice = true)
    {j : Nat} (hj : j < rs.length) :
    rOff rs j + 8 + rs[j].predecessorId.length + rs[j].receiverId.length + 32 ≤ pb.length ∧
    sl pb (rOff rs j + 8 + rs[j].predecessorId.length + rs[j].receiverId.length) 32 = rs[j].receiptId := by
  have hin : rs[j].inSlice = true := List.all_eq_true.mp hsl _ (List.getElem_mem hj)
  have hrid : rs[j].receiptId.length = 32 := by
    simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true, beq_iff_eq] at hin
    exact hin.1.1.1.1.2
  have d := drop_rOff hcat (k := j)
  rw [List.drop_eq_getElem_cons hj, List.map_cons, concatAll, List.append_assoc] at d
  have hsplit : rs[j].encode = (borshBytes rs[j].predecessorId ++ borshBytes rs[j].receiverId) ++
      (rs[j].receiptId ++ ([0] ++ (borshBytes rs[j].signerId ++ rs[j].signerPk.encode ++ u128 rs[j].gasPrice ++
        u32 0 ++ u32 0 ++ u32 1 ++ [3] ++ u128 rs[j].deposit))) := by
    simp only [Receipt.encode, List.append_assoc]
  have hl : (borshBytes rs[j].predecessorId ++ borshBytes rs[j].receiverId).length =
      8 + rs[j].predecessorId.length + rs[j].receiverId.length := by
    simp only [List.length_append, borshBytes_length]; omega
  rw [hsplit, List.append_assoc] at d
  have hlen := congrArg List.length d
  simp only [List.length_drop, List.length_append, hl, hrid] at hlen
  refine ⟨by omega, ?_⟩
  simp only [sl]
  rw [show rOff rs j + 8 + rs[j].predecessorId.length + rs[j].receiverId.length =
    rOff rs j + (borshBytes rs[j].predecessorId ++ borshBytes rs[j].receiverId).length by rw [hl]; omega,
    ← List.drop_drop, d, List.drop_left, List.append_assoc, List.take_left' hrid]

theorem rt_rid (r : Receipt) (A : Nat) :
    ((rtBytes r A).drop 16).take 4 = NearSpec.u32 (A + 4 + r.predecessorId.length + 4 + r.receiverId.length) := by
  simp [rtBytes, NearSpec.u32, NearSpec.leN]

/-- The memory states along the receipts phase after the receipt loop. -/
structure Chain (cb pb : NearSpec.Bytes) (n : Nat) (rs : List Receipt) (ms x y z w : M) : Prop where
  pre : PreSt cb pb n ms
  inv : LInv cb pb ms n rs x
  ymem : y.mem = writeMem x.mem 3080 4 (Bytes.leN 4 (PF + rOff rs n))
  zmem : z.mem = writeMem y.mem SH8 8 (readMem y.mem 2637 8)
  wmem : w.mem = writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem SH8 (rOff rs n + 8)))

section
variable {cb pb : NearSpec.Bytes} {n : Nat} {rs : List Receipt} {ms x y z w : M}

theorem Chain.xms (h : Chain cb pb n rs ms x y z w) (a k : Nat) (hak : a + k ≤ RT ∨ RT + 64 * n ≤ a) :
    readMem x.mem a k = readMem ms.mem a k :=
  readMem_congr (fun i hi => h.inv.out _ (by omega))

theorem Chain.zx (h : Chain cb pb n rs ms x y z w) (a k : Nat) (h1 : a + k ≤ 3080 ∨ 3084 ≤ a)
    (h2 : a + k ≤ SH8 ∨ PF ≤ a) : readMem z.mem a k = readMem x.mem a k := by
  rw [h.zmem, readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [SH8, PF] at h2 ⊢; omega), h.ymem,
    readMem_writeMem_disjoint _ _ _ _ _ _ h1]

theorem Chain.wz (h : Chain cb pb n rs ms x y z w) (a k : Nat) (h1 : a + k ≤ 1408 ∨ 1440 ≤ a) :
    readMem w.mem a k = readMem z.mem a k := by
  rw [h.wmem, readMem_writeMem_disjoint _ _ _ _ _ _ h1]

theorem Chain.wms (h : Chain cb pb n rs ms x y z w) (a k : Nat) (h1 : a + k ≤ 1408 ∨ 1440 ≤ a)
    (h2 : a + k ≤ 3080 ∨ 3084 ≤ a) (h3 : a + k ≤ SH8 ∨ PF ≤ a) (h4 : a + k ≤ RT ∨ RT + 64 * n ≤ a) :
    readMem w.mem a k = readMem ms.mem a k := by
  rw [h.wz a k h1, h.zx a k h2 h3, h.xms a k h4]

theorem Chain.R_le (h : Chain cb pb n rs ms x y z w) : rOff rs n ≤ pb.length := h.inv.oLe

theorem Chain.commit_iff (h : Chain cb pb n rs ms x y z w) :
    ArenaCore.sha256 (readMem z.mem SH8 (rOff rs n + 8)) = readMem z.mem 2713 32 ↔
      receiptsCommitment (claimOf cb).shardId rs = (claimOf cb).receiptsCommitment := by
  have hpre := h.pre
  have hn := hpre.nmax
  have hcl := hpre.claim
  have hR := h.R_le
  have hpl := hpre.plen
  simp only [PMAX] at hpl
  have e1 : readMem z.mem SH8 (rOff rs n + 8) = readMem z.mem SH8 8 ++ readMem z.mem PF (rOff rs n) := by
    rw [Nat.add_comm, readMem_add]; rfl
  have e2 : readMem z.mem SH8 8 = seg cb 77 8 := by
    rw [h.zmem, readMem_writeMem_self _ _ _ _ (by simp), List.take_of_length_le (by simp), h.ymem,
      readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), h.xms _ _ (by simp [RT]),
      show (2637 : Nat) = 2560 + 77 from rfl, seg_claim hcl 77 8 (by omega)]
  have e3 : readMem z.mem PF (rOff rs n) = pb.take (rOff rs n) := by
    rw [h.zx _ _ (by simp [PF]) (by simp), h.xms _ _ (by simp only [RT, PF]; omega),
      readMem_prefix hpre.proof _ hR]
  have e4 : readMem z.mem 2713 32 = seg cb 153 32 := by
    rw [h.zx _ _ (by omega) (by simp [SH8]), h.xms _ _ (by simp [RT]),
      show (2713 : Nat) = 2560 + 153 from rfl, seg_claim hcl 153 32 (by omega)]
  have e5 := take_rOff h.inv.dec hpre.n4 (by rw [hpre.count]) 
  have hlen := h.inv.len
  rw [e1, e2, e3, e4, e5]
  have hu : NearSpec.u64 (claimOf cb).shardId = seg cb 77 8 := leN_seg (by rw [hpre.shape.1]; omega)
  simp only [receiptsCommitment, hu]
  rfl


theorem Chain.ridOK (h : Chain cb pb n rs ms x y z w) : RidOK w.mem n (rs.map Receipt.receiptId) := by
  intro j hj
  have hlen := h.inv.len
  have hj' : j < rs.length := by omega
  have hn := h.pre.nmax
  have hpl := h.pre.plen
  simp only [PMAX] at hpl
  have hcat := (readMany_decReceipt_some h.inv.dec).1
  obtain ⟨hb, hsl⟩ := rid_bytes hcat h.inv.slice hj'
  have h16 := readMem_slice (h.inv.rt j hj') 16 4 (by omega)
  rw [rt_rid] at h16
  have hq : qp w.mem j = PF + (rOff rs j + 8 + rs[j].predecessorId.length + rs[j].receiverId.length) := by
    simp only [qp]
    rw [h.wz _ _ (by omega), h.zx _ _ (by omega) (by simp [SH8]; omega),
      show j * 64 + 3600 = RT + 64 * j + 16 by simp [RT]; omega, h16, NearSpec.u32, ← leN_eq,
      leToNat_leN _ _ (by simp only [PF]; omega)]
    omega
  rw [hq, h.wms _ _ (by simp [PF]; omega) (by simp [PF]; omega) (by simp) (by simp only [RT, PF]; omega),
    rdProof h.pre.proof hb, hsl]
  refine ⟨by simp [List.getD_eq_getElem?_getD, hj'], by simp only [PF]; omega⟩

theorem Chain.st (h : Chain cb pb n rs ms x y z w) {m' : M} (hm : m'.mem = w.mem) (h15 : m'.regs 15 = 1)
    (h14 : m'.regs 14 = 8) (hnd : (rs.map Receipt.receiptId).Nodup)
    (hcom : receiptsCommitment (claimOf cb).shardId rs = (claimOf cb).receiptsCommitment) :
    RcptsSt cb pb rs (rOff rs n) m' := by
  have hpre := h.pre
  have hn := hpre.nmax
  have hpl := hpre.plen
  have hlen := h.inv.len
  have hR := h.R_le
  simp only [PMAX] at hpl
  have hw : ∀ a k, (a + k ≤ 1408 ∨ 1440 ≤ a) → (a + k ≤ 3080 ∨ 3084 ≤ a) → (a + k ≤ SH8 ∨ PF ≤ a) →
      (a + k ≤ RT ∨ RT + 64 * n ≤ a) → readMem m'.mem a k = readMem ms.mem a k := by
    intro a k h1 h2 h3 h4; rw [hm]; exact h.wms a k h1 h2 h3 h4
  have hproof : readMem m'.mem PF pb.length = pb := by
    rw [hw _ _ (by simp [PF]) (by simp [PF]) (by simp) (by simp only [RT, PF]; omega)]; exact hpre.proof
  refine { toClaimIn := ⟨⟨h15, h14, ?_⟩, ?_, hpre.shape⟩, ok := ?_, rcpts := ?_, plen := hpre.plen,
           pend := ?_, nC := ?_, rend := ?_, rt := ?_, proof := hproof }
  · rw [hw _ _ (by omega) (by omega) (by simp [SH8]) (by simp [RT])]; exact hpre.data
  · rw [hw _ _ (by simp [CLM]) (by simp [CLM]) (by simp [CLM, SH8]) (by simp [CLM, RT])]; exact hpre.claim
  · refine ⟨hpre.n4, by rw [hpre.count, hlen], by rw [hlen]; exact h.inv.dec, hR, by rw [hlen]; exact hpre.cnt,
      by rw [hlen]; exact hpre.npos, by rw [hlen]; exact hpre.nmax, by rw [hlen]; exact hpre.gas, h.inv.slice,
      hnd, hcom⟩
  · rw [readMem_prefix hproof _ hR]
  · simp only [rd32, C_PEND]
    rw [hw _ _ (by omega) (by omega) (by simp [SH8]) (by simp [RT])]
    exact hpre.pend
  · simp only [rd32, C_N]
    rw [hw _ _ (by omega) (by omega) (by simp [SH8]) (by simp [RT])]
    have := hpre.nC
    simp only [rd32, C_N] at this
    rw [this, hlen]
  · simp only [rd32, C_REND]
    rw [hm, h.wz _ _ (by omega), h.zmem, readMem_writeMem_disjoint _ _ _ _ _ _ (by simp [SH8]), h.ymem,
      readMem_writeMem_self _ _ _ _ (by simp [Bytes.leN_length]),
      List.take_of_length_le (by simp [Bytes.leN_length]), leToNat_leN _ _ (by simp only [PF]; omega)]
  · intro i hi
    rw [hm, h.wz _ _ (by simp only [RT]; omega), h.zx _ _ (by simp only [RT]; omega) (by simp only [RT, SH8]; omega)]
    exact h.inv.rt i hi

theorem nodup_of_getD {ids : List NearSpec.Bytes} {n : Nat} (hl : ids.length = n)
    (h : ∀ a b, a < b → b < n → ids.getD a [] ≠ ids.getD b []) : ids.Nodup := by
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  have := h a b hab (by omega)
  simpa [List.getD_eq_getElem?_getD, ha, hb] using this

theorem getD_of_nodup {ids : List NearSpec.Bytes} (h : ids.Nodup) :
    ∀ a b, a < b → b < ids.length → ids.getD a [] ≠ ids.getD b [] := by
  unfold List.Nodup at h
  rw [List.pairwise_iff_getElem] at h
  intro a b hab hb
  have := h a b (by omega) hb hab
  simpa [List.getD_eq_getElem?_getD, hb, show a < ids.length by omega] using this

theorem R_eq {pb : NearSpec.Bytes} {rs : List Receipt} {R : Nat}
    (hdec : readMany decReceipt rs.length (pb.drop 4) = some (rs, pb.drop R)) (hR : R ≤ pb.length)
    (h4 : 4 ≤ pb.length) : R = rOff rs rs.length := by
  have hcat := (readMany_decReceipt_some hdec).1
  have := congrArg List.length hcat
  simp only [List.length_drop, List.length_append] at this
  simp only [rOff, List.take_length]
  omega
end

end RcptProof


end ReexecNpai
