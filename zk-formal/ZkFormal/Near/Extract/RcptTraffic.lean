import ZkFormal.Near.Extract.RcptShape

/-!
# ZkFormal.Near.Extract.RcptTraffic — the table's traffic is `rcptTraffic` of its view

Rows split into the claim rows, the receipts and the padding
(`rows_split`); per bus, the receipts' messages are the view's per-receipt
messages (`RcptBytes`, `RcptDig`, `RcptKey`, `RcptBus`), the claim rows add the
`RC`/`RF` headers, the last receipt the commitments.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- `fun (x, r) => …` over `rs.zip (range rs.length)`. -/
theorem zip_flatMap' {β : Type} (rs : RcptVs) (F : RcptV → Nat → List β) :
    (rs.zip (List.range rs.length)).flatMap (fun p => match p with | (x, r) => F x r) =
      (List.range rs.length).flatMap fun i => F (rs.getD i default) i := by
  rw [← zip_range_flatMap rs F]

theorem zip_map' {β : Type} (rs : RcptVs) (F : RcptV → Nat → β) :
    (rs.zip (List.range rs.length)).map (fun p => match p with | (x, r) => F x r) =
      (List.range rs.length).map fun i => F (rs.getD i default) i := by
  rw [map_eq_flatMap, map_eq_flatMap, ← zip_range_flatMap rs (fun x r => [F x r])]

/-- Per-receipt `Perm` lifts to the receipts. -/
theorem perm_range {α : Type} (n : Nat) (A : Nat → List α) (B : Nat → List α)
    (h : ∀ i, i < n → (A i).Perm (B i)) :
    ((List.range n).flatMap A).Perm ((List.range n).flatMap B) := by
  have gen : ∀ l : List Nat, (∀ i ∈ l, (A i).Perm (B i)) → (l.flatMap A).Perm (l.flatMap B) := by
    intro l; induction l with
    | nil => intro _; exact List.Perm.refl _
    | cons x l ih => intro hl; simp only [List.flatMap_cons]; exact (hl x (by simp)).append (ih (fun i hi => hl i (by simp [hi])))
  exact gen _ (fun i hi => h i (List.mem_range.mp hi))

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- **Rows of the table.** -/
theorem rows_split {rcs : List RS} (S : Shape tr rcs) (b : Nat) (sd : Bool) :
    (List.range (tr.height T_RCPT)).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b sd) =
      (List.range' 0 12).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b sd) ++
      (List.range rcs.length).flatMap (fun i => (List.range' (rcs.getD i default).s (rcs.getD i default).tot).flatMap
        (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b sd)) := by
  rw [flatMap_rows_segs _ ((0, 12) :: segsOf rcs) _ ⟨rfl, S.consec⟩ (by simp only [segEnd]; exact Nat.le_of_lt S.fin)
    (fun q h1 h2 => pad_quiet hL h2 (S.pad q (by simpa [segEnd] using h1) h2) b sd)]
  rw [List.flatMap_cons]
  congr 1
  rw [segsOf, List.flatMap_map, flatMap_eq_range]

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem rcs_get {rcs : List RS} (i : Nat) (hi : i < rcs.length) : rcs.getD i default = rcs[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Data of receipt `i`. -/
theorem rcpt_i {rcs : List RS} (S : Shape tr rcs) (i : Nat) (hi : i < rcs.length) :
    Layout tr (rcs.getD i default).s (rcs.getD i default).h (rcs.getD i default).Lp (rcs.getD i default).Lv
      (rcs.getD i default).Ls (rcs.getD i default).kt ∧
    tr.cell T_RCPT (rcs.getD i default).s o = (rcOffs (viewOf tr rcs) i : Fp) ∧
    tr.cell T_RCPT (rcs.getD i default).s o2 = (rfOffs (viewOf tr rcs) i : Fp) ∧
    tr.cell T_RCPT (rcs.getD i default).s Rcpt.r = ((i : Nat) : Fp) ∧
    (viewOf tr rcs).getD i default = rcptOf tr (rcs.getD i default) := by
  rw [rcs_get hL i hi]
  exact ⟨S.lay _ (List.getElem_mem hi), (offs hL S i hi).1, (offs hL S i hi).2, S.r i hi, viewOf_get tr rcs i hi⟩

/-- **`BYTES` sends.** -/
theorem tr_bytes {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_BYTES true).Perm
      ((rcptSends pub (viewOf tr rcs) B_BYTES).map Msg.toFp) := by
  rw [rows_split hL S]
  simp only [rcptSends, ↓reduceIte, List.map_append]
  rw [zip_flatMap' (viewOf tr rcs) (fun x r => emitAt K_RC (rcOffs (viewOf tr rcs) r) x.enc ++
      (if x.hr = true then emitAt K_RF (rfOffs (viewOf tr rcs) r) x.encRefund else []) ++
      emitAt (msgId K_PEO r) 0 x.peo ++ emitAt (msgId K_LEAF r) 0 x.leaf ++
      (if x.hr = true then emitAt (msgId K_RID r) 0 (x.rid ++ pubBytes pub PV_HEIGHT 8 ++ List.replicate 8 0)
       else [])), viewOf_len, List.map_flatMap]
  refine List.Perm.append (by rw [← List.map_append]; exact claim_bytes hL) (perm_range _ _ _ (fun i hi => ?_))
  obtain ⟨lay, ho, ho2, hr, hv⟩ := rcpt_i hL S i hi
  rw [hv]
  exact rcpt_bytes hL lay ho ho2 hr

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem claim_nil {b : Nat} {sd : Bool} (hb : ¬ (b = B_BYTES ∧ sd = true)) :
    (List.range' 0 12).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b sd) = [] := by
  apply flatMap_range'_nil; intro q hq
  rw [claim_quiet hL (by omega), if_neg hb]

/-- Same-shape buses: per-receipt equality. -/
theorem tr_rcpts {rcs : List RS} (S : Shape tr rcs) (b : Nat) (sd : Bool) (hb : ¬ (b = B_BYTES ∧ sd = true))
    (G : Nat → List Msg)
    (hG : ∀ i, i < rcs.length → (List.range' (rcs.getD i default).s (rcs.getD i default).tot).flatMap
      (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b sd) = (G i).map Msg.toFp) :
    (List.range (tr.height T_RCPT)).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b sd) =
      ((List.range rcs.length).flatMap G).map Msg.toFp := by
  rw [rows_split hL S, claim_nil hL hb, List.nil_append, List.map_flatMap]
  exact flatMap_congr' (fun i hi => hG i (List.mem_range.mp hi))

theorem tr_key {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true).Perm
      ((rcptSends pub (viewOf tr rcs) B_KEYNIB).map Msg.toFp) := by
  apply List.Perm.of_eq
  rw [tr_rcpts hL S B_KEYNIB true (by decide) _ (fun i hi => by
    obtain ⟨lay, -, -, hr, -⟩ := rcpt_i hL S i hi
    exact rcpt_key hL lay hr)]
  simp only [rcptSends, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, ↓reduceIte, Nat.reduceEqDiff]
  rw [zip_flatMap' (viewOf tr rcs) (fun x r => (List.range x.keySyms.length).map fun t =>
      [r, t, x.keySyms.getD t 0, if t + 1 = x.keySyms.length then 1 else 0]), viewOf_len]
  congr 1
  apply flatMap_congr'; intro i hi
  rw [(rcpt_i hL S i (List.mem_range.mp hi)).2.2.2.2]

theorem tr_memS {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_MEM true).Perm
      ((rcptSends pub (viewOf tr rcs) B_MEM).map Msg.toFp) := by
  apply List.Perm.of_eq
  rw [tr_rcpts hL S B_MEM true (by decide) _ (fun i hi => by
    obtain ⟨lay, -, -, hr, -⟩ := rcpt_i hL S i hi
    exact rcpt_memS hL lay hr)]
  simp only [rcptSends, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, ↓reduceIte, Nat.reduceEqDiff]
  rw [zip_flatMap' (viewOf tr rcs) (fun x r => (List.range 16).map fun i =>
      [x.kslot, r + 1, i, x.aft.getD i 0, x.lk.getD i 0, x.st.getD i 0]), viewOf_len]
  congr 1
  apply flatMap_congr'; intro i hi
  rw [(rcpt_i hL S i (List.mem_range.mp hi)).2.2.2.2]

theorem tr_memR {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_MEM false).Perm
      ((rcptRecvs pub (viewOf tr rcs) B_MEM).map Msg.toFp) := by
  apply List.Perm.of_eq
  rw [tr_rcpts hL S B_MEM false (by decide) _ (fun i hi => by
    obtain ⟨lay, -, -, hr, -⟩ := rcpt_i hL S i hi
    exact rcpt_memR hL lay hr)]
  simp only [rcptRecvs, B_DIGEST, B_FINAL, B_MEM, ↓reduceIte, Nat.reduceEqDiff]
  rw [zip_flatMap' (viewOf tr rcs) (fun x r => (List.range 16).map fun i =>
      [x.kslot, x.tprev, i, x.bef.getD i 0, x.lk.getD i 0, x.st.getD i 0]), viewOf_len]
  congr 1
  apply flatMap_congr'; intro i hi
  rw [(rcpt_i hL S i (List.mem_range.mp hi)).2.2.2.2]

theorem tr_rids {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_RIDS true).Perm
      ((rcptSends pub (viewOf tr rcs) B_RIDS).map Msg.toFp) := by
  apply List.Perm.of_eq
  rw [tr_rcpts hL S B_RIDS true (by decide) _ (fun i hi => by
    obtain ⟨lay, -, -, hr, -⟩ := rcpt_i hL S i hi
    exact rcpt_rids hL lay hr)]
  simp only [rcptSends, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, ↓reduceIte, Nat.reduceEqDiff]
  rw [zip_flatMap' (viewOf tr rcs) (fun x r => (List.range 32).map fun i => [r, i, x.rid.getD i 0]), viewOf_len]
  congr 1
  apply flatMap_congr'; intro i hi
  rw [(rcpt_i hL S i (List.mem_range.mp hi)).2.2.2.2]

theorem tr_final {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_FINAL false).Perm
      ((rcptRecvs pub (viewOf tr rcs) B_FINAL).map Msg.toFp) := by
  apply List.Perm.of_eq
  rw [tr_rcpts hL S B_FINAL false (by decide) (fun i => [[i, ((viewOf tr rcs).getD i default).kslot]]) (fun i hi => by
    obtain ⟨lay, -, -, hr, hv⟩ := rcpt_i hL S i hi
    rw [hv]; exact rcpt_final hL lay hr (lay_row0 hL lay).2.2.2)]
  simp only [rcptRecvs, B_DIGEST, B_FINAL, B_MEM, ↓reduceIte, Nat.reduceEqDiff]
  rw [zip_map' (viewOf tr rcs) (fun x r => [r, x.kslot]), viewOf_len]
  simp [List.map_flatMap, List.flatMap_map, map_eq_flatMap]

theorem tr_mpos {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_MPOS true).Perm
      ((rcptSends pub (viewOf tr rcs) B_MPOS).map Msg.toFp) := by
  apply List.Perm.of_eq
  rw [tr_rcpts hL S B_MPOS true (by decide) (fun i => [[0, i, msgId K_LEAF i, 68]]) (fun i hi => by
    obtain ⟨lay, -, -, hr, hv⟩ := rcpt_i hL S i hi
    exact rcpt_mpos hL lay hr (lay_row0 hL lay).2.2.2)]
  simp only [rcptSends, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, ↓reduceIte, Nat.reduceEqDiff]
  rw [zip_map' (viewOf tr rcs) (fun _ r => [0, r, msgId K_LEAF r, 68]), viewOf_len]
  simp [List.map_flatMap, List.flatMap_map, map_eq_flatMap]

end ZkFormal.Near.RcptProof
