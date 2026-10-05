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

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem ends_i {rcs : List RS} (S : Shape tr rcs) (i : Nat) (hi : i < rcs.length) :
    tr.cell T_RCPT (rcs.getD i default).s oEnd = (rcOffs (viewOf tr rcs) (i + 1) : Fp) ∧
    tr.cell T_RCPT (rcs.getD i default).s o2End = (rfOffs (viewOf tr rcs) (i + 1) : Fp) := by
  obtain ⟨lay, ho, ho2, -, hv⟩ := rcpt_i hL S i hi
  obtain ⟨ha, hc, -, -⟩ := lay_row0 hL lay
  have hs : (rcs.getD i default).s < tr.height T_RCPT := by
    have := lay.fin; have := total_pos (rcs.getD i default).h (rcs.getD i default).Lp (rcs.getD i default).Lv
      (rcs.getD i default).Ls (rcs.getD i default).kt; omega
  obtain ⟨z1, z2⟩ := sizes hL hs ha hc
  rw [z1, z2, ho, ho2, lay.cLp, lay.cLv, lay.cLs, lay.ckt, lay.hr]
  simp only [rcOffs, rfOffs, hv, enc_len, encRefund_len, rcptOf_hr, Vt]
  constructor
  · simp only [natCast_add, natCast_mul]; grind
  · cases (rcs.getD i default).h <;> simp [natCast_add, natCast_mul] <;> grind

omit hL in
theorem pubsAt_eq (off len : Nat) : pubsAt pub off len = (pubBytes pub off len).map Fp.ofNat := by
  simp [pubsAt, pubBytes, pubNat, fpN]

/-- **`DIGEST` receives.** -/
theorem tr_dig {rcs : List RS} (S : Shape tr rcs) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_DIGEST false).Perm
      ((rcptRecvs pub (viewOf tr rcs) B_DIGEST).map Msg.toFp) := by
  have hn : 0 < rcs.length := by have := S.ne; cases rcs <;> simp_all
  rw [rows_split hL S, claim_nil hL (by decide), List.nil_append]
  let V : Nat → List (List Fp) := fun i =>
    ((if ((viewOf tr rcs).getD i default).hr then [digMsg (msgId K_RID i) 48 ((viewOf tr rcs).getD i default).rfid]
      else []) ++ [digMsg (msgId K_PEO i) ((viewOf tr rcs).getD i default).peo.length
        ((viewOf tr rcs).getD i default).peoh]).map Msg.toFp
  let E : Nat → List (List Fp) := fun i =>
    if tr.cell T_RCPT ((rcs.getD i default).s + (rcs.getD i default).tot) act = 1 then [] else
      [[(K_RC : Fp), tr.cell T_RCPT (rcs.getD i default).s oEnd] ++ pubsAt pub PV_RC 32,
       [(K_RF : Fp), tr.cell T_RCPT (rcs.getD i default).s o2End] ++ pubsAt pub PV_RFC 32]
  have step1 := perm_range rcs.length _ (fun i => V i ++ E i) (fun i hi => by
    obtain ⟨lay, -, -, hr, hv⟩ := rcpt_i hL S i hi
    simp only [V, E, hv]
    exact rcpt_dig hL lay hr)
  refine step1.trans ((flatMap_append_perm _ _ _).trans ?_)
  have hE : (List.range rcs.length).flatMap E =
      [[(K_RC : Fp), (rcOffs (viewOf tr rcs) rcs.length : Fp)] ++ pubsAt pub PV_RC 32,
       [(K_RF : Fp), (rfOffs (viewOf tr rcs) rcs.length : Fp)] ++ pubsAt pub PV_RFC 32] := by
    have hr : List.range rcs.length = List.range (rcs.length - 1) ++ [rcs.length - 1] := by
      rw [← List.range_succ]; congr 1; omega
    rw [hr, List.flatMap_append,
      flatMap_congr' (G := fun _ => []) (fun i hi => by
        rw [List.mem_range] at hi
        simp only [E]
        rw [show (rcs.getD i default).s + (rcs.getD i default).tot = rcs[i].s + rcs[i].tot by
          rw [rcs_get hL i (by omega)], act_after S hL i (by omega)]
        simp [show i + 1 < rcs.length by omega]),
      flatMap_nil_fun, List.nil_append, List.flatMap_singleton]
    simp only [E]
    rw [show (rcs.getD (rcs.length - 1) default).s + (rcs.getD (rcs.length - 1) default).tot =
        rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot by
      rw [rcs_get hL (rcs.length - 1) (by omega)], act_after S hL (rcs.length - 1) (by omega)]
    simp only [show ¬ (rcs.length - 1 + 1 < rcs.length) by omega, ↓reduceIte, fp_zero_ne_one]
    obtain ⟨e1, e2⟩ := ends_i hL S (rcs.length - 1) (by omega)
    rw [e1, e2, show rcs.length - 1 + 1 = rcs.length by omega]
  rw [hE]
  simp only [rcptRecvs, B_DIGEST, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  rw [zip_flatMap' (viewOf tr rcs) (fun x r => (if x.hr = true then [digMsg (msgId K_RID r) 48 x.rfid] else []) ++
      [digMsg (msgId K_PEO r) x.peo.length x.peoh]), viewOf_len]
  refine List.perm_append_comm.trans ?_
  simp only [digMsg, Msg.toFp, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pubsAt_eq, List.map_flatMap]
  apply List.Perm.of_eq
  simp [V, digMsg, Msg.toFp]
  exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem perm_send {rcs : List RS} (S : Shape tr rcs) (b : Nat) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b true).Perm
      ((rcptSends pub (viewOf tr rcs) b).map Msg.toFp) := by
  by_cases h1 : b = B_BYTES
  · subst h1; exact tr_bytes hL S
  by_cases h2 : b = B_KEYNIB
  · subst h2; exact tr_key hL S
  by_cases h3 : b = B_MEM
  · subst h3; exact tr_memS hL S
  by_cases h4 : b = B_RIDS
  · subst h4; exact tr_rids hL S
  by_cases h5 : b = B_MPOS
  · subst h5; exact tr_mpos hL S
  apply List.Perm.of_eq
  rw [flatMap_congr' (G := fun _ => []) (fun q _ => by rw [rowT]; simp [h1, h2, h3, h4, h5]), flatMap_nil_fun]
  simp [rcptSends, h1, h2, h3, h4, h5]

theorem perm_recv {rcs : List RS} (S : Shape tr rcs) (b : Nat) :
    ((List.range (tr.height T_RCPT)).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub b false).Perm
      ((rcptRecvs pub (viewOf tr rcs) b).map Msg.toFp) := by
  by_cases h1 : b = B_DIGEST
  · subst h1; exact tr_dig hL S
  by_cases h2 : b = B_FINAL
  · subst h2; exact tr_final hL S
  by_cases h3 : b = B_MEM
  · subst h3; exact tr_memR hL S
  apply List.Perm.of_eq
  rw [flatMap_congr' (G := fun _ => []) (fun q _ => by rw [rowT]; simp [h1, h2, h3]), flatMap_nil_fun]
  simp [rcptRecvs, h1, h2, h3]

/-- **The table's traffic.** -/
theorem traffic_of {rcs : List RS} (S : Shape tr rcs) :
    TableTraffic Rcpt.interactions tr T_RCPT pub (rcptTraffic pub (viewOf tr rcs)) := by
  intro b m
  refine ⟨?_, ?_⟩
  · rw [tableBusCount_eq]; exact (perm_send hL S b).count_eq m
  · rw [tableBusCount_eq]; exact (perm_recv hL S b).count_eq m

end ZkFormal.Near.RcptProof
