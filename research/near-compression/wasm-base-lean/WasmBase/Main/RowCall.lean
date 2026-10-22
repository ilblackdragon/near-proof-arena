import WasmBase.Main.Rows
import WasmBase.StepCall
import WasmBase.Local.Call
import WasmBase.Main.MemInit
/-!
# Row lemma: CALL (`call` of a checked function)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

theorem call_filterC :
    Call.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)) =
      chRecv 5 0 0 [v Call.r0, v Call.r1, 0, 0] (v Call.tpb) (v Call.act) ::
      (List.range 8).map (fun j => stkRecv (Call.sbNew + Expr.c j) (v (Call.tagP j)) (limbsOf (Call.P j))
        (v (Call.tP j)) (v (Call.pf j))) := by decide

theorem call_filterP :
    Call.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) =
      [chSend 5 0 0 [v Call.n0, v Call.n1, 0, 0] (v cTs) (v Call.act),
       chSend 4 (v cTs) 0 [v cPc + 1, v Call.kSb, v Call.kCid, v Call.charge] (v cTs) (v Call.act)] ++
      (List.range 8).map (fun j => chSend (16 + v cTs) (Expr.c j) (v (Call.tagP j)) (limbsOf (Call.P j)) (v cTs)
        (v (Call.pf j))) ++
      (List.range 64).map (fun j => chSend (16 + v cTs) (Expr.c j) (v (Call.tg j)) zeros4 (v cTs) (Call.lcnt j)) := by
  decide

theorem call_count_cases : ∀ i ∈ Call.inters, i.count = v Call.act ∨ (∃ j, j < 8 ∧ i.count = v (Call.pf j)) ∨
    (∃ j, j < 64 ∧ i.count = Call.lcnt j) := by
  intro i hi
  have := List.all_eq_true.mp (show Call.inters.all (fun i => decide (i.count = v Call.act) ||
    (List.range 8).any (fun j => decide (i.count = v (Call.pf j))) ||
    (List.range 64).any (fun j => decide (i.count = Call.lcnt j))) = true by decide) i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at this
  rcases this with (h | ⟨j, hj, h⟩) | ⟨j, hj, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, hj, h⟩)
  · exact Or.inr (Or.inr ⟨j, hj, h⟩)

/-- The CALL row's flags as naturals. -/
theorem call_flags_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Call.table.constraints, e.eval (natRow (rowNat tr 13 r) (tr.row pub 13 r)) = 0) :
    rowNat tr 13 r Call.act ≤ 1 ∧ rowNat tr 13 r (Call.af 0) ≤ rowNat tr 13 r Call.act ∧
    (∀ j, j < 8 → rowNat tr 13 r (Call.pf j) ≤ 1 ∧ rowNat tr 13 r (Call.pf j) ≤ rowNat tr 13 r (Call.af j)) ∧
    (∀ j, j + 1 < 8 → rowNat tr 13 r (Call.pf (j + 1)) ≤ rowNat tr 13 r (Call.pf j)) ∧
    (∀ j, j < 64 → rowNat tr 13 r (Call.af j) ≤ 1 ∧ rowNat tr 13 r (Call.tg j) ≤ 1) ∧
    (∀ j, j + 1 < 64 → rowNat tr 13 r (Call.af (j + 1)) ≤ rowNat tr 13 r (Call.af j)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := call_sound (rowNat tr 13 r) (tr.row pub 13 r) (rowNat_lt tr 13 r) hcon
  exact ⟨a1, a2, a3, a4, a5, a6⟩

theorem call_flags {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 13) :
    rowNat tr 13 r Call.act ≤ 1 ∧ rowNat tr 13 r (Call.af 0) ≤ rowNat tr 13 r Call.act ∧
    (∀ j, j < 8 → rowNat tr 13 r (Call.pf j) ≤ 1 ∧ rowNat tr 13 r (Call.pf j) ≤ rowNat tr 13 r (Call.af j)) ∧
    (∀ j, j + 1 < 8 → rowNat tr 13 r (Call.pf (j + 1)) ≤ rowNat tr 13 r (Call.pf j)) ∧
    (∀ j, j < 64 → rowNat tr 13 r (Call.af j) ≤ 1 ∧ rowNat tr 13 r (Call.tg j) ≤ 1) ∧
    (∀ j, j + 1 < 64 → rowNat tr 13 r (Call.af (j + 1)) ≤ rowNat tr 13 r (Call.af j)) :=
  call_flags_of (table_constr H (by simp [air_len]) hr)

theorem call_count_val {pub : List F} {tr : Trace} {r : Nat}
    (hf : ∀ j, j < 8 → rowNat tr 13 r (Call.pf j) ≤ rowNat tr 13 r (Call.af j)) :
    ∀ i ∈ Call.inters, (i.count.eval (tr.row pub 13 r)).toNat = rowNat tr 13 r Call.act ∨
      (∃ j, j < 8 ∧ (i.count.eval (tr.row pub 13 r)).toNat = rowNat tr 13 r (Call.pf j)) ∨
      (∃ j, j < 64 ∧ (i.count.eval (tr.row pub 13 r)).toNat =
        if j < 8 then rowNat tr 13 r (Call.af j) - rowNat tr 13 r (Call.pf j) else rowNat tr 13 r (Call.af j)) := by
  intro i hi
  rcases call_count_cases i hi with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;> rw [h]
  · left; simp only [v, Expr.eval_col, Trace.row]; rfl
  · right; left; exact ⟨j, hj, by simp only [v, Expr.eval_col, Trace.row]; rfl⟩
  · right; right
    refine ⟨j, hj, ?_⟩
    unfold Call.lcnt
    split
    · rename_i hj8
      simp only [v, Expr.eval_sub', Expr.eval_col, Trace.row]
      rw [cell_cast, cell_cast, toNat_cast_sub (hf j hj8) (rowNat_lt _ _ _ _)]
    · simp only [v, Expr.eval_col, Trace.row]; rfl

theorem call_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Call.table.constraints, e.eval (natRow (rowNat tr 13 r) (tr.row pub 13 r)) = 0) :
    ∀ i ∈ Call.inters, (i.count.eval (tr.row pub 13 r)).toNat ≤ 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := call_flags_of hcon
  intro i hi
  rcases call_count_val (pub := pub) (fun j hj => (a3 j hj).2) i hi with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;> rw [h]
  · exact a1
  · exact (a3 j hj).1
  · split
    · have := (a5 j hj).1; omega
    · exact (a5 j hj).1

theorem call_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 13) :
    ∀ i ∈ Call.inters, (i.count.eval (tr.row pub 13 r)).toNat ≤ 1 :=
  call_counts_of (table_constr H (by simp [air_len]) hr)

theorem call_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 13)
    (hna : ¬ rowAct Call.table tr pub 13 r) :
    ∀ i ∈ Call.inters, (i.count.eval (tr.row pub 13 r)).toNat ≠ 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := call_flags H hr
  have h0 : rowNat tr 13 r Call.act ≠ 1 := by
    intro h; apply hna
    simp only [rowAct, Call.table, Call.inters, stateIn, List.cons_append, List.getD_cons_zero, v, Expr.eval_col,
      Trace.row]
    exact h
  have haf : ∀ j, j < 64 → rowNat tr 13 r (Call.af j) = 0 := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih => have := a6 j hj; have := ih (by omega); omega
  intro i hi
  rcases call_count_val (pub := pub) (fun j hj => (a3 j hj).2) i hi with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;> rw [h]
  · exact h0
  · have := (a3 j hj).2; have := haf j (by omega); omega
  · have := haf j hj; split <;> omega

theorem nodup_map_inj {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (l : List α), l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_inj f hf l h.2⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact h.1 (hf b a he ▸ hb)

theorem vtTag_le (t : VT) : vtTag t ≤ 1 := by unfold vtTag; split <;> omega

theorem getD_map_vtTag_le (l : List VT) (i : Nat) : (l.map vtTag).getD i 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => simp
  | some t => simpa using vtTag_le t

theorem filterMap_congr' {β γ : Type} {f g : β → Option γ} :
    ∀ (l : List β), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | b :: l, h => by
    simp only [List.filterMap_cons]
    rw [h b List.mem_cons_self, filterMap_congr' l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filterMap_ite_map {β γ : Type} (p : β → Bool) (h : β → γ) :
    ∀ (l : List β), l.filterMap (fun j => if p j then some (h j) else none) = (l.filter p).map h
  | [] => rfl
  | b :: l => by
    simp only [List.filterMap_cons, List.filter_cons]
    by_cases hb : p b = true
    · simp only [hb, ite_true, List.map_cons, filterMap_ite_map p h l]
    · simp only [hb, Bool.false_eq_true, ite_false, filterMap_ite_map p h l]

theorem range_filter_lt (m : Nat) : ∀ n, m ≤ n → (List.range n).filter (fun j => decide (j < m)) = List.range m
  | 0, h => by have : m = 0 := by omega
               subst this; rfl
  | n + 1, h => by
    rw [List.range_succ, List.filter_append]
    by_cases hmn : m ≤ n
    · rw [range_filter_lt m n hmn]
      simp only [List.filter_cons, List.filter_nil]
      rw [if_neg (by simp; omega), List.append_nil]
    · have hm : m = n + 1 := by omega
      subst hm
      rw [List.filter_eq_self.mpr (fun j hj => by simp at hj; simp; omega)]
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, show n < n + 1 by omega, ite_true]
      rw [List.range_succ]

set_option maxHeartbeats 8000000 in
theorem call_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 13) (hact : rowAct Call.table tr pub 13 r) :
    RowFacts X (rowIn Call.table tr pub 13 r) (rowOut Call.table tr pub 13 r)
      (rowCons Call.table tr pub 13 r) (rowProd Call.table tr pub 13 r) := by
  have hP' := P_val
  have ht : 13 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 13 r i < P := rowNat_lt tr 13 r
  have hcon : ∀ e ∈ Call.table.constraints, e.eval (natRow (rowNat tr 13 r) (tr.row pub 13 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨sAct, sAf0, sPf, sPp, sAf, sAp, sShape, sMask, enp, enl, sBud, sSb, sTs⟩ :=
    call_sound (rowNat tr 13 r) (tr.row pub 13 r) hcP hcon
  rw [← row_eq_natRow] at enp enl sBud sSb sTs
  have cntA : ((v Call.act).eval (tr.row pub 13 r)).toNat = 1 := hact
  have a1 : rowNat tr 13 r Call.act = 1 := cntA
  have hocc : ∀ i ∈ Call.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 13 r)),
      (i.count.eval (tr.row pub 13 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Call.table.inters from hi)
  -- params and locals present: prefixes
  let npN := cellSum (rowNat tr 13 r) Call.pf (List.range 8)
  let nlN := cellSum (rowNat tr 13 r) Call.af (List.range 64)
  have hpfI : ∀ j, j < 8 → (rowNat tr 13 r (Call.pf j) = 1 ↔ j < npN) := fun j hj =>
    prefix_bits (fun j => rowNat tr 13 r (Call.pf j)) 8 (fun j hj => (sPf j hj).1) sPp j hj
  have hafI : ∀ j, j < 64 → (rowNat tr 13 r (Call.af j) = 1 ↔ j < nlN) := fun j hj =>
    prefix_bits (fun j => rowNat tr 13 r (Call.af j)) 64 (fun j hj => (sAf j hj).1) sAp j hj
  have hnp8 : npN ≤ 8 := by
    have := cellSum_le (rowNat tr 13 r) Call.pf 1 (List.range 8) (fun j hj => (sPf j (List.mem_range.mp hj)).1)
    simpa using this
  have hnl64 : nlN ≤ 64 := by
    have := cellSum_le (rowNat tr 13 r) Call.af 1 (List.range 64) (fun j hj => (sAf j (List.mem_range.mp hj)).1)
    simpa using this
  have hnpnl : npN ≤ nlN := by
    rcases Nat.eq_zero_or_pos npN with h0 | hpos
    · omega
    · have h1 := (hpfI (npN - 1) (by omega)).mpr (by omega)
      have h2 := (sPf (npN - 1) (by omega)).2
      have := (hafI (npN - 1) (by omega)).mp (by have := (sAf (npN - 1) (by omega)).1; omega)
      omega
  let cc : Nat → F := fun i => ((rowNat tr 13 r i : Nat) : F)
  have hsbNew : Call.sbNew.eval (tr.row pub 13 r) = cc Call.kSb + cc 3 - ((npN : Nat) : F) := by
    show tr.cell 13 r Call.kSb + tr.cell 13 r cH - Call.np.eval (tr.row pub 13 r) = _
    rw [enp, cell_cast, cell_cast]; rfl
  have hIn : rowIn Call.table tr pub 13 r = [cc 0, cc 1, cc 2, ((0 : Nat) : F), cc Call.kSb, cc Call.kCid] := by
    simp only [rowIn, Call.table, Call.inters, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cTs, cS, cc]
  have hOut : rowOut Call.table tr pub 13 r =
      [cc Call.entry, cc 1 + ((1 : Nat) : F), cc 2 + cc 4 + cc Call.pro, ((0 : Nat) : F),
        cc Call.kSb + cc 3 - ((npN : Nat) : F), cc 1] := by
    simp only [rowOut, Call.table, Call.inters, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, hsbNew]
    simp only [v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat', cell_cast, Trace.row, cPc, cTs, cS, cFee, cH, cc]
  -- consumed and produced messages
  let mB : Msg := ⟨5, 0, 0, rowNat tr 13 r Call.r0, rowNat tr 13 r Call.r1, 0, 0, rowNat tr 13 r Call.tpb⟩
  let mP : Nat → Msg := fun j => ⟨0, (cc Call.kSb + cc 3 - ((npN : Nat) : F) + ((j : Nat) : F)).toNat,
    rowNat tr 13 r (Call.tagP j), rowNat tr 13 r (Call.P j), rowNat tr 13 r (Call.P j + 1),
    rowNat tr 13 r (Call.P j + 2), rowNat tr 13 r (Call.P j + 3), rowNat tr 13 r (Call.tP j)⟩
  let mB' : Msg := ⟨5, 0, 0, rowNat tr 13 r Call.n0, rowNat tr 13 r Call.n1, 0, 0, rowNat tr 13 r 1⟩
  let mRec : Msg := ⟨4, rowNat tr 13 r 1, 0, (cc 0 + ((1 : Nat) : F)).toNat, rowNat tr 13 r Call.kSb,
    rowNat tr 13 r Call.kCid, rowNat tr 13 r Call.charge, rowNat tr 13 r 1⟩
  let lsp : Nat := (((16 : Nat) : F) + cc 1).toNat
  let mL : Nat → Msg := fun j => ⟨lsp, j, rowNat tr 13 r (Call.tagP j), rowNat tr 13 r (Call.P j),
    rowNat tr 13 r (Call.P j + 1), rowNat tr 13 r (Call.P j + 2), rowNat tr 13 r (Call.P j + 3), rowNat tr 13 r 1⟩
  let mD : Nat → Msg := fun j => ⟨lsp, j, rowNat tr 13 r (Call.tg j), 0, 0, 0, 0, rowNat tr 13 r 1⟩
  have z5 : (((5 : Nat) : F)).toNat = 5 := Fp.toNat_cast_of_lt (by omega)
  have z4 : (((4 : Nat) : F)).toNat = 4 := Fp.toNat_cast_of_lt (by omega)
  have z0 : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by omega)
  have hjc : ∀ j, j < 64 → (((j : Nat) : F)).toNat = j := fun j hj => Fp.toNat_cast_of_lt (by omega)
  have hCons : rowCons Call.table tr pub 13 r = mB :: (List.range npN).map mP := by
    rw [rowCons, rowMsgs_eq]
    show (List.filterMap _ (Call.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)))).map decMsg = _
    rw [call_filterC, List.filterMap_cons]
    simp only [chRecv, cntA, ite_true, List.filterMap_map]
    rw [filterMap_congr' (g := fun j => if decide (j < npN) = true then some ((stkRecv (Call.sbNew + Expr.c j)
        (v (Call.tagP j)) (limbsOf (Call.P j)) (v (Call.tP j)) (v (Call.pf j))).msg.map (·.eval (tr.row pub 13 r)))
        else none) (List.range 8) (fun j hj => by
      rw [List.mem_range] at hj
      simp only [Function.comp, stkRecv, chRecv, v, Expr.eval_col, Trace.row]
      simp only [show (tr.cell 13 r (Call.pf j)).toNat = rowNat tr 13 r (Call.pf j) from rfl]
      by_cases hjn : j < npN
      · rw [if_pos ((hpfI j hj).mpr hjn), if_pos (by simpa using hjn)]
      · rw [if_neg (fun h => hjn ((hpfI j hj).mp h)), if_neg (by simpa using hjn)])]
    rw [filterMap_ite_map, range_filter_lt npN 8 hnp8, List.map_cons, List.map_map]
    have hhead : decMsg ((([5, 0, 0] ++ [v Call.r0, v Call.r1, 0, 0] ++ [v Call.tpb]) : List Expr).map
        (·.eval (tr.row pub 13 r))) = mB := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_col, Expr.eval_ofNat',
        cell_cast, Trace.row, decMsg, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _),
        z0, z5, mB]
    rw [hhead]
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp, stkRecv, chRecv, limbsOf, List.range, List.range.loop, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Expr.eval_add', Expr.eval_c, hsbNew]
    simp only [v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Nat.reduceAdd, Nat.add_zero, decMsg,
      List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _), z0, mP, cc]
  have hlc : ∀ j, j < 64 → (((Call.lcnt j).eval (tr.row pub 13 r)).toNat = 1 ↔ (npN ≤ j ∧ j < nlN)) := by
    intro j hj
    unfold Call.lcnt
    split
    · rename_i hj8
      simp only [v, Expr.eval_sub', Expr.eval_col, Trace.row]
      rw [cell_cast, cell_cast, toNat_cast_sub (sPf j hj8).2 (hcP _)]
      have h1 := hpfI j hj8; have h2 := hafI j hj
      have b1 := (sPf j hj8).1; have b2 := (sAf j hj).1; have b3 := (sPf j hj8).2
      constructor
      · intro h; constructor <;> omega
      · intro ⟨h3, h4⟩; omega
    · rename_i hj8
      simp only [v, Expr.eval_col, Trace.row]
      show rowNat tr 13 r (Call.af j) = 1 ↔ _
      rw [hafI j hj]; constructor
      · intro h; exact ⟨by omega, h⟩
      · intro h; exact h.2
  have hProd : rowProd Call.table tr pub 13 r = mB' :: mRec :: ((List.range npN).map mL ++
      ((List.range 64).filter (fun j => decide (npN ≤ j ∧ j < nlN))).map mD) := by
    rw [rowProd, rowMsgs_eq]
    show (List.filterMap _ (Call.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)))).map decMsg = _
    rw [call_filterP, List.filterMap_append, List.filterMap_append, List.filterMap_cons, List.filterMap_cons,
      List.filterMap_nil]
    simp only [chSend, cntA, ite_true, List.filterMap_map]
    rw [filterMap_congr' (g := fun j => if decide (j < npN) = true then some ((chSend (16 + v cTs) (Expr.c j)
        (v (Call.tagP j)) (limbsOf (Call.P j)) (v cTs) (v (Call.pf j))).msg.map (·.eval (tr.row pub 13 r)))
        else none) (List.range 8) (fun j hj => by
      rw [List.mem_range] at hj
      simp only [Function.comp, chSend, v, Expr.eval_col, Trace.row]
      simp only [show (tr.cell 13 r (Call.pf j)).toNat = rowNat tr 13 r (Call.pf j) from rfl]
      by_cases hjn : j < npN
      · rw [if_pos ((hpfI j hj).mpr hjn), if_pos (by simpa using hjn)]
      · rw [if_neg (fun h => hjn ((hpfI j hj).mp h)), if_neg (by simpa using hjn)])]
    rw [filterMap_congr' (g := fun j => if decide (npN ≤ j ∧ j < nlN) = true then some ((chSend (16 + v cTs)
        (Expr.c j) (v (Call.tg j)) zeros4 (v cTs) (Call.lcnt j)).msg.map (·.eval (tr.row pub 13 r))) else none)
        (List.range 64) (fun j hj => by
      rw [List.mem_range] at hj
      simp only [Function.comp, chSend]
      by_cases hjn : npN ≤ j ∧ j < nlN
      · rw [if_pos ((hlc j hj).mpr hjn), if_pos (by simpa using hjn)]
      · rw [if_neg (fun h => hjn ((hlc j hj).mp h)), if_neg (by simpa using hjn)])]
    rw [filterMap_ite_map, filterMap_ite_map, range_filter_lt npN 8 hnp8]
    have hh1 : decMsg ((([5, 0, 0] ++ [v Call.n0, v Call.n1, 0, 0] ++ [v cTs]) : List Expr).map
        (·.eval (tr.row pub 13 r))) = mB' := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_col, Expr.eval_ofNat',
        cell_cast, Trace.row, cTs, decMsg, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _),
        z0, z5, mB']
    have hh2 : decMsg ((([4, v cTs, 0] ++ [v cPc + 1, v Call.kSb, v Call.kCid, v Call.charge] ++ [v cTs]) : List Expr).map
        (·.eval (tr.row pub 13 r))) = mRec := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_col, Expr.eval_ofNat',
        Expr.eval_add', cell_cast, Trace.row, cTs, cPc, decMsg, List.getD_cons_zero, List.getD_cons_succ,
        Fp.toNat_cast_of_lt (hcP _), z0, z4, mRec, cc]
    rw [List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_nil, hh1, hh2, List.map_map,
      List.map_map]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    congr 2
    congr 1
    · apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      simp only [Function.comp, chSend, limbsOf, List.range, List.range.loop, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Expr.eval_add', Expr.eval_c, Expr.eval_ofNat', v, Expr.eval_col,
        cell_cast, Trace.row, Nat.reduceAdd, Nat.add_zero, cTs, decMsg, List.getD_cons_zero, List.getD_cons_succ,
        Fp.toNat_cast_of_lt (hcP _), hjc j (by omega), mL, lsp, cc]
    · apply List.map_congr_left
      intro j hj
      simp only [List.mem_filter, List.mem_range] at hj
      simp only [Function.comp, chSend, zeros4, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Expr.eval_add', Expr.eval_c, Expr.eval_ofNat', v, Expr.eval_col,
        cell_cast, Trace.row, cTs, decMsg, List.getD_cons_zero, List.getD_cons_succ,
        Fp.toNat_cast_of_lt (hcP _), hjc j hj.1, z0, mD, lsp, cc]
  -- the FETCH query: a call record
  have hfetch := hocc (fetch (v cPc) (Expr.c Call.opCall) (v cH) (v cFee) [v Call.entry, 0, 0, 0] (v Call.act))
    (by simp [Call.inters])
  simp only [fetch, cntA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  rw [hre] at hm
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_c,
    Expr.eval_ofNat', cell_cast, Trace.row, cPc, cH, cFee, Call.entry, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, ex0, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 13 r 4 = fee := natEq efee (hcP _) (by omega)
  have hopC : op = opCall := by
    have hoplt := recordOf_op_lt hrc
    rw [hre] at hoplt; simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
    exact (natEq eop (by simp [Call.opCall]; omega) (by omega)).symm
  have hcall : ∃ fi, ins = .call fi ∧ X.cinfo fi = some x0 := by
    rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ |
      ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨fi, hfi, hci, -, -⟩
    all_goals first
      | exact ⟨fi, hfi, hci⟩
      | (exfalso; rw [hopC] at h; revert h; simp [opCall, Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif])
      | (exfalso; rw [hopC] at hf; revert hf; decide)
      | (exfalso; rw [hopC] at hmem; simp [opCall] at hmem)
  obtain ⟨fi, hfi, hci⟩ := hcall
  obtain ⟨kc, hkc, hfik, hoffk⟩ := cinfo_spec X hci
  have eentry : rowNat tr 13 r Call.entry = x0 := natEq ex0 (hcP _) (by
    have := X.off_bound hkc; have := X.mf.total; omega)
  -- the FUNC query: the callee's function-table row
  have hfq := hocc ⟨busFunc, true, v Call.act, [v Call.entry, v Call.shape, v Call.charge, v Call.pro,
    v (Call.m 0), v (Call.m 1), v (Call.m 2), v (Call.m 3)]⟩ (by simp [Call.inters])
  simp only [cntA] at hfq
  obtain ⟨k', hk', hfm⟩ := L.func _ hfq rfl rfl rfl
  have CFk := X.factsOf hk'
  simp only [funcRec, X.mf.funcs k' hk', funcRow, limbs4, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, v, Expr.eval_col, Trace.row, List.cons.injEq, and_true] at hfm
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := hfm
  rw [cell_cast] at f0 f1 f2 f3 f4 f5 f6 f7
  have hnpk := CFk.np; have hnlk := CFk.nl; have hchk := CFk.charge; have hprk := CFk.prologue
  have hplk := CFk.prologueLt; have hcgk := CFk.chargeLt; have hparK := CFk.params; have hnlK := CFk.nloc
  have q0 : rowNat tr 13 r Call.entry = X.offOf k' := natEq f0 (hcP _) (by
    have := X.off_bound hk'; have := X.mf.total; unfold Ctx.offOf at *; omega)
  have hkk : k' = kc := by
    have h0k := (X.factsOf hk').h0; have h0c := (X.factsOf hkc).h0
    have sz : ∀ k, k < X.nf → 0 < (X.pfOf k).code.size := fun k hk => by
      have := (X.factsOf hk).h0; rw [← (X.factsOf hk).hsize]
      rcases h : (X.ckOf k).heights[0]? with _ | x
      · rw [h] at this; simp at this
      · exact (Array.getElem?_eq_some_iff.mp h).1
    exact (X.loc_unique hk' (sz k' hk') hkc (sz kc hkc) (by rw [Nat.add_zero, Nat.add_zero, ← q0, eentry, hoffk])).1
  subst hkk
  have q1 : rowNat tr 13 r Call.shape = (X.ckOf k').np + 128 * (X.ckOf k').nl := natEq f1 (hcP _) (by omega)
  have hnpE : npN = (X.pfOf k').type.params.size := by omega
  have hnlE : nlN = (X.pfOf k').type.params.size + (X.pfOf k').locals.size := by omega
  have q2 : rowNat tr 13 r Call.charge = (X.pfOf k').stackCharge := by
    rw [← hchk]; exact natEq f2 (hcP _) (by omega)
  have q3 : rowNat tr 13 r Call.pro = (X.ckOf k').prologue := natEq f3 (hcP _) (by omega)
  -- the type bits are the callee's local tags
  have htags : ∀ j, j < 64 → rowNat tr 13 r (Call.tg j) = (X.ckOf k').localTags.getD j 0 := by
    apply mask_bits
    · intro i; rw [CFk.localTags]; exact getD_map_vtTag_le _ i
    · exact fun j hj => (sAf j hj).2
    · intro q hq
      have hm := sMask q hq
      simp only [wSum] at hm
      rw [← hm]
      rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl
      · exact natEq f4 (hcP _) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega))
      · exact natEq f5 (hcP _) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega))
      · exact natEq f6 (hcP _) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega))
      · exact natEq f7 (hcP _) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega))
  -- range checks of the row
  have rr : ∀ e : Expr, r16 e (v Call.act) ∈ Call.inters → (e.eval (tr.row pub 13 r)).toNat < 65536 :=
    fun e he => row_r16 L ht hr e (v Call.act) (show r16 e (v Call.act) ∈ Call.table.inters from he) cntA
  have rN : ∀ i, r16 (v i) (v Call.act) ∈ Call.inters → rowNat tr 13 r i < 65536 := fun i hi => by
    have := rr (v i) hi; simp only [v, Expr.eval_col, Trace.row] at this; exact this
  have rM : ∀ (e : Expr) (i k : Nat), k * rowNat tr 13 r i < P →
      e.eval (tr.row pub 13 r) = ((k : Nat) : F) * ((rowNat tr 13 r i : Nat) : F) →
      r16 e (v Call.act) ∈ Call.inters → k * rowNat tr 13 r i < 65536 := fun e i k hk he h2 => by
    have := rr _ h2
    rw [he, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt hk] at this
    exact this
  have bn0 := rN Call.n0 (by simp [Call.inters])
  have bn1' := rN Call.n1 (by simp [Call.inters])
  have bn1 := rM (4 * v Call.n1) Call.n1 4 (by omega) (by
    simp only [v, Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Trace.row]; rw [cell_cast]) (by simp [Call.inters])
  have bs0 := rN Call.sbn0 (by simp [Call.inters])
  have bs1' := rN Call.sbn1 (by simp [Call.inters])
  have bs1 := rM (16 * v Call.sbn1) Call.sbn1 16 (by omega) (by
    simp only [v, Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Trace.row]; rw [cell_cast]) (by simp [Call.inters])
  have bt0 := rN Call.ts0 (by simp [Call.inters])
  have bt1' := rN Call.ts1 (by simp [Call.inters])
  have bt1 := rM (16 * v Call.ts1) Call.ts1 16 (by omega) (by
    simp only [v, Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Trace.row]; rw [cell_cast]) (by simp [Call.inters])
  have hts : rowNat tr 13 r 1 = rowNat tr 13 r Call.ts0 + 65536 * rowNat tr 13 r Call.ts1 := by
    have h := sTs
    simp only [Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat', B16, cTs, Trace.row] at h
    rw [cell_cast, cell_cast, cell_cast] at h
    have e : ((rowNat tr 13 r 1 : Nat) : F) = ((rowNat tr 13 r Call.ts0 + 65536 * rowNat tr 13 r Call.ts1 : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
    exact natEq e (hcP _) (by omega)
  have hlsp : lsp = 16 + rowNat tr 13 r 1 := by
    show (((16 : Nat) : F) + ((rowNat tr 13 r 1 : Nat) : F)).toNat = _
    rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]
  -- channel time checks
  have tchk : ∀ (cnt : Expr) (tpc hic : Nat), (cnt.eval (tr.row pub 13 r)).toNat = 1 →
      r16 (v cTs - v tpc - 1 - B16 * v hic) cnt ∈ Call.inters → r16 (4 * v hic) cnt ∈ Call.inters →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 13 r tpc + 1 + n : Nat) : F) = ((rowNat tr 13 r 1 : Nat) : F) := by
    intro cnt tpc hic hc m1 m2
    have h1 := hocc _ m1
    have h2 := hocc _ m2
    simp only [r16, hc] at h1 h2
    simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat',
      B16, cTs, Trace.row] at h1 h2
    obtain ⟨n, hn, e⟩ := time_chk L h1 h2
    exact ⟨n, hn, e.trans (cell_cast tr 13 r 1)⟩
  -- the fee bound
  obtain ⟨ins', fee'', hins', hfee', hfl', -⟩ := CF.recs l hl
  have hfee2 : fee'' = fee := by rw [hfee] at hfee'; exact (Option.some.inj hfee').symm
  have hfeeK : fee + (X.ckOf k').prologue ≤ X.maxFee := by have := X.callFee_le hq hk'; omega
  have mtc : ∀ j, j < 8 → r16 (v cTs - v (Call.tP j) - 1 - B16 * v (Call.hP j)) (v (Call.pf j)) ∈ Call.inters ∧
      r16 (4 * v (Call.hP j)) (v (Call.pf j)) ∈ Call.inters := by
    intro j hj
    constructor <;> unfold Call.inters <;>
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        by simp [timeChk]⟩))
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee + (X.ckOf k').prologue, hfeeK, ?_⟩, ?_, ?_, ?_⟩
  rotate_left
  · rw [hIn, hOut]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, cc, efee', q3, Lean.Grind.Semiring.natCast_add]
    grind
  · rw [hCons, hIn]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact tchk (v Call.act) Call.tpb Call.hb cntA (by simp [Call.inters, timeChk]) (by simp [Call.inters, timeChk])
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hj
      have hc : ((v (Call.pf j)).eval (tr.row pub 13 r)).toNat = 1 := (hpfI j (by omega)).mpr hj
      exact tchk (v (Call.pf j)) (Call.tP j) (Call.hP j) hc (mtc j (by omega)).1 (mtc j (by omega)).2
  · rw [hProd, hIn]
    intro x hx
    have : x.tp = rowNat tr 13 r 1 := by
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hx
      rcases hx with rfl | rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;> rfl
    rw [this]; exact ⟨hcP _, rfl⟩
  · rw [hProd]
    have hA : ((List.range npN).map mL).Nodup := by
      refine nodup_map_inj _ (fun a b hab => ?_) _ List.nodup_range
      have := congrArg Msg.slot hab; simpa [mL] using this
    have hB : (((List.range 64).filter (fun j => decide (npN ≤ j ∧ j < nlN))).map mD).Nodup := by
      refine nodup_map_inj _ (fun a b hab => ?_) _ (List.nodup_range.filter _)
      have := congrArg Msg.slot hab; simpa [mD] using this
    have hsp : ∀ x ∈ (List.range npN).map mL ++ ((List.range 64).filter (fun j => decide (npN ≤ j ∧ j < nlN))).map mD,
        x.space = lsp := by
      intro x hx
      simp only [List.mem_append, List.mem_map] at hx
      rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;> rfl
    rw [List.nodup_cons, List.nodup_cons, List.nodup_append]
    refine ⟨fun h => ?_, fun h => ?_, hA, hB, fun x hx y hy hxy => ?_⟩
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · have := congrArg Msg.space h; simp [mB', mRec] at this
      · have := hsp _ h; simp only [mB'] at this; omega
    · have := hsp _ h; simp only [mRec] at this; omega
    · subst hxy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j', hj', he⟩ := List.mem_map.mp hy
      have := congrArg Msg.slot he
      simp only [mL, mD] at this
      simp only [List.mem_range] at hj
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj'
      omega
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : rowNat tr 13 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 13 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 13 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 13 r Call.kSb = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 13 r Call.kCid = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
  have hsbR := R.sbLe
  have hpc : pc0 = X.offOf E.k + pc := natEq (e0.symm.trans i0) (by omega) (by omega)
  subst hpc
  obtain ⟨hqk, hlpc⟩ := X.loc_unique hq hl R.kLt hpcl hoff
  subst q
  subst l
  have hH := R.height
  have hHb := CF.hBound pc hpcl
  rw [hH] at eh hHb
  simp only [Option.getD_some] at eh hHb
  have p3 : rowNat tr 13 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  subst hfi
  obtain ⟨np', ar', hsig, hnp', hnext, hL1, hH1⟩ := verify_call X R.kLt hpcl hins hL0 hH
  obtain ⟨enp, ear⟩ := sigOf_callee X hk' hfik hsig
  -- the new base, the clock
  have hnpS : npN ≤ s.stack.size - E.sb := by omega
  have hsbF : Call.sbNew.eval (tr.row pub 13 r) = ((s.stack.size - npN : Nat) : F) := by
    rw [hsbNew]; simp only [cc, psb, p3]
    have e1 : ((E.sb : Nat) : F) + ((s.stack.size - E.sb : Nat) : F) =
        ((s.stack.size - npN : Nat) : F) + ((npN : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add]; congr 1; omega
    rw [e1]; grind
  have hbase28 : s.stack.size - npN < 2 ^ 28 := by
    have h := sSb
    rw [Expr.eval_sub', Expr.eval_sub', hsbF] at h
    simp only [Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat', B16, Trace.row] at h
    rw [cell_cast, cell_cast] at h
    have e : ((s.stack.size - npN : Nat) : F) = ((rowNat tr 13 r Call.sbn0 + 65536 * rowNat tr 13 r Call.sbn1 : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
    have := natEq e (by omega) (by omega)
    omega
  have ht28 : t < 2 ^ 28 := by omega
  -- the budget register
  obtain ⟨tpb0, htpb0, hbudE⟩ := R.calls.budget
  obtain ⟨sv, hch, -, -, hrl⟩ := R.calls.chain
  have hrem30 : s.stackRem < 2 ^ 30 := by omega
  rw [hCons] at hlive
  have hmB := hlive mB List.mem_cons_self
  have hmBeq : mB = budMsg s.stackRem tpb0 :=
    (hbudE mB rfl).mp (R.env_msg hmB (by simp [mB]) (by simp [mB, Env.lsp]; omega))
  have hr0 : rowNat tr 13 r Call.r0 = s.stackRem % 65536 := by
    have := congrArg Msg.l0 hmBeq; simpa [mB, budMsg] using this
  have hr1 : rowNat tr 13 r Call.r1 = s.stackRem / 65536 := by
    have := congrArg Msg.l1 hmBeq; simpa [mB, budMsg] using this
  have hcg := (X.factsOf hk').chargeLt
  have hbudN : rowNat tr 13 r Call.n0 + 65536 * rowNat tr 13 r Call.n1 + (X.pfOf k').stackCharge = s.stackRem := by
    have h := sBud
    simp only [Expr.eval_sub', Expr.eval_add', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat', B16,
      Trace.row] at h
    rw [cell_cast, cell_cast, cell_cast, cell_cast, cell_cast, hr0, hr1, q2] at h
    have e : ((rowNat tr 13 r Call.n0 + 65536 * rowNat tr 13 r Call.n1 + (X.pfOf k').stackCharge : Nat) : F) =
        ((s.stackRem % 65536 + 65536 * (s.stackRem / 65536) : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
    have := natEq e (by omega) (by omega)
    omega
  have hremC : (X.pfOf k').stackCharge ≤ s.stackRem := by omega
  have hmBl : live (budMsg s.stackRem tpb0) := hmBeq ▸ hmB
  have hmB' : mB' = budMsg (s.stackRem - (X.pfOf k').stackCharge) t := by
    simp only [mB', budMsg, Msg.mk.injEq, true_and]
    exact ⟨by omega, by omega, p1⟩
  -- the params
  have hmP : ∀ j, j < npN → mP j = enc 0 (s.stack.size - npN + j)
      (s.stack[s.stack.size - npN + j]?.getD default) (tps (s.stack.size - npN + j)) := by
    intro j hj
    have hl := hlive (mP j) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    have hsl : (mP j).slot = s.stack.size - npN + j := by
      show (cc Call.kSb + cc 3 - ((npN : Nat) : F) + ((j : Nat) : F)).toNat = _
      rw [← hsbNew, hsbF, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]
    exact (R.stack_dec hl rfl hsl (by omega)).1
  -- the callee's locals
  have CFc := X.factsOf hk'
  have hnewSz : (s.stack.extract (s.stack.size - npN) s.stack.size ++ (X.pfOf k').locals.map Val.default).size = nlN := by
    simp only [Array.size_append, Array.size_extract, Array.size_map, Nat.min_self]; omega
  have hlocA : ∀ j, j < npN → (s.stack.extract (s.stack.size - npN) s.stack.size ++ (X.pfOf k').locals.map Val.default)[j]?.getD default = s.stack[s.stack.size - npN + j]?.getD default := by
    intro j hj
    rw [Array.getElem?_append_left (by simp [Array.size_extract]; omega), Array.getElem?_extract,
      if_pos (by rw [Nat.min_self]; omega)]
  have hlocB : ∀ j, npN ≤ j → j < nlN → ∃ ty, (X.pfOf k').locals[j - npN]? = some ty ∧
      (s.stack.extract (s.stack.size - npN) s.stack.size ++ (X.pfOf k').locals.map Val.default)[j]?.getD default = Val.default ty ∧ (ty = .i32 ∨ ty = .i64) := by
    intro j h1 h2
    have hj' : j - npN < (X.pfOf k').locals.size := by omega
    refine ⟨(X.pfOf k').locals[j - npN], Array.getElem?_eq_getElem hj', ?_,
      CFc.locTypes _ (Array.getElem_mem_toList hj')⟩
    rw [Array.getElem?_append_right (by simp [Array.size_extract]; omega)]
    have hsz : (s.stack.extract (s.stack.size - npN) s.stack.size).size = npN := by
      simp [Array.size_extract]; omega
    rw [hsz, Array.getElem?_map, Array.getElem?_eq_getElem hj']
    rfl
  have hmLeq : ∀ j, j < npN → mL j = enc (16 + t) j ((s.stack.extract (s.stack.size - npN) s.stack.size ++ (X.pfOf k').locals.map Val.default)[j]?.getD default) t := by
    intro j hj
    rw [hlocA j hj]
    have e := hmP j hj
    have e2 := congrArg Msg.tag e; have e3 := congrArg Msg.l0 e; have e4 := congrArg Msg.l1 e
    have e5 := congrArg Msg.l2 e; have e6 := congrArg Msg.l3 e
    simp only [mP, enc] at e2 e3 e4 e5 e6
    simp only [mL, enc, Msg.mk.injEq, hlsp, p1, true_and, and_true]
    exact ⟨e2, e3, e4, e5, e6⟩
  have hmDeq : ∀ j, npN ≤ j → j < nlN → mD j = enc (16 + t) j ((s.stack.extract (s.stack.size - npN) s.stack.size ++ (X.pfOf k').locals.map Val.default)[j]?.getD default) t := by
    intro j h1 h2
    obtain ⟨ty, hty, hv, hty2⟩ := hlocB j h1 h2
    rw [hv]
    have htg := htags j (by omega)
    rw [CFc.localTags, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append_right (by simp; omega)]
      at htg
    simp only [Array.length_toList, ← hnpE, Array.getElem?_toList, hty, Option.map_some, Option.getD_some] at htg
    simp only [mD, enc, Msg.mk.injEq, hlsp, p1, htg]
    rcases hty2 with rfl | rfl <;> refine ⟨trivial, trivial, rfl, rfl, rfl, rfl, rfl, trivial⟩
  -- the output state and the step
  have hsb5 : cc Call.kSb + cc 3 - ((npN : Nat) : F) = ((s.stack.size - npN : Nat) : F) := hsbNew.symm.trans hsbF
  have hout : rowOut Call.table tr pub 13 r =
      stMsg (X.offOf k' + 0) (t + 1) (S + (fee + (X.ckOf k').prologue)) 0 (s.stack.size - npN) t := by
    rw [hOut, hsb5]
    simp only [stMsg, cc, q0, p1, p2, efee', q3, Nat.add_zero, Lean.Grind.Semiring.natCast_add, List.cons.injEq,
      and_true]
    exact ⟨trivial, trivial, by grind⟩
  refine ⟨k', 0, fee + (X.ckOf k').prologue, 0, s.stack.size - npN, t, hfeeK, by omega, hout,
    fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  obtain ⟨hstep, hrel⟩ := step_call X R hins hfee hk' hfik hg hg64 hremC (by rw [← hnpE]; exact hbase28) ht28 hmBl
  refine ⟨_, hstep, ?_⟩
  rw [← hnpE] at hrel
  rw [hCons, hProd]
  refine (Rel_congr hrel (stepLive_congr ?_ ?_))
  · intro x
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.mem_nil_iff, or_false]
    constructor
    · rintro (⟨d, hd, rfl⟩ | rfl)
      · right; exact ⟨d, hd, hmP d hd⟩
      · left; exact hmBeq.symm
    · rintro (rfl | ⟨d, hd, rfl⟩)
      · right; exact hmBeq
      · left; exact ⟨d, hd, (hmP d hd).symm⟩
  · intro x
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
    have hrec : mRec = callMsg t (X.offOf E.k + (pc + 1)) E.sb E.cid (X.pfOf k').stackCharge t := by
      simp only [mRec, callMsg, Msg.mk.injEq, p1, psb, pcid, q2, true_and, and_true]
      show (cc 0 + ((1 : Nat) : F)).toNat = _
      simp only [cc, p0]; rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]; omega
    rw [hrec, hmB', mem_localView, hnewSz]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl | rfl)
      · by_cases hjn : j < npN
        · right; right; left; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hjn, hmLeq j hjn⟩
        · right; right; right
          exact List.mem_map.mpr ⟨j, by simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]; omega,
            hmDeq j (by omega) hj⟩
      · right; left; rfl
      · left; rfl
    · rintro (rfl | rfl | (h | h))
      · right; right; rfl
      · right; left; rfl
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        rw [List.mem_range] at hj
        exact Or.inl ⟨j, by omega, hmLeq j hj⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
        exact Or.inl ⟨j, hj.2.2, hmDeq j hj.2.1 hj.2.2⟩

end WasmBase
