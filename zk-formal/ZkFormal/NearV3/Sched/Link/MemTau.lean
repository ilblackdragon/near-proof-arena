import ZkFormal.NearV3.Sched.Link.MemSend

/-!
# ZkFormal.NearV3.Sched.Link.MemTau — the addresses of an instance: `INIT`s and times

Stage B step 2 (memory side). Instance τ with `n ≤ 64` participants owns the addresses
`τ·2^14 + x` with `idxOk n x`: links `x < n²`, senders `4096 + s`, receivers `8192 + r`
(`s, r < n`); `QT τ n` is this set.

* `initRec`, `initMsgs`: the expected `INIT` messages of τ: links
  `(a, 0, 0, allowed[l], st.allowance[l], st.granted[l], 0, 1)` (the codec's `c = 1`), budgets
  `(a, 0, 0, 0, st.senderBudget[s] / st.receiverBudget[r], 0, 0, 0)` (`Gen.Mem.expectedInit`);
* **`InitVals`** (the agreed `hInitVals`, from the codec / distribute stage): the `INIT`
  messages sent on `SOP` with an address in τ's range are, as a multiset, `initMsgs`;
* **`initOnce_of`**: `InitVals ⇒ InitOnceQ (QT τ n)`; `init_row_msg`: an `INIT` memory row of a
  τ address has the expected message; **`init_row_isL`**: its `isL = [link address]` (the
  `INIT` row's `c = isL` is message position 7); `init_exists`, **`memInit_tau`**: every τ address has
  its `INIT` row and `memInit a = rd τ st a`;
* **`mem_timeQ`**: `TimeQ (QT τ n)` — `INIT` rows at 0, process GRANTs `< T0 + 2^22`,
  scan READs `≤ 2^16` (`op_sent`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## The addresses and the expected `INIT`s -/

/-- Offsets of the addresses of an instance with `n` participants. -/
def idxOk (n x : Nat) : Bool :=
  decide (x < n * n ∨ (4096 ≤ x ∧ x < 4096 + n) ∨ (8192 ≤ x ∧ x < 8192 + n))

/-- The addresses of instance τ. -/
def QT (τ n a : Nat) : Bool := decide (τ * 16384 ≤ a) && idxOk n (a - τ * 16384)

/-- The state value at address `a` of instance τ. -/
def rd (τ : Nat) (S : St) (a : Nat) : Nat :=
  if a - τ * 16384 < 4096 then S.allowance[a - τ * 16384]!
  else if a - τ * 16384 < 8192 then S.senderBudget[a - τ * 16384 - 4096]!
  else S.receiverBudget[a - τ * 16384 - 8192]!

/-- The expected `INIT` record of offset `x`. -/
def initRec (τ : Nat) (allowed : Array Bool) (st : St) (x : Nat) : List Nat :=
  [τ * 16384 + x, 0, OP_INIT, if x < 4096 then (if allowed[x]! then 1 else 0) else 0,
    rd τ st (τ * 16384 + x), if x < 4096 then st.granted[x]! else 0, 0, if x < 4096 then 1 else 0]

def initMsgs (τ n : Nat) (allowed : Array Bool) (st : St) : List (List Fp) :=
  ((List.range 12288).filter (idxOk n)).map fun x => (initRec τ allowed st x).map Fp.ofNat

/-- An `INIT` message with an address in τ's range. -/
def isTauInit (τ : Nat) (m : List Fp) : Bool :=
  m[2]? == some 0 && m.head?.any (fun a => decide (τ * 16384 ≤ a.toNat ∧ a.toNat < τ * 16384 + 16384))

/-- **`hInitVals`**: the `INIT` messages of τ's address range sent on `SOP` are `initMsgs`. -/
def InitVals (AP : AirP) (tr : Trace Fp) (pub : List Fp) (τ n : Nat) (allowed : Array Bool)
    (st : St) : Prop :=
  ((sopSent AP tr pub).filter (isTauInit τ)).Perm (initMsgs τ n allowed st)

/-- Value bound of the state arrays. -/
def ABnd (B : Nat) (S : St) : Prop :=
  ∀ i : Nat, S.senderBudget[i]! ≤ B ∧ S.receiverBudget[i]! ≤ B ∧ S.allowance[i]! ≤ B

section
variable {τ n : Nat}

theorem idxOk_lt (hn : n ≤ 64) {x : Nat} (h : idxOk n x = true) : x < 12288 := by
  have := Nat.mul_le_mul hn hn
  simp only [idxOk, decide_eq_true_eq] at h; omega

theorem QT_iff {a : Nat} : QT τ n a = true ↔ τ * 16384 ≤ a ∧ idxOk n (a - τ * 16384) = true := by
  simp [QT]

theorem QT_range (hn : n ≤ 64) {a : Nat} (h : QT τ n a = true) :
    τ * 16384 ≤ a ∧ a < τ * 16384 + 16384 := by
  obtain ⟨h1, h2⟩ := QT_iff.1 h
  have := idxOk_lt hn h2; omega

theorem QT_link (hn : n ≤ 64) {l : Nat} (hl : l < n * n) : QT τ n (addrOf τ 0 l) = true := by
  have := Nat.mul_le_mul hn hn
  rw [QT_iff]; refine ⟨by unfold addrOf; omega, ?_⟩
  rw [show addrOf τ 0 l - τ * 16384 = l by unfold addrOf; omega]
  simp only [idxOk, decide_eq_true_eq]; omega

theorem QT_snd (hn : n ≤ 64) {s : Nat} (hs : s < n) : QT τ n (addrOf τ 1 s) = true := by
  have := Nat.mul_le_mul hn hn
  rw [QT_iff]; refine ⟨by unfold addrOf; omega, ?_⟩
  rw [show addrOf τ 1 s - τ * 16384 = 4096 + s by unfold addrOf; omega]
  simp only [idxOk, decide_eq_true_eq]; omega

theorem QT_rcv (hn : n ≤ 64) {r : Nat} (hr : r < n) : QT τ n (addrOf τ 2 r) = true := by
  have := Nat.mul_le_mul hn hn
  rw [QT_iff]; refine ⟨by unfold addrOf; omega, ?_⟩
  rw [show addrOf τ 2 r - τ * 16384 = 8192 + r by unfold addrOf; omega]
  simp only [idxOk, decide_eq_true_eq]; omega

theorem rd_link (S : St) (hn : n ≤ 64) {l : Nat} (hl : l < n * n) : rd τ S (addrOf τ 0 l) = S.allowance[l]! := by
  have := Nat.mul_le_mul hn hn
  unfold rd; rw [show addrOf τ 0 l - τ * 16384 = l by unfold addrOf; omega, if_pos (by omega)]

theorem rd_snd (S : St) (hn : n ≤ 64) {s : Nat} (hs : s < n) : rd τ S (addrOf τ 1 s) = S.senderBudget[s]! := by
  unfold rd; rw [show addrOf τ 1 s - τ * 16384 = 4096 + s by unfold addrOf; omega, if_neg (by omega),
    if_pos (by omega), show 4096 + s - 4096 = s by omega]

theorem rd_rcv (S : St) (hn : n ≤ 64) {r : Nat} (hr : r < n) : rd τ S (addrOf τ 2 r) = S.receiverBudget[r]! := by
  unfold rd; rw [show addrOf τ 2 r - τ * 16384 = 8192 + r by unfold addrOf; omega, if_neg (by omega),
    if_neg (by omega), show 8192 + r - 8192 = r by omega]

theorem rd_le {B : Nat} {S : St} (h : ABnd B S) (a : Nat) : rd τ S a ≤ B := by
  unfold rd; split
  · exact (h _).2.2
  · split
    · exact (h _).1
    · exact (h _).2.1

theorem initRec_lt {allowed : Array Bool} {st : St} (hτ : τ < 256) (hB : ABnd 4500000 st)
    (hG : ∀ l : Nat, st.granted[l]! ≤ 4500000) {x : Nat} (hx : x < 12288) :
    ∀ y ∈ initRec τ allowed st x, y < 2013265921 := by
  intro y hy
  have := rd_le (τ := τ) hB (τ * 16384 + x)
  have := hG x
  simp only [initRec, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with h | h | h | h | h | h | h | h <;> subst h <;> (try split) <;> (try split) <;>
    (try simp only [OP_INIT]) <;> omega

end

/-! ## `InitOnce` on τ's addresses -/

theorem countP_le_one {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) (x : β) :
    ∀ {l : List α}, (l.map g).Nodup → l.countP (fun m => g m == x) ≤ 1
  | [], _ => by simp
  | y :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.countP_cons]
    by_cases hy : g y = x
    · have : l.countP (fun m => g m == x) = 0 :=
        List.countP_eq_zero.2 (fun a ha hb => h.1 (by
          rw [beq_iff_eq] at hb; rw [hy, ← hb]; exact List.mem_map_of_mem ha))
      rw [this]; split <;> omega
    · have := countP_le_one g x h.2
      have : (g y == x) = false := by simpa using hy
      simp only [this, Bool.false_eq_true, ↓reduceIte]; omega

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem initMsgs_heads {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64) (allowed : Array Bool) (st : St) :
    ((initMsgs τ n allowed st).map List.head?).Nodup := by
  unfold initMsgs
  rw [List.map_map]
  apply nodup_map_on _ (List.nodup_range.sublist List.filter_sublist)
  intro x hx y hy he
  have hx' := idxOk_lt hn (List.mem_filter.1 hx).2
  have hy' := idxOk_lt hn (List.mem_filter.1 hy).2
  simp only [Function.comp, initRec, List.map_cons, List.head?_cons, Option.some.injEq] at he
  have := (Proc.ofNat_cv_eq (by omega) (by omega)).1 he
  omega

/-- **`InitOnce` on τ's addresses** from `InitVals`. -/
theorem initOnce_of {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64) {allowed : Array Bool} {st : St}
    (hV : InitVals AP tr pub τ n allowed st) : InitOnceQ AP tr pub (QT τ n) := by
  intro a ha
  have hr := QT_range hn ha
  calc (sopSent AP tr pub).countP (fun m => m.take 3 == [a, 0, 0])
      ≤ (sopSent AP tr pub).countP (fun m => (m.head? == some a) && isTauInit τ m) := by
        apply List.countP_mono_left
        intro m _ hm
        simp only [beq_iff_eq] at hm
        have h0 : m.head? = some a := by
          have := congrArg List.head? hm
          rw [List.head?_take] at this; simpa using this
        have h2 : m[2]? = some 0 := by
          have := congrArg (·[2]?) hm
          simpa [List.getElem?_take] using this
        simp only [isTauInit, h0, h2, Bool.and_eq_true, beq_iff_eq, Option.any_some,
          decide_eq_true_eq]
        exact ⟨trivial, trivial, hr⟩
    _ = ((sopSent AP tr pub).filter (isTauInit τ)).countP (fun m => m.head? == some a) := by
        rw [List.countP_filter]
    _ = (initMsgs τ n allowed st).countP (fun m => m.head? == some a) := hV.countP_eq _
    _ ≤ 1 := countP_le_one List.head? (some a) (initMsgs_heads hτ hn allowed st)

end

/-! ## The `INIT` rows of τ's addresses -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tm : Nat}

theorem mem_initMsgs {τ n : Nat} (hn : n ≤ 64) {allowed : Array Bool} {st : St} {m : List Fp} :
    m ∈ initMsgs τ n allowed st ↔ ∃ x, idxOk n x = true ∧ m = (initRec τ allowed st x).map Fp.ofNat := by
  simp only [initMsgs, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨idxOk_lt hn hx, hx⟩, rfl⟩


theorem mem_sopSent_of_recv (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {r : Nat} (hr : r < tr.height tm)
    (ha : cv tr tm r Mem.act = 1) : Mem.opMsg tr tm pub r ∈ sopSent AP tr pub := by
  have h1 : Mem.opMsg tr tm pub r ∈ memRecv tr tm pub :=
    List.mem_filterMap.2 ⟨r, List.mem_range.2 hr, by simp [ha]⟩
  exact (mem_recv_perm hH hM).subset h1

theorem opMsg_head (r : Nat) :
    (Mem.opMsg tr tm pub r).head? = some (Fp.ofNat (cv tr tm r Mem.addr)) := by
  rw [Mem.opMsg_eq]; simp only [List.head?_cons, Option.some.injEq]
  exact (Fp.ofNat_toNat _).symm

theorem opMsg_get1 (r : Nat) :
    (Mem.opMsg tr tm pub r)[1]? = some (Fp.ofNat (cv tr tm r Mem.t)) := by
  rw [Mem.opMsg_eq]; simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
  exact (Fp.ofNat_toNat _).symm

/-- An `INIT` row of a τ address carries an expected `INIT` message. -/
theorem init_row_msg (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {τ n : Nat} (hn : n ≤ 64)
    {allowed : Array Bool} {st : St} (hV : InitVals AP tr pub τ n allowed st)
    {f : Nat} (hf : f < tr.height tm) (hff : cv tr tm f Mem.fst = 1) (hq : QT τ n (cv tr tm f Mem.addr) = true) :
    ∃ x, idxOk n x = true ∧ Mem.opMsg tr tm pub f = (initRec τ allowed st x).map Fp.ofNat := by
  have hL := mLocal_of hH hM
  have hs := mem_sopSent_of_recv hH hM hf (Mem.init_row hL hf hff).1
  have hr := QT_range hn hq
  have hin : Mem.opMsg tr tm pub f ∈ (sopSent AP tr pub).filter (isTauInit τ) := by
    refine List.mem_filter.2 ⟨hs, ?_⟩
    simp only [isTauInit, Mem.op_init hL hf hff, opMsg_head, Bool.and_eq_true, beq_iff_eq,
      Option.any_some, decide_eq_true_eq, toNat_ofNat_lt' (cv_lt _ _)]
    exact ⟨trivial, hr⟩
  exact (mem_initMsgs hn).1 (hV.subset hin)

theorem cell_eq_ofNat {t r col : Nat} {L : List Fp} {v : Nat} (hv : v < 2013265921) :
    tr.cell t r col = Fp.ofNat v → cv tr t r col = v := fun h => cell_ofNat h hv

/-- **The values of an `INIT` row of a τ address.** -/
theorem init_row_vals (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64)
    {allowed : Array Bool} {st : St} (hB : ABnd 4500000 st) (hV : InitVals AP tr pub τ n allowed st)
    {f : Nat} (hf : f < tr.height tm) (hff : cv tr tm f Mem.fst = 1) (hq : QT τ n (cv tr tm f Mem.addr) = true) :
    cv tr tm f Mem.v = rd τ st (cv tr tm f Mem.addr) ∧
      cv tr tm f Mem.vin = (if cv tr tm f Mem.addr - τ * 16384 < 4096 then
        (if allowed[cv tr tm f Mem.addr - τ * 16384]! then 1 else 0) else 0) := by
  obtain ⟨x, hx, he⟩ := init_row_msg hH hM hn hV hf hff hq
  have hx' := idxOk_lt hn hx
  rw [Mem.opMsg_eq] at he
  simp only [initRec, List.map_cons, List.map_nil, List.cons.injEq] at he
  obtain ⟨ea, -, -, evin, ev, -⟩ := he
  have ha := cell_ofNat ea (by omega)
  rw [ha, show τ * 16384 + x - τ * 16384 = x by omega]
  refine ⟨cell_ofNat ev (by have := rd_le (τ := τ) hB (τ * 16384 + x); omega), cell_ofNat evin ?_⟩
  split <;> (try split) <;> decide

/-- **The `isL` flag of an `INIT` row of a τ address** is `[link address]`: the row's `c = isL`
(`Mem.row_init`) is position 7 of its `INIT` message, which the codec sends as 1 (links) and the
distribute as 0 (budgets). -/
theorem init_row_isL (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64)
    {allowed : Array Bool} {st : St} (hV : InitVals AP tr pub τ n allowed st)
    {f : Nat} (hf : f < tr.height tm) (hff : cv tr tm f Mem.fst = 1) (hq : QT τ n (cv tr tm f Mem.addr) = true) :
    cv tr tm f Mem.isL = if cv tr tm f Mem.addr - τ * 16384 < 4096 then 1 else 0 := by
  have hL := mLocal_of hH hM
  obtain ⟨x, hx, he⟩ := init_row_msg hH hM hn hV hf hff hq
  have hx' := idxOk_lt hn hx
  rw [Mem.opMsg_eq] at he
  simp only [initRec, List.map_cons, List.map_nil, List.cons.injEq] at he
  obtain ⟨ea, -, -, -, -, -, -, ec, -⟩ := he
  have ha := cell_ofNat ea (by omega)
  rw [ha, show τ * 16384 + x - τ * 16384 = x by omega, ← (Mem.row_init hL hf hff).2.2.2.2.1]
  exact cell_ofNat ec (by split <;> decide)

/-- **Every τ address has its `INIT` row.** -/
theorem init_exists (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64)
    {allowed : Array Bool} {st : St} (hV : InitVals AP tr pub τ n allowed st)
    {a : Nat} (hq : QT τ n a = true) :
    ∃ f, f < tr.height tm ∧ cv tr tm f Mem.fst = 1 ∧ cv tr tm f Mem.addr = a := by
  obtain ⟨h1, hx⟩ := QT_iff.1 hq
  have hx' := idxOk_lt hn hx
  have hmem : (initRec τ allowed st (a - τ * 16384)).map Fp.ofNat ∈ initMsgs τ n allowed st :=
    (mem_initMsgs hn).2 ⟨_, hx, rfl⟩
  have hs := (List.mem_filter.1 (hV.symm.subset hmem)).1
  have hc := List.count_pos_iff.2 hs
  rw [sopSent_count, ← mem_init_eq_sent hH hM _ (by simp [initRec, OP_INIT]; rfl)] at hc
  obtain ⟨f, hf, hm⟩ := List.mem_filterMap.1 (List.count_pos_iff.1 hc)
  have hf' := List.mem_range.1 hf
  by_cases hff : cv tr tm f Mem.fst = 1
  · simp only [hff, ↓reduceIte, Option.some.injEq] at hm
    refine ⟨f, hf', hff, ?_⟩
    have := congrArg List.head? hm
    rw [opMsg_head] at this
    simp only [initRec, List.map_cons, List.head?_cons, Option.some.injEq] at this
    rw [(Proc.ofNat_cv_eq (cv_lt _ _) (by omega)).1 this]; omega
  · simp [hff] at hm

/-- **The start state**: `memInit a = rd τ st a` on τ's addresses. -/
theorem memInit_tau (hH : HoldsP AP pub tr) (hM : MemOwn AP tm) {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64)
    {allowed : Array Bool} {st : St} (hB : ABnd 4500000 st) (hV : InitVals AP tr pub τ n allowed st)
    {a : Nat} (hq : QT τ n a = true) : memInit tr tm a = rd τ st a := by
  obtain ⟨f, hf, hff, rfl⟩ := init_exists hH hM hτ hn hV hq
  rw [memInit_eqQ (mem_seg_uniqueQ hH hM (initOnce_of hτ hn hV)) hf hff hq]
  exact (init_row_vals hH hM hτ hn hB hV hf hff hq).1

end

/-! ## The op rows of τ's addresses and their times -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd : Nat}

/-- **An op row of a τ address** carries a process GRANT of an entry of the instance or the
READ of a τ request block. -/
theorem op_row (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd) (PS : ParSmall AP pub)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) {n : Nat} (hn : n ≤ 64)
    {r : Nat} (hr : r < tr.height tm) (ha : cv tr tm r Mem.act = 1) (hf0 : cv tr tm r Mem.fst = 0)
    (hq : QT (cv tr tp f Proc.tau) n (cv tr tm r Mem.addr) = true) :
    (∃ i, i < m ∧ ∃ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr ∧ ∃ k, (k = 7 ∨ k = 8 ∨ k = 9) ∧
        Mem.opMsg tr tm pub r = (Proc.interactions[k]!).msgVal tr tp (Proc.hdrAt tr tp f i + 1 + j) pub) ∨
      (∃ f', f' < tr.height tsd ∧ cv tr tsd f' Scan.fQ = 1 ∧ cv tr tsd f' Scan.tau = cv tr tp f Proc.tau ∧
        Mem.opMsg tr tm pub r = (ScanDist.interactions[4]!).msgVal tr tsd (f' + 19) pub) := by
  have hL := mLocal_of hH O.mem
  have hr' := QT_range hn hq
  exact op_sent hH O OS OO PS htau hf hk hc I (mem_sopSent_of_recv hH O.mem hr ha)
    (Mem.op_row hL hr ha hf0).2 (opMsg_head r) hr'.1 hr'.2

/-- The time of an entry's GRANT is `T_i + j`. -/
theorem ent_time (hL : Proc.PLocal tr tp pub) (hHt : tr.height tp ≤ 2 ^ 22) {f m : Nat}
    (I : Proc.Inst tr tp f m) {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)
    {k : Nat} (hk : k = 7 ∨ k = 8 ∨ k = 9) :
    ((Proc.interactions[k]!).msgVal tr tp (Proc.hdrAt tr tp f i + 1 + j) pub)[1]? =
      some (Fp.ofNat (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)) ∧
    cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j < T0 + 2 ^ 22 := by
  obtain ⟨⟨hh0, hh, -⟩, hTb⟩ := I.hdr i hi
  obtain ⟨-, -, -, -, -, -, -, -, -, h7, -, h8, -, h9, -⟩ := Proc.ent_msgs hL hHt hh0 hh hj
  refine ⟨?_, by omega⟩
  rcases hk with rfl | rfl | rfl
  · rw [h7]; rfl
  · rw [h8]; rfl
  · rw [h9]; rfl

/-- **Times of the memory rows on τ's addresses are `< 2^29`.** -/
theorem mem_timeQ (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd) (PS : ParSmall AP pub)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m) {P : InstPub} (SP : ScanPub AP pub (cv tr tp f Proc.tau) P)
    (PO : ScanPubOk P) {n : Nat} (hn : n ≤ 64) :
    TimeQ tr tm (QT (cv tr tp f Proc.tau) n) := by
  have hL := mLocal_of hH O.mem
  have hLp := pLocal_of hH O.tp_lt O.tp_tab
  have hHt := proc_height hH O.tp_lt O.tp_tab
  intro r hr ha hq
  by_cases hff : cv tr tm r Mem.fst = 1
  · rw [(Mem.row_init hL hr hff).1]; decide
  have hf0 : cv tr tm r Mem.fst = 0 := by have := (Mem.row_flags hL hr).2.1; omega
  have h1 := opMsg_get1 (tr := tr) (tm := tm) (pub := pub) r
  rcases op_row hH O OS OO PS htau hf hk hc I hn hr ha hf0 hq with
    ⟨i, hi, j, hj, k, hk', hM⟩ | ⟨f', hf', hq', ht', hM⟩
  · obtain ⟨e, hb⟩ := ent_time hLp hHt I hi hj hk'
    rw [hM, e, Option.some.injEq] at h1
    have := (Proc.ofNat_cv_eq (by unfold T0 at hb; omega) (cv_lt _ _)).1 h1
    unfold T0 at hb; omega
  · have hSD := sd_local hH OS
    have hS := Scan.SLocal.of_sd hSD
    obtain ⟨-, hkS, -, hcol⟩ := Scan.shape_all hS hf' hq' 19 (by omega)
    have hcid := hcol Scan.cid (by simp [Scan.reqCols])
    have hlt := (blk_ok hH OS SP PO hf' hq' ht').lt
    have := PO.len16
    rw [hM, Scan.op_msg, hcid, hkS] at h1
    simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1
    have := (Proc.ofNat_cv_eq (by omega) (cv_lt _ _)).1 h1
    omega

end

end ZkFormal.NearV3.Sched
