import StateM5a.WsDecode
import StateM5a.Tape

/-!
# StateM5a.ChipStub — non-vacuity: `Holds` of the prover's AIR is satisfiable with the native chip

Every theorem of this package about the working set is stated over
`Holds (fullAir D extra nb np) pub tr` (`m5aAir D` tables, then `extra`), and `Holds` requires
**every** bus to balance.  The `IF384` bus (`B_IF384 = 16`) is only *received* by Lean tables
(`WSB`, `WSN`, `WSL`, `WSP` through `Ws.comp`); its sender is the native SHA-512 compression chip
(`prover/src/main.rs`: Lean bus 16 ↦ native bus 103), which is not a Lean table.  So `Holds` is
satisfiable only if `extra` contains `IF384` senders (lane A's results were vacuous for exactly
this reason).  This file shows our statements are **not** vacuous:

* `chipStub`: a Lean stand-in for the chip's interface — no constraints, width 9, one interaction
  `snd B_IF384 [col 0] [col 1, …, col 8]`, `maxLog 22` (the protocol cap `Table.wf`; the receive
  volume can exceed `2^20`: `WSL` alone has 32 receives per row on up to `2^20` rows).
* `holds_of_holdsX` (generic, any `Air`, any bus `b0`, any field): if a trace satisfies every
  part of `Holds` except balance of `b0` (`HoldsX`), no table sends on `b0`, and `L` is any list of
  8-element messages that is a permutation of the `b0` receives with `L.length ≤ 2^22`, then
  extending the trace by one stub table whose row `r < |L|` carries multiplicity 1 and message
  `L[r]` (other rows 0) gives `Holds` of the AIR with the stub appended, the original tables
  unchanged, and the stub's sends **equal** to `L`.  No receive multiplicity has to vanish.
* `m5a_ifOK`: in `m5aAir D` no table sends on `IF384` and every `IF384` receive has 8 message
  columns; `tape_ifOK`: the public tape table does not use `IF384`.
* `precheck_holds` / `precheck_holds_tape` (the deployment): for the AIR the prover runs,
  `fullAir D (tapeTable … :: rest ++ [chipStub])`, a trace accepted by the Rust precheck (Lean
  constraints, booleanity, heights, every non-`IF384` bus balanced, and the native chip's
  `IF384` sends `chip` a permutation of the receives) yields a `Holds` instance of exactly the shape
  our theorems take, and their premise
  `Sha512IfContract compress ((busList … B_IF384 true).map decIf)` becomes
  `Sha512IfContract compress (chip.map decIf)`: the native chip's faithfulness on its own sends.
* `stub_bus_premise`, `stub_sendsOn_premise`: appending the stub preserves every `extra`-side
  premise of the existing theorems (they all exclude buses `≠ IF384`, or sends on buses
  `≠ IF384`), so none of them excludes the chip.
-/

namespace StateM5a.ChipStub

open ZkFormal.Air ZkFormal.Algebra StateM5a.Bus StateM5a.DecodeBus StateM5a.DecodeM5a
open StateM5a.Sha512If StateM5a.WsDecode StateM5a.KeyDecode

/-! ## The stub table -/

/-- Message columns `1..8`. -/
def stubMsg : List Expr := (List.range 8).map fun j => Expr.col (j + 1) false

/-- The stub's one interaction: send on `bus`, multiplicity bit column 0, message columns 1..8. -/
def stubIx (bus : Nat) : Interaction := { bus, mult := [.col 0 false], msg := stubMsg, send := true }

/-- A sender-only table on `bus` (no constraints, width 9, `maxLog 22`). -/
def chipStubOn (bus : Nat) : Table :=
  { width := 9, constraints := [], interactions := [stubIx bus], maxLog := 22 }

/-- **The `IF384` chip stub.** -/
def chipStub : Table := chipStubOn B_IF384

theorem chipStub_ix : chipStub.interactions = [stubIx B_IF384] := rfl

/-! ## `Holds` without one bus -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Every part of `Holds` except the balance of bus `b0`. -/
structure HoldsX (A : Air) (pub : List F) (tr : Trace F) (b0 : Nat) : Prop where
  logBound : ∀ t (ht : t < A.tables.length), 1 ≤ tr.log t ∧ tr.log t ≤ A.tables[t].maxLog
  constr : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ A.tables[t].constraints, e.eval tr t r pub = 0
  bits : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ i ∈ A.tables[t].interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1
  balance : ∀ b m, b ≠ b0 → busCount A tr pub b true m = busCount A tr pub b false m

theorem Holds.toHoldsX {A : Air} {pub : List F} {tr : Trace F} (h : Holds A pub tr) (b0 : Nat) :
    HoldsX A pub tr b0 :=
  ⟨h.logBound, h.constr, h.bits, fun b m _ => h.balance b m⟩

/-- The stub's cells: row `r < |L|` is `1 ‖ L[r]`, other rows are `0`. -/
def stubCell (L : List (List F)) (r c : Nat) : F :=
  match L[r]? with
  | none => 0
  | some m => if c = 0 then 1 else m.getD (c - 1) 0

/-- `tr` extended by the stub at table index `n` (height `2^22`). -/
def extTrace (tr : Trace F) (n : Nat) (L : List (List F)) : Trace F where
  log t := if t = n then 22 else tr.log t
  cell t r c := if t = n then stubCell L r c else tr.cell t r c

section ext
variable (tr : Trace F) (n : Nat) (L : List (List F)) {t : Nat} (ht : t ≠ n)
include ht

omit [DecidableEq F] in
theorem height_ext : (extTrace tr n L).height t = tr.height t := by
  simp [Trace.height, extTrace, ht]

theorem rowEnv_ext (r : Nat) (pub : List F) : rowEnv (extTrace tr n L) t r pub = rowEnv tr t r pub := by
  unfold rowEnv
  simp only [height_ext tr n L ht]
  simp [extTrace, ht]

theorem eval_ext (e : Expr) (r : Nat) (pub : List F) :
    e.eval (extTrace tr n L) t r pub = e.eval tr t r pub := by
  simp only [Expr.eval, rowEnv_ext tr n L ht]

theorem multNat_ext (i : Interaction) (r : Nat) (pub : List F) :
    i.multNat (extTrace tr n L) t r pub = i.multNat tr t r pub := by
  unfold Interaction.multNat
  generalize i.mult = bs
  generalize 0 = k
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [Interaction.multNat.go, eval_ext tr n L ht, ih]

theorem rowBusList_ext (is : List Interaction) (r : Nat) (pub : List F) (b : Nat) (s : Bool) :
    rowBusList is (extTrace tr n L) t r pub b s = rowBusList is tr t r pub b s := by
  simp only [rowBusList, multNat_ext tr n L ht, Interaction.msgVal, eval_ext tr n L ht]

theorem tableBusList_ext (is : List Interaction) (pub : List F) (b : Nat) (s : Bool) :
    tableBusList is (extTrace tr n L) t pub b s = tableBusList is tr t pub b s := by
  simp only [tableBusList, height_ext tr n L ht, rowBusList_ext tr n L ht]

end ext

theorem busList_go_ext (tr : Trace F) (n : Nat) (L : List (List F)) (pub : List F) (b : Nat) (s : Bool) :
    ∀ (Ts : List Table) (t : Nat), t + Ts.length ≤ n →
      busList.go (extTrace tr n L) pub b s Ts t = busList.go tr pub b s Ts t
  | [], _, _ => rfl
  | T :: Ts, t, h => by
    simp only [List.length_cons] at h
    simp only [busList.go]
    rw [tableBusList_ext tr n L (by omega), busList_go_ext tr n L pub b s Ts (t + 1) (by omega)]

/-- The bus lists of `A` with a table `S` appended, on the extended trace. -/
theorem busList_stub (A : Air) (S : Table) (tr : Trace F) (L : List (List F)) (pub : List F) (b : Nat)
    (s : Bool) :
    busList { A with tables := A.tables ++ [S] } (extTrace tr A.tables.length L) pub b s =
      busList A tr pub b s ++ tableBusList S.interactions (extTrace tr A.tables.length L) A.tables.length pub b s := by
  simp only [busList]
  rw [busList_go_append, busList_go_ext tr _ L pub b s A.tables 0 (by omega)]
  simp [busList.go]

theorem flatMap_range_take {α : Type} (L : List α) :
    ∀ H, (List.range H).flatMap (fun r => L[r]?.toList) = L.take H
  | 0 => by simp
  | H + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_take L H, List.take_add_one]
    simp

omit [DecidableEq F] in
theorem stubMsg_val (m : List F) (hm : m.length = 8) :
    ((List.range 8).map fun j => m[j]?.getD 0) = m := by
  apply List.ext_getElem
  · simp [hm]
  · intro k h1 h2
    simp [List.getElem?_eq_getElem h2]

omit [DecidableEq F] in
theorem eval_col (tr : Trace F) (t r c : Nat) (pub : List F) :
    (Expr.col c false).eval tr t r pub = tr.cell t r c := by
  simp [Expr.eval, Expr.evalWith, rowEnv]

omit [DecidableEq F] in
theorem stubCell_bit (L : List (List F)) (r : Nat) : stubCell L r 0 = 0 ∨ stubCell L r 0 = 1 := by
  unfold stubCell; split <;> simp

/-- The stub's row `r` on its own bus sends `L[r]` once (or nothing past `|L|`). -/
theorem stub_row (tr : Trace F) (n : Nat) (L : List (List F)) (h01 : (0 : F) ≠ 1)
    (h8 : ∀ m ∈ L, m.length = 8) (b0 r : Nat) (pub : List F) :
    rowBusList [stubIx b0] (extTrace tr n L) n r pub b0 true = L[r]?.toList := by
  simp only [rowBusList, stubIx, List.flatMap_cons, List.flatMap_nil, List.append_nil, and_self,
    ↓reduceIte, multNat_one, Interaction.msgVal, stubMsg, List.map_map, Function.comp_def, eval_col]
  simp only [extTrace, ↓reduceIte]
  cases hL : L[r]? with
  | none => simp [stubCell, hL, h01]
  | some m =>
    have hm : m.length = 8 := h8 m (List.mem_of_getElem? hL)
    simp only [stubCell, hL, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    simp only [List.getD_eq_getElem?_getD]
    simp [stubMsg_val m hm]

theorem stub_list (tr : Trace F) (n : Nat) (L : List (List F)) (h01 : (0 : F) ≠ 1)
    (h8 : ∀ m ∈ L, m.length = 8) (hlen : L.length ≤ 2 ^ 22) (b0 : Nat) (pub : List F) :
    tableBusList [stubIx b0] (extTrace tr n L) n pub b0 true = L := by
  simp only [tableBusList, stub_row tr n L h01 h8 b0 _ pub]
  rw [show (extTrace tr n L).height n = 2 ^ 22 by simp [Trace.height, extTrace],
    flatMap_range_take, List.take_of_length_le hlen]

theorem stub_nil (tr : Trace F) (n : Nat) (L : List (List F)) (b0 b : Nat) (s : Bool) (pub : List F)
    (h : ¬ (b = b0 ∧ s = true)) : tableBusList [stubIx b0] (extTrace tr n L) n pub b s = [] :=
  tableBusList_nil _ _ _ _ _ _ (fun i hi => by
    simp only [List.mem_singleton] at hi; subst hi
    simp only [stubIx]; exact fun ⟨e1, e2⟩ => h ⟨e1.symm, e2.symm⟩)

/-- **Non-vacuity, generic.**  A trace satisfying everything but the balance of bus `b0`, on an
AIR where no table sends on `b0`, extends — by one `chipStubOn b0` table carrying any permutation
`L` of the `b0` receives (8-element messages, `|L| ≤ 2^22`) — to a trace satisfying `Holds` of the
AIR with the stub appended; the original tables are untouched and the stub's sends are `L`. -/
theorem holds_of_holdsX {A : Air} {pub : List F} {tr : Trace F} {b0 : Nat} (h01 : (0 : F) ≠ 1)
    (hX : HoldsX A pub tr b0)
    (hns : ∀ T ∈ A.tables, ∀ i ∈ T.interactions, ¬ (i.bus = b0 ∧ i.send = true))
    (L : List (List F)) (hperm : L.Perm (busList A tr pub b0 false))
    (h8 : ∀ m ∈ L, m.length = 8) (hlen : L.length ≤ 2 ^ 22) :
    ∃ tr' : Trace F,
      (∀ t < A.tables.length, tr'.log t = tr.log t ∧ tr'.cell t = tr.cell t) ∧
      Holds { A with tables := A.tables ++ [chipStubOn b0] } pub tr' ∧
      busList { A with tables := A.tables ++ [chipStubOn b0] } tr' pub b0 true = L ∧
      busList { A with tables := A.tables ++ [chipStubOn b0] } tr' pub b0 false = busList A tr pub b0 false := by
  let n := A.tables.length
  have hS : (chipStubOn b0).interactions = [stubIx b0] := rfl
  have hsend : busList A tr pub b0 true = [] := busList_go_nil tr pub b0 true A.tables 0 hns
  have eT : busList { A with tables := A.tables ++ [chipStubOn b0] } (extTrace tr n L) pub b0 true = L := by
    rw [busList_stub, hsend, hS, stub_list tr n L h01 h8 hlen]; rfl
  have eF : busList { A with tables := A.tables ++ [chipStubOn b0] } (extTrace tr n L) pub b0 false =
      busList A tr pub b0 false := by
    rw [busList_stub, hS, stub_nil tr n L b0 b0 false pub (by simp), List.append_nil]
  refine ⟨extTrace tr n L, fun t ht => ?_, ?_, eT, eF⟩
  · have : t ≠ n := by omega
    exact ⟨by simp [extTrace, this], by funext r c; simp [extTrace, this]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [List.length_append, List.length_singleton] at ht
    by_cases h : t < n
    · have hne : t ≠ n := by omega
      simp only [List.getElem_append_left h, extTrace, hne, ↓reduceIte]
      exact hX.logBound t h
    · have e : t = n := by omega
      subst e
      simp [extTrace, chipStubOn, n]
  · intro t ht r hr e he
    simp only [List.length_append, List.length_singleton] at ht
    by_cases h : t < n
    · have hne : t ≠ n := by omega
      rw [List.getElem_append_left h] at he
      rw [eval_ext tr n L hne]
      exact hX.constr t h r (by rwa [height_ext tr n L hne] at hr) e he
    · have e' : t = n := by omega
      subst e'
      simp [chipStubOn, n] at he
  · intro t ht r hr i hi b hb
    simp only [List.length_append, List.length_singleton] at ht
    by_cases h : t < n
    · have hne : t ≠ n := by omega
      rw [List.getElem_append_left h] at hi
      rw [eval_ext tr n L hne]
      exact hX.bits t h r (by rwa [height_ext tr n L hne] at hr) i hi b hb
    · have e' : t = n := by omega
      subst e'
      simp [n, chipStubOn] at hi
      subst hi
      simp only [stubIx, List.mem_singleton] at hb
      subst hb
      simp only [eval_col, extTrace, ↓reduceIte]
      exact stubCell_bit L r
  · intro b m
    rw [← count_busList, ← count_busList]
    by_cases hb : b = b0
    · subst hb
      rw [eT, eF]
      exact hperm.count_eq m
    · rw [busList_stub, busList_stub, hS, stub_nil tr n L b0 b true pub (by simp [hb]),
        stub_nil tr n L b0 b false pub (by simp), List.append_nil, List.append_nil, count_busList,
        count_busList]
      exact hX.balance b m hb

theorem busList_go_len (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) :
    ∀ (Ts : List Table) (t : Nat),
      (∀ T ∈ Ts, ∀ i ∈ T.interactions, i.bus = b → i.send = s → i.msg.length = 8) →
      ∀ m ∈ busList.go tr pub b s Ts t, m.length = 8
  | [], _, _ => by simp [busList.go]
  | T :: Ts, t, h => by
    intro m hm
    simp only [busList.go, List.mem_append] at hm
    rcases hm with hm | hm
    · simp only [tableBusList, rowBusList, List.mem_flatMap] at hm
      obtain ⟨r, -, i, hi, hm⟩ := hm
      split at hm
      · rename_i hbs
        rw [List.eq_of_mem_replicate hm, Interaction.msgVal, List.length_map]
        exact h T (List.mem_cons_self ..) i hi hbs.1 hbs.2
      · simp at hm
    · exact busList_go_len tr pub b s Ts (t + 1) (fun T' hT' => h T' (List.mem_cons_of_mem _ hT')) m hm

/-- Every message on `(b, s)` has length `8` when every interaction on `(b, s)` has 8 message
expressions. -/
theorem busList_len (A : Air) (tr : Trace F) (pub : List F) (b : Nat) (s : Bool)
    (h : ∀ T ∈ A.tables, ∀ i ∈ T.interactions, i.bus = b → i.send = s → i.msg.length = 8) :
    ∀ m ∈ busList A tr pub b s, m.length = 8 :=
  busList_go_len tr pub b s A.tables 0 h

end

/-! ## The M5a AIR: `IF384` is receive-only, 8-element messages -/

/-- No send on `IF384`, and every `IF384` receive has 8 message expressions. -/
def ifOK (is : List Interaction) : Bool :=
  is.all fun i => !(i.bus == B_IF384) || (!i.send && i.msg.length == 8)

theorem of_ifOK {is : List Interaction} (h : ifOK is = true) {i : Interaction} (hi : i ∈ is)
    (hb : i.bus = B_IF384) : i.send = false ∧ i.msg.length = 8 := by
  have := List.all_eq_true.1 h i hi
  simp only [hb, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq] at this
  exact this

set_option maxRecDepth 100000 in
theorem m5a_ifOK (D : Nat) : ∀ T ∈ (m5aAir D).tables, ifOK T.interactions = true := by
  intro T hT
  simp only [m5aAir, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show ifOK shaTable.interactions = true; decide
  · show ifOK Key.interactions = true; decide
  · show ifOK Br.interactions = true; decide
  · show ifOK Sn.interactions = true; decide
  · show ifOK Kcmp.interactions = true; decide
  · show ifOK Wsb.interactions = true; decide
  · show ifOK Wsn.interactions = true; decide
  · show ifOK Wsa.interactions = true; decide
  · show ifOK Snc.interactions = true; decide
  · show ifOK Rng.interactions = true; decide
  · show ifOK Wsl.interactions = true; decide
  · show ifOK Wsp.interactions = true; decide

/-- The public tape (`Tape.tapeTable (m5aTape …)`) uses only `WRITE` and `TCH`. -/
theorem tape_ifOK (writes : List (List Nat)) (prev post : NearSpec.Bytes) (n : Nat) :
    ifOK (Tape.tapeTable (Tape.m5aTape writes prev post n)).interactions = true := by
  simp only [ifOK, List.all_eq_true]
  intro i hi
  simp only [Tape.tapeTable, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  have : e.1 ≠ B_IF384 := by
    simp only [Tape.m5aTape, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with ⟨w, -, rfl⟩ | rfl | rfl <;> simp [B_WRITE, B_TCH, B_IF384]
  simp [this]

/-! ## The deployment: `fullAir D (extra ++ [chipStub])` -/

theorem fullAir_stub (D : Nat) (extra : List Table) (nb np : Nat) :
    fullAir D (extra ++ [chipStub]) nb np =
      { fullAir D extra nb np with tables := (fullAir D extra nb np).tables ++ [chipStubOn B_IF384] } := by
  simp [fullAir, chipStub]

theorem zero_ne_one_fp : (0 : Fp) ≠ 1 := by decide +kernel

/-- **Non-vacuity of the package's statements (the deployment).**  `extra` is the prover's extra
tables before the chip (the public tape and anything else) — none sends on `IF384` and their
`IF384` receives (if any) have 8 columns.  A trace accepted by the Rust precheck — heights,
constraints, booleanity of the Lean/extra tables, every bus other than `IF384` balanced — together
with the native chip's `IF384` sends `chip`, a permutation of the receives (the precheck's
`chip_if` comparison), yields a trace `tr'`, equal to `tr` on every table of
`fullAir D extra nb np`, with `Holds (fullAir D (extra ++ [chipStub]) nb np) pub tr'` — the
hypothesis shape of every working-set theorem — and the chip-contract premise of those theorems is
the contract on `chip` itself (the native chip's faithfulness argument). -/
theorem precheck_holds {D nb np : Nat} {extra : List Table} {pub : List Fp} {tr : Trace Fp}
    (hX : HoldsX (fullAir D extra nb np) pub tr B_IF384)
    (hxs : ∀ T ∈ extra, ifOK T.interactions = true)
    (chip : List (List Fp)) (hchip : chip.Perm (busList (fullAir D extra nb np) tr pub B_IF384 false))
    (hlen : chip.length ≤ 2 ^ 22) :
    ∃ tr' : Trace Fp,
      (∀ t < (fullAir D extra nb np).tables.length, tr'.log t = tr.log t ∧ tr'.cell t = tr.cell t) ∧
      Holds (fullAir D (extra ++ [chipStub]) nb np) pub tr' ∧
      busList (fullAir D (extra ++ [chipStub]) nb np) tr' pub B_IF384 true = chip ∧
      busList (fullAir D (extra ++ [chipStub]) nb np) tr' pub B_IF384 false =
        busList (fullAir D extra nb np) tr pub B_IF384 false ∧
      ∀ compress : List Nat → List Nat → List Nat,
        Sha512IfContract compress
            ((busList (fullAir D (extra ++ [chipStub]) nb np) tr' pub B_IF384 true).map decIf) ↔
          Sha512IfContract compress (chip.map decIf) := by
  have hok : ∀ T ∈ (fullAir D extra nb np).tables, ifOK T.interactions = true := by
    intro T hT
    simp only [fullAir, List.mem_append] at hT
    rcases hT with hT | hT
    · exact m5a_ifOK D T hT
    · exact hxs T hT
  have hns : ∀ T ∈ (fullAir D extra nb np).tables, ∀ i ∈ T.interactions,
      ¬ (i.bus = B_IF384 ∧ i.send = true) := fun T hT i hi ⟨hb, hs⟩ => by
    have := (of_ifOK (hok T hT) hi hb).1; rw [hs] at this; exact absurd this (by decide)
  have h8 : ∀ m ∈ chip, m.length = 8 := fun m hm =>
    busList_len _ tr pub B_IF384 false
      (fun T hT i hi hb _ => (of_ifOK (hok T hT) hi hb).2) m (hchip.subset hm)
  obtain ⟨tr', hag, hH, eT, eF⟩ := holds_of_holdsX zero_ne_one_fp hX hns chip hchip h8 hlen
  rw [fullAir_stub]
  exact ⟨tr', hag, hH, eT, eF, fun compress => by rw [eT]⟩

/-- The same with the public tape first: the prover's AIR is
`fullAir D (tapeTable (m5aTape writes prev post n) :: rest ++ [chipStub])`. -/
theorem precheck_holds_tape {D nb np : Nat} {writes : List (List Nat)} {prev post : NearSpec.Bytes}
    {n : Nat} {rest : List Table} {pub : List Fp} {tr : Trace Fp}
    (hX : HoldsX (fullAir D (Tape.tapeTable (Tape.m5aTape writes prev post n) :: rest) nb np) pub tr B_IF384)
    (hrs : ∀ T ∈ rest, ifOK T.interactions = true)
    (chip : List (List Fp))
    (hchip : chip.Perm (busList (fullAir D (Tape.tapeTable (Tape.m5aTape writes prev post n) :: rest) nb np)
      tr pub B_IF384 false))
    (hlen : chip.length ≤ 2 ^ 22) :
    ∃ tr' : Trace Fp,
      (∀ t < (fullAir D (Tape.tapeTable (Tape.m5aTape writes prev post n) :: rest) nb np).tables.length,
        tr'.log t = tr.log t ∧ tr'.cell t = tr.cell t) ∧
      Holds (fullAir D (Tape.tapeTable (Tape.m5aTape writes prev post n) :: (rest ++ [chipStub])) nb np) pub tr' ∧
      busList (fullAir D (Tape.tapeTable (Tape.m5aTape writes prev post n) :: (rest ++ [chipStub])) nb np)
        tr' pub B_IF384 true = chip := by
  have hxs : ∀ T ∈ Tape.tapeTable (Tape.m5aTape writes prev post n) :: rest, ifOK T.interactions = true := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact tape_ifOK writes prev post n
    · exact hrs T hT
  obtain ⟨tr', hag, hH, eT, -⟩ := precheck_holds hX hxs chip hchip hlen
  exact ⟨tr', hag, hH, eT⟩

/-! ## The stub passes every `extra`-side premise of the package -/

/-- Premises of the form `∀ T ∈ extra, ∀ i ∈ T.interactions, P i.bus` (e.g. `i.bus ≠ B_WM ∧ … ∧
i.bus ≠ B_TREE`, `i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH`, `i.bus ≠ B_RNG`) survive appending
the stub whenever `P B_IF384`. -/
theorem stub_bus_premise {P : Nat → Prop} (hP : P B_IF384) {extra : List Table}
    (h : ∀ T ∈ extra, ∀ i ∈ T.interactions, P i.bus) :
    ∀ T ∈ extra ++ [chipStub], ∀ i ∈ T.interactions, P i.bus := by
  intro T hT i hi
  rcases List.mem_append.1 hT with hT | hT
  · exact h T hT i hi
  · simp only [List.mem_singleton] at hT; subst hT
    simp only [chipStub_ix, List.mem_singleton] at hi; subst hi
    exact hP

/-- Premises `∀ T ∈ extra, sendsOn T.interactions b = false` survive appending the stub for every
`b ≠ B_IF384` (`B_NIB`, `B_KLEN`, `B_ORD`, `B_SHA_BYTES`, `B_SHA_DIGEST`, `B_KC`, `B_KCR`, `B_KDIG`,
`B_VER`). -/
theorem stub_sendsOn_premise {b : Nat} (hb : b ≠ B_IF384) {extra : List Table}
    (h : ∀ T ∈ extra, sendsOn T.interactions b = false) :
    ∀ T ∈ extra ++ [chipStub], sendsOn T.interactions b = false := by
  intro T hT
  rcases List.mem_append.1 hT with hT | hT
  · exact h T hT
  · simp only [List.mem_singleton] at hT; subst hT
    simp [sendsOn, chipStub_ix, stubIx, Ne.symm hb]

/-- E.g. `FinalOrder.Prem.hx` / `WsEntries.ws_entries` `hx`. -/
example {extra : List Table}
    (h : ∀ T ∈ extra, ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE) :
    ∀ T ∈ extra ++ [chipStub], ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE :=
  stub_bus_premise (P := fun b => b ≠ B_WM ∧ b ≠ B_PT ∧ b ≠ B_RCH ∧ b ≠ B_RNG ∧ b ≠ B_TREE)
    (by decide) h

end StateM5a.ChipStub
