import NearSpecV3.ChunkValidationD1
import NearSpecV3.ChunkValidationD1Out
import NearSpecV3.D0SubD1.Work.Root.Basic

/-!
# `NearSpecV3.D0SubD1.Work.Root.Rel` — the vocabulary of the D0 ⊆ D1 lockstep

The two checkers `checkD0` (`Except String Unit`) and `checkD1CoreObs`
(`Except String Observable`) are the same do-block up to a handful of statements.  Each of them
is cut into five phases (`NearSpecV3.D0SubD1.Work.Root.Phases`), and the five phase lemmas
(`NearSpecV3.D0SubD1.Work.Root.PhaseA … PhaseE`) are simulation statements in the vocabulary defined
here:

* `SIM x y` — *`y` succeeds whenever `x` does*: the value of `x` is irrelevant (it is always
  `()`), and the value of `y` (an `Observable`) is not determined by the statement.  Every
  phase has type `Except String Unit` on the D0 side and `Except String Observable` on the D1
  side, so `SIM` is the shape of a phase lemma's conclusion.
* `EQ x y` — the same success value (same type).  This is the shape of the *statement* level:
  inside a phase, a D0 statement and the matching D1 statement are the *same term*
  (`NearSpecV3.check b m`, the same `for` loop, the same `mapM`), so the natural fact about them
  is `EQ`.
* `WRel w w'` — the D0 witness `w` and the D1 witness `w'` of a D0-accepted stream: every
  shared field equal and the two transaction lists empty.  This is the conclusion of
  `NearSpecV3.D0SubD1.Work.Decode.Agree`.
* `ORel out out'` — the D0 runtime output and the D1 runtime output on the empty transaction
  list: same trie, same outgoing receipts, same gas/tokens, no local ids, and the outcomes
  decorated with status `.value`.  This is the conclusion of
  `NearSpecV3.D0SubD1.Work.Runtime.EmptyTxs`, and `NearSpecV3.D0SubD1.Work.Root.Outcome` turns the decoration
  into the equality of the outcome roots needed at the header comparison.

## Kit

* `sim_bind` peels one `bind` on the D0 side and hands the matching value of the D1 side to the
  continuation hypothesis: the workhorse of every phase proof;
* `sim_check`, `sim_pure`, `sim_mapError`, `sim_forIn` cover the statements that appear
  verbatim in both checkers.
-/

namespace NearSpecV3.D0SubD1.Work.Root

open NearSpec NearSpecV3

/-! ## The two relations on `Except String` computations -/

/-- **`y` succeeds whenever `x` does** (the values are not related; on the D1 side the value is
an `Observable` nobody looks at inside a phase). -/
def SIM {α β : Type} (x : Except String α) (y : Except String β) : Prop :=
  ∀ a, x = .ok a → ∃ b, y = .ok b

/-- **Same success value.** -/
def EQ {α : Type} (x y : Except String α) : Prop := ∀ a, x = .ok a → y = .ok a

theorem sim_of_eq {α : Type} {x y : Except String α} (h : x = y) : SIM x y := by
  intro a ha; exact ⟨a, h ▸ ha⟩

theorem eq_refl' {α : Type} (x : Except String α) : EQ x x := by intro a h; exact h

/-- Transport a `SIM` along equalities of both sides. -/
theorem sim_congr {α β : Type} {x x' : Except String α} {y y' : Except String β} (hx : x' = x)
    (hy : y = y') (h : SIM x y) : SIM x' y' := by
  intro a ha
  obtain ⟨b, hb⟩ := h a (hx ▸ ha)
  exact ⟨b, hy ▸ hb⟩

/-- **Peel one `bind` whose two scrutinee terms are the *same* term** (the answer types may
differ).  This is the workhorse for the long run of statements that the two checkers share. -/
theorem sim_bind_same {α γ δ : Type} {x : Except String α} {f : α → Except String γ}
    {g : α → Except String δ} (hf : ∀ a, SIM (f a) (g a)) : SIM (x >>= f) (x >>= g) := by
  intro c h
  obtain ⟨a, ha, hc⟩ := bind_ok_exists h
  obtain ⟨d, hd⟩ := hf a c hc
  exact ⟨d, by rw [ha]; simp only [bind_ok]; exact hd⟩

/-- **Peel one `bind` whose two scrutinee terms differ.**  The D0 side succeeding locates the D1
side's value through `hx`, and the continuations are then related by `hf`. -/
theorem sim_bind {α β γ δ : Type} {x : Except String α} {y : Except String β}
    {f : α → Except String γ} {g : β → Except String δ} (hx : SIM x y)
    (hf : ∀ a b, x = .ok a → y = .ok b → SIM (f a) (g b)) : SIM (x >>= f) (y >>= g) := by
  intro c h
  obtain ⟨a, ha, hc⟩ := bind_ok_exists h
  obtain ⟨b, hb⟩ := hx a ha
  obtain ⟨d, hd⟩ := hf a b ha hb c hc
  exact ⟨d, by rw [hb]; simp only [bind_ok]; exact hd⟩

/-- A `check` is the same term on both sides. -/
theorem sim_check (b : Bool) (m : String) : SIM (check b m) (check b m) := sim_of_eq rfl

/-- `pure` is the same term on both sides. -/
theorem sim_pure {α : Type} (a : α) : SIM (pure a : Except String α) (pure a : Except String α) :=
  sim_of_eq rfl

/-- The monadic `if` with the same condition on both sides. -/
theorem sim_ite_same {c : Prop} [Decidable c] {α β : Type} {x x' : Except String α}
    {y y' : Except String β} (h : SIM x y) (h' : SIM x' y') :
    SIM (if c then x else x') (if c then y else y') := by
  by_cases hc : c <;> simp only [hc, ite_true, ite_false] <;> assumption

/-- `mapError` never changes the success value, so it may differ in the message. -/
theorem sim_mapError {α : Type} (x : Except String α) (f g : String → String) :
    SIM (x.mapError f) (x.mapError g) := by
  intro a h
  cases x with
  | error e => simp [Except.mapError] at h
  | ok b => exact ⟨b, rfl⟩

/-- A `throw` on the D0 side is impossible: the hypothesis is `.ok`. -/
theorem sim_throw {α β : Type} (e : String) (y : Except String β) :
    SIM (throw e : Except String α) y := by intro a h; simp [throw] at h

/-! ## The statement-level primitives of a phase proof -/

/-- **A D0-only statement that succeeds, followed by nothing on the D1 side**: the D0
computation is `check b m` then `f`, the D1 side is just `y`, and `f` ignores its value. -/
theorem sim_bind_skip {γ δ : Type} (b : Bool) (m : String) (f : Unit → Except String γ)
    (y : Except String δ) (h : SIM (f ()) y) : SIM (check b m >>= f) y := by
  intro a ha
  obtain ⟨u, -, hf⟩ := bind_ok_exists ha
  cases u
  exact h a hf

/-- **A D1-only statement that holds**: `b = true`, so the extra `check` on the D1 side is the
identity. -/
theorem sim_extra {α δ : Type} {x : Except String α} (b : Bool) (m : String)
    (g : Unit → Except String δ) (hb : b = true) (h : SIM x (g ())) :
    SIM x (check b m >>= g) := by
  subst hb
  exact h

/-- **A D0-only statement**: `check b m >>= f` succeeds iff `b = true` and `f ()` does; the D1
side has no statement here at all.  The caller supplies the extra hypothesis `b = true` derived
from *inside* the D0 run (`b` is typically `c.txValid.isEmpty`). -/
theorem sim_bind_skip' {γ δ : Type} (b : Bool) (m : String) (f : Unit → Except String γ)
    (y : Except String δ) (h : b = true → SIM (f ()) y) : SIM (check b m >>= f) y := by
  intro a ha
  obtain ⟨u, hu, hf⟩ := bind_ok_exists ha
  cases u
  exact h (check_eq_true hu) a hf

/-- **A statement present on both sides with different booleans, both true.**  This is how an
extra `check` on one side and a differently-worded `check` on the other side are peeled
together: once both booleans are `true` the two runs are the same `f ()`/`g ()`. -/
theorem sim_check_both {γ δ : Type} {b b' : Bool} (m m' : String)
    (f : Unit → Except String γ) (g : Unit → Except String δ) (hb : b = true) (hb' : b' = true)
    (h : SIM (f ()) (g ())) : SIM (check b m >>= f) (check b' m' >>= g) := by
  subst hb; subst hb'; exact h

/-- **`==` reflects equality** on `Bytes` and on `Nat` (both are `LawfulBEq` via `DecidableEq`),
stated at the two types the lockstep needs. -/
theorem beq_nat {a b : Nat} (h : a = b) : (a == b) = true := by subst h; simp

theorem eq_of_beq_nat {a b : Nat} (h : (a == b) = true) : a = b := by simpa using h

theorem beq_bytes {a b : Bytes} (h : a = b) : (a == b) = true := by subst h; simp

theorem eq_of_beq_bytes {a b : Bytes} (h : (a == b) = true) : a = b := by simpa using h

theorem beq_bytes_symm {a b : Bytes} (h : (a == b) = true) : (b == a) = true :=
  beq_bytes (eq_of_beq_bytes h).symm

/-- **A `check` whose boolean is a `Nat` comparison with itself** (`a == a`), the shape of
`c.txValid.length == w.txs.length` and `stop + 1 == blks.length` when both sides are known equal. -/
theorem sim_check_beq_refl {γ δ : Type} (a : Nat) (m m' : String)
    (f : Unit → Except String γ) (g : Unit → Except String δ) (h : SIM (f ()) (g ())) :
    SIM (check (a == a) m >>= f) (check (a == a) m' >>= g) :=
  sim_check_both m m' f g (beq_nat rfl) (beq_nat rfl) h

/-- **The paired peel**: the two sides have a `check` at the *same position* but with different
booleans/messages, the D1 boolean being implied by the D0 one.  This is how the D0-only check
`check (c.txValid.isEmpty) …` is paired with the D1-only check
`check (c.txValid.length == w.txs.length) …`, and how
`check (slotB2.txRoot == zeroHash32)` is paired with
`check (merklizeBorsh (w.txs.map Tx.raw) == slotB2.txRoot)`: the boolean of the D0 side is
learned from its own success (`hb`), and the continuation then receives both truths. -/
theorem sim_bind_check2 {γ δ : Type} {b1 b2 : Bool} {m1 m2 : String}
    {f : Unit → Except String γ} {g : Unit → Except String δ}
    (hb : b1 = true → b2 = true) (hk : b1 = true → SIM (f ()) (g ())) :
    SIM (check b1 m1 >>= f) (check b2 m2 >>= g) := by
  intro a ha
  obtain ⟨u, hcu, hf⟩ := bind_ok_exists ha
  cases u
  have h1 : b1 = true := check_eq_true hcu
  have h2 : b2 = true := hb h1
  obtain ⟨d, hd⟩ := hk h1 a hf
  exact ⟨d, by simp only [check_of_true m2 h2, bind_ok]; exact hd⟩

/-- **A `match` with `pure`/`throw` arms on both sides** (at different answer types): the value
is the payload of the `some` arm, and the `none` arm never succeeds. -/
theorem sim_match_pure_throw {β ρ ρ' : Type} {X : Option β} (e : String) :
    SIM (match X with
          | some i => (pure i : Except String β)
          | none => (throw e : Except String β))
        (match X with
          | some i => (pure i : Except String β)
          | none => (throw e : Except String β)) :=
  sim_of_eq rfl

/-- Let `pure`/`throw` continue into different continuations. -/
theorem sim_match_pure_throw_bind {β ρ ρ' : Type} {X : Option β} {e : String}
    {K : β → Except String ρ} {K' : β → Except String ρ'} (hK : ∀ b, SIM (K b) (K' b)) :
    SIM (match X with
          | some i => (pure i : Except String β) >>= K
          | none => (throw e : Except String β) >>= K)
        (match X with
          | some i => (pure i : Except String β) >>= K'
          | none => (throw e : Except String β) >>= K') := by
  cases X with
  | none =>
      show SIM ((throw e : Except String β) >>= K) ((throw e : Except String β) >>= K')
      exact sim_throw e _
  | some b => exact hK b

/-- A trailing `pure` on the D1 side is always fine. -/
theorem sim_pure_right {α δ : Type} {x : Except String α} (v : δ) : SIM x (pure v) := by
  intro a ha; exact ⟨v, rfl⟩

/-- **The general `match` peel** (the shape of every `let x ← match Y? with …` statement): the
scrutinee is the *same* `Option` on both sides, the `some`-arm continuations are related pointwise
and the `none` arms are related.  This is the generalisation of `sim_match_pure_throw` needed when
the payload is used at a non-`Nat` type or when the arms continue into a do-block. -/
theorem sim_match_same {β γ δ : Type} (X : Option β) {f : β → Except String γ}
    {g : β → Except String δ} {n : Except String γ} {n' : Except String δ}
    (h : ∀ b, SIM (f b) (g b)) (hn : SIM n n') :
    SIM (match X with | some b => f b | none => n)
        (match X with | some b => g b | none => n') := by
  cases X with
  | none => exact hn
  | some b => exact h b

/-- **A `match` on the same scrutinee whose two do-block arms are `pure x`/`throw e` followed by
different continuations** (the shape of `let idx ← match L.index H.shardId with …` when the rest of
the slice follows): the `some` arm is a `sim_bind_same`, the `none` arm is a `throw`. -/
theorem sim_match_same_bind {β γ δ : Type} (X : Option β)
    {K : β → Except String γ} {K' : β → Except String δ} {n : Except String γ}
    {n' : Except String δ} (hK : ∀ b, SIM (K b) (K' b)) (hn : SIM n n') :
    SIM (match X with | some b => (pure b : Except String β) >>= K | none => n)
        (match X with | some b => (pure b : Except String β) >>= K' | none => n') :=
  sim_match_same X (fun b => sim_bind_same hK) hn

/-! ## The `EQ` kit: the two sides are *the same term* (so the loops match without an induction)

A `for … in …` loop whose state type and body are the same on both sides is **one term**, and the
state it produces is the same on both sides (`EQ`).  This is the case of the receipt loop of phase C
and of the implicit-transition loop of phase E: `simp only [List.forIn_cons]` + `eq_bind` +
`eq_forIn_congr` walks them once, at the state type, and the answer type of the surrounding do-block
never enters. -/

/-- `EQ` version of `sim_bind`: the two scrutinees have the same success value. -/
theorem eq_bind {α β : Type} {x y : Except String α} {f g : α → Except String β}
    (hx : EQ x y) (hf : ∀ a, EQ (f a) (g a)) : EQ (x >>= f) (y >>= g) := by
  intro c h
  obtain ⟨a, ha, hc⟩ := bind_ok_exists h
  have hb : y = .ok a := hx a ha
  rw [hb]; simp only [bind_ok]; exact hf a c hc

/-- **The `for`-loop lockstep at a shared state type** (two runs of the *same* loop term). -/
theorem eq_forIn_congr {α σ : Type} (l : List α)
    {f g : α → σ → Except String (ForInStep σ)} (h : ∀ a s, EQ (f a s) (g a s)) :
    ∀ s, EQ (forIn l s f) (forIn l s g) := by
  induction l with
  | nil => intro s; exact eq_refl' _
  | cons a t ih =>
    intro s
    simp only [List.forIn_cons]
    refine eq_bind (h a s) ?_
    intro r
    cases r with
    | done b => exact eq_refl' _
    | yield b => exact ih b

/-- **The `SIM` version of the loop lockstep**: for a loop whose state type is shared and whose body
is *the same term* on both sides, the loop itself is one term, so `SIM` is `sim_of_eq rfl` *at the
loop's own answer type* — no induction needed.  (A `SIM` induction on two *different* bodies would be
false: the D0 body may `done` where the D1 body `yield`s.) -/
theorem sim_forIn_self {α σ : Type} (l : List α) (s : σ)
    (f : α → σ → Except String (ForInStep σ)) : SIM (forIn l s f) (forIn l s f) :=
  sim_of_eq rfl

/-- **The `throw`-arm of a `match`-headed statement**: the D0 side is `.error e` and both sides
continue into a `bind` whose continuations may differ.  This is the `none` arm of every
`let x ← match Y? with …` statement. -/
theorem sim_throw_bind {α β γ : Type} (e : String) (f : α → Except String β)
    (g : α → Except String γ) :
    SIM ((throw e : Except String α) >>= f) ((throw e : Except String α) >>= g) := by
  intro a h
  obtain ⟨u, hu, -⟩ := bind_ok_exists h
  cases hu

/-- **The `have`-headed `match` peel** — the exact shape a `let x ← match Y with | some b => pure b
| none => throw e` statement takes *inside a do-block with a following continuation*:

  `have jp := K; match Y with | some b => pure b >>= jp | none => throw e >>= jp`

The `some` arm is `sim_bind_same`; the `none` arm is `sim_throw_bind`.  Proven by `cases Y` — the
same `cases` (with a **named** scrutinee, `cases h : Y`) `dsimp only`s the goal in each branch and
leaves `SIM (pure b >>= K) (pure b >>= K')`. -/
theorem sim_have_match {β γ δ : Type} (Y : Option β)
    {K : β → Except String γ} {K' : β → Except String δ} (hK : ∀ b, SIM (K b) (K' b))
    (e : String) :
    SIM (have jp := K
         match Y with
         | some b => (pure b : Except String β) >>= jp
         | none => (throw e : Except String β) >>= (jp : β → Except String γ))
        (have jp := K'
         match Y with
         | some b => (pure b : Except String β) >>= jp
         | none => (throw e : Except String β) >>= (jp : β → Except String δ)) := by
  cases hY : Y with
  | none => dsimp only; exact sim_throw_bind e _ _
  | some b => dsimp only; exact sim_bind_same hK

/-! ## Empty-list base facts (the D1-only statements) -/

theorem merklizeBorsh_nil : merklizeBorsh ([] : List Bytes) = zeroHash32 := rfl

theorem merklizeBorsh_nil_tx : merklizeBorsh (([] : List Tx).map Tx.raw) = zeroHash32 := rfl

theorem concatAll_nil : concatAll ([] : List Bytes) = [] := rfl

theorem u32_nil_length : u32 ([] : List Tx).length = u32 0 := rfl

theorem txValid_map_nil : ([] : Bytes).map (· != 0) = [] := rfl

theorem zip_nil_tx (xs : List Tx) : xs.zip ([] : List Bool) = [] := by cases xs <;> rfl

theorem all_sizeOk_nil : ([] : List Tx).all Tx.sizeOk = true := rfl

theorem txKeys_nil : txKeys ([] : List Tx) = [] := rfl

theorem mainKeys_append_nil (receipts : List Receipt) (bshards : List Nat) :
    mainKeys receipts bshards ++ ([] : List (List Nat)) = mainKeys receipts bshards :=
  List.append_nil _

/-! ## The witness relation -/

/-- The D1 witness of a D0-accepted witness file: every shared field equal, both transaction
lists empty. -/
def WRel (w : StateWitness) (w' : StateWitnessD1) : Prop :=
  w'.epochId = w.epochId ∧ w'.innerBytes = w.innerBytes ∧ w'.inner = w.inner ∧
  w'.main = w.main ∧ w'.entries = w.entries ∧ w'.appliedReceiptsHash = w.appliedReceiptsHash ∧
  w'.implicit = w.implicit ∧ w'.txs = [] ∧ w'.newTxs = []

/-- The D0 runtime output and the D1 runtime output of the empty transaction list. -/
def ORel (out : MainOut) (out' : MainOutD1) : Prop :=
  out'.trie = out.trie ∧
  out'.outcomes = out.outcomes.map (fun o => { o := o, status := OStatus.value }) ∧
  out'.outgoing = out.outgoing ∧ out'.gasUsed = out.gasUsed ∧
  out'.tokensBurnt = out.tokensBurnt ∧ out'.localIds = []
theorem length_eq_zero_of_isEmpty' {α : Type} {l : List α} (h : l.isEmpty = true) :
    l.length = 0 := by
  rw [eq_nil_of_isEmpty h]
  rfl

theorem isEmpty_of_length_eq_zero {α : Type} {l : List α} (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t => simp at h

end NearSpecV3.D0SubD1.Work.Root
