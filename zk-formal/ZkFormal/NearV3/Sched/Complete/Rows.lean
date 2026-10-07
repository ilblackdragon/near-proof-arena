import ZkFormal.NearV3.Sched.Complete.Trace
import ZkFormal.NearV3.Sched.Gen.Proc
import ZkFormal.NearV3.Sched.Gen.Scan

/-!
# ZkFormal.NearV3.Sched.Complete.Rows — row counts of the generated process and scan rows (M4)

* `proc_rows_size`: `sprV3` has `16` key rows, then per round a header and its entries;
* `scan_rows_size`: the scan part of `ssdV3` has a param row and `20` rows per converted request
  (none without a converted request).

With `Gen.Cmp.rows` (`rows_size`) and `Gen.Mem.rows` (`memRows_size`, `memVs_length`) these tie
`Complete/Height`'s per-instance counts to the generators.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem size_foldl_push {α β : Type} (g : α → β) : ∀ (l : List α) (a : Array β),
    (l.foldl (fun b x => b.push (g x)) a).size = a.size + l.length
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, size_foldl_push g l]; simp; omega

theorem roundRows_size (R : Run) (rd : RoundD) : (Gen.Proc.roundRows R rd).size = 1 + rd.entries.length := by
  unfold Gen.Proc.roundRows
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  show (List.foldl _ _ _ : Array (Array Nat)).size = _
  rw [size_foldl_push]
  simp

theorem foldl_append_size {α : Type} (f : α → Array (Array Nat)) : ∀ (l : List α) (acc : Array (Array Nat)),
    (l.foldl (fun acc x => acc ++ f x) acc).size = acc.size + (l.map fun x => (f x).size).sum
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_append_size f l, Array.size_append, List.map_cons, List.sum_cons]; omega

theorem proc_rows_size (R : Run) :
    (Gen.Proc.rows R).size = 16 + (R.rounds.map fun rd => 1 + rd.entries.length).sum := by
  unfold Gen.Proc.rows
  rw [foldl_append_size]
  simp [roundRows_size]

/-- A loop in `Id` whose every step yields a state with one more row. -/
theorem forIn_size {β γ : Type} (l : List Nat) (f : Nat → Array β × γ → Id (ForInStep (Array β × γ)))
    (hf : ∀ a s, ∃ s', f a s = .yield s' ∧ s'.1.size = s.1.size + 1) :
    ∀ s, (Id.run (forIn l s f)).1.size = s.1.size + l.length := by
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    obtain ⟨s', h1, h2⟩ := hf a s
    rw [List.forIn_cons]
    simp only [h1]
    show (Id.run (forIn l s' f)).1.size = _
    rw [ih s', h2, List.length_cons]; omega

theorem reqRows_size (R : Run) (c : CReq) : (Gen.Scan.reqRows R c).size = 20 := by
  unfold Gen.Scan.reqRows
  show (Id.run (forIn (List.range 20) ((#[] : Array (Array Nat)), (0 : Nat), R.base) _)).1.size = 20
  refine (forIn_size _ _ ?_ _).trans ?_
  · intro a s; exact ⟨_, rfl, Array.size_push _⟩
  · simp

theorem sum_const20 {α : Type} : ∀ l : List α, (l.map fun _ => 20).sum = 20 * l.length
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_const20 l, List.length_cons]; omega

theorem scan_rows_size (R : Run) :
    (Gen.Scan.rows R).size = if R.conv.isEmpty then 0 else 1 + 20 * R.conv.length := by
  unfold Gen.Scan.rows
  split
  · rfl
  · rw [foldl_append_size]
    simp only [reqRows_size, sum_const20]
    rfl

end ZkFormal.NearV3.Sched.Complete
