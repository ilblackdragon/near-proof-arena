import ZkFormal.NearV3.Candidates.SchedSetAll
namespace ZkFormal.NearV3.Candidates.SchedSetAllRange
open ZkFormal.NearV3.Sched.Gen SchedSetAll

/-- Contiguous native register assignment, as used for Codec byte registers. -/
def block (base len : Nat) (value : Nat→Nat) : List (Nat×Nat) :=
  (List.range len).map fun i=>(base+i,value i)

theorem lookup_block (base len : Nat) (value : Nat→Nat) (c v : Nat) :
    lookup (block base len value) c v =
      if base≤c ∧ c<base+len then value (c-base) else v := by
  induction len with
  | zero => simp [block,lookup]; omega
  | succ len ih =>
    have he : block base (len+1) value=block base len value++[(base+len,value len)] := by
      simp [block,List.range_succ]
    rw [he,append]
    change (if base+len=c then value len else lookup (block base len value) c v)=_
    rw [ih]
    by_cases hl:base+len=c
    · rw [if_pos hl,if_pos (by omega)]
      congr 1; omega
    · rw [if_neg hl]
      have hh:(base≤c ∧ c<base+len) ↔ (base≤c ∧ c<base+(len+1)) := by omega
      simp only [hh]

theorem read_block (w base len c : Nat) (value : Nat→Nat) (before : List (Nat×Nat))
    (hc:c<w) (hb:base≤c) (hl:c<base+len) :
    (setAll w (before++block base len value))[c]! = value (c-base) := by
  rw [SchedSetAll.cell w _ c hc,append,lookup_block,if_pos ⟨hb,hl⟩]

theorem miss_block (base len c v : Nat) (value : Nat→Nat)
    (hc:c<base ∨ base+len≤c) :
    lookup (block base len value) c v=v := by
  rw [lookup_block,if_neg (by omega)]

end ZkFormal.NearV3.Candidates.SchedSetAllRange
