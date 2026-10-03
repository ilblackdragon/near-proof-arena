import ReexecNpai.Spec.State

/-!
# The record-parse loop invariant

`pParse` runs `pRecord` (decode one post-order record into a new arena entry
and push it) while `P < E`. `ParseInv … o A K S rv m` describes the state
after `A.length` records ending at proof offset `o`:

* the Lean decoder agrees: `decRecs A.length [] (pb.drop (R + 4))` yields the
  stack of the subtrees of the stack entries `S` (bottom first; the Lean stack
  is top first) and the rest `pb.drop o`;
* every entry is well formed (`NodeWF`) w.r.t. the final arena `A`/child list
  `K` built so far — a `NodeWF` only mentions entries `≤ j` and child-list
  entries already written, and the parse never changes them again except the
  `pslot` of popped children, which is not part of a child's own `NodeWF`;
* records are contiguous from `PF + R + 4` to `PF + o`; the stack entries'
  subtrees are consecutive intervals `[0, S₀], [S₀ + 1, S₁], …` ending at the
  last entry;
* arena, child list and stack contents are in memory; registers
  `r10 = PF + o`, `r9 = E`, `r8 = A.length`, `r7 = S.length`, `r5 = rv` (the
  revealed bytes so far); cell `C_KC = K.length`, `C_NODES` = the header count.
-/

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Revealed bytes of one entry: its preimage and its revealed value. -/
def entRev (pb : Bytes) (e : Ent) : Nat := e.preLen + (if hasVal e.nf then vlenAt pb e else 0)

/-- Sum of `entRev` over the entries. -/
def revSum (pb : Bytes) (A : List Ent) : Nat := (A.map (entRev pb)).foldl (· + ·) 0

/-- Stack entries: consecutive subtree intervals, the first starting at entry
`0`, the last ending at the last entry. -/
def StackOK (A : List Ent) (S : List Nat) : Prop :=
  (S = [] → A = []) ∧
  (∀ i (h : i < S.length), S[i] < A.length) ∧
  (∀ (h : 0 < S.length), (A.getD S[0] default).lo = 0) ∧
  (∀ i (h : i + 1 < S.length), (A.getD S[i + 1] default).lo = S[i] + 1) ∧
  (∀ (h : 0 < S.length), S[S.length - 1] + 1 = A.length)

structure ParseInv (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (K : List Nat)
    (S : List Nat) (m : M) : Prop where
  st : RcptsSt cb pb rs R m
  rP : m.regs 10 = PF + o
  rE : m.regs 9 = PF + pb.length
  re : m.regs 8 = A.length
  rsp : m.regs 7 = S.length
  rrv : m.regs 5 = revSum pb A
  kc : rd32 m C_KC = K.length
  hdr : rd32 m C_NODES = N
  oR : R + 4 ≤ o
  ole : o ≤ pb.length
  cap : A.length ≤ NCAP
  dec : decRecs A.length [] (pb.drop (R + 4)) =
    some ((S.map (treeAt A K (vals0 pb A))).reverse, pb.drop o)
  wf : ∀ j, j < A.length → NodeWF pb A K j
  first : 0 < A.length → (A.getD 0 default).rst = PF + R + 4
  contig : ∀ j, j + 1 < A.length →
    (A.getD j default).pre + (A.getD j default).preLen = (A.getD (j + 1) default).rst
  last : (0 < A.length → (A.getD (A.length - 1) default).pre + (A.getD (A.length - 1) default).preLen = PF + o) ∧
    (A.length = 0 → o = R + 4)
  stack : StackOK A S
  amem : ∀ j (h : j < A.length), EntMem m j A[j]
  kmem : ∀ i (h : i < K.length), rd32 m (KL + 4 * i) = K[i]
  krange : ∀ j (h : j < A.length), A[j].kid + nKids A[j].nf ≤ K.length
  smem : ∀ i (h : i < S.length), rd32 m (STK + 4 * i) = S[i]
  klen : K.length + S.length = A.length

end ReexecNpai
