import ReexecNpai.Spec.State

/-!
# Batch, part 1: target keys and walks

* `pKey`: the target key `accountKeyPath receiver` as one nibble per byte at `S_KEY`;
* `pWalk`: `PTrie.get` on the arena (the `Walk` relation of `Trie/Arena.lean`).
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Nibbles stored one per byte. -/
def nibBytes (k : List Nat) : Bytes := k.map fun x => UInt8.ofNat x

/-- Registers 14/15 hold the constants, memory outside `[lo, hi)` is unchanged. -/
def KeepOut (lo hi : Nat) (m m' : M) : Prop :=
  m'.regs 14 = m.regs 14 ∧ m'.regs 15 = m.regs 15 ∧ ∀ a, (a < lo ∨ hi ≤ a) → m'.mem a = m.mem a

section
variable {pub cb pb : Bytes}

theorem key_wp {m : M} (hb : Base m) (hp : m.regs 1 + m.regs 2 ≤ P.memSize) (hlen : m.regs 2 ≤ 64) :
    wp P (Inp pub cb pb) pKey m (fun m' =>
      readMem m'.mem S_KEY (2 + 2 * m.regs 2) = nibBytes (accountKeyPath (readMem m.mem (m.regs 1) (m.regs 2))) ∧
      m'.regs 3 = 2 + 2 * m.regs 2 ∧ KeepOut S_KEY (S_KEY + 130) m m' ∧ Frame [0, 3, 4, 11, 12, 13] m m') := by
  sorry

theorem key_twp {m : M} (hb : Base m) (hp : m.regs 1 + m.regs 2 ≤ P.memSize) (hlen : m.regs 2 ≤ 64) :
    twp P (Inp pub cb pb) pKey m (fun m' c =>
      readMem m'.mem S_KEY (2 + 2 * m.regs 2) = nibBytes (accountKeyPath (readMem m.mem (m.regs 1) (m.regs 2))) ∧
      m'.regs 3 = 2 + 2 * m.regs 2 ∧ KeepOut S_KEY (S_KEY + 130) m m' ∧ Frame [0, 3, 4, 11, 12, 13] m m' ∧
      c ≤ 2000) := by
  sorry

/-- The entry the walk starts from. -/
def rootRes (A : List Ent) : Nat := (A.getD (A.length - 1) default).res

theorem walk_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16)
    (hkl : key.length ≤ 130) (h3 : m.regs 3 = key.length) :
    wp P (Inp pub cb pb) pWalk m (fun m' => ∃ f, Walk A K (rootRes A) key f ∧ f < A.length ∧
      m'.regs 0 = f ∧ m'.regs 9 = m.regs 9 ∧ KeepOut S_HP (S_HP + 128) m m') := by
  sorry

theorem walk_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16)
    (hkl : key.length ≤ 130) (h3 : m.regs 3 = key.length) {f : Nat} (hw : Walk A K (rootRes A) key f) :
    twp P (Inp pub cb pb) pWalk m (fun m' c => m'.regs 0 = f ∧ f < A.length ∧ m'.regs 9 = m.regs 9 ∧
      KeepOut S_HP (S_HP + 128) m m' ∧ c ≤ 60000) := by
  sorry

end

end ReexecNpai
