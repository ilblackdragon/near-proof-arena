import ReexecNpai.Spec.State

/-!
# Phase spec: the hash pass and the root comparison
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes}

theorem hash_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) :
    wp P (Inp pub cb pb) pHash m (fun m' => TrieSt cb pb rs R A K vals m' ∧
      readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf) := by
  sorry

theorem hash_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) :
    twp P (Inp pub cb pb) pHash m (fun m' c => TrieSt cb pb rs R A K vals m' ∧
      readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf ∧ c ≤ 20 * pb.length + 10000) := by
  sorry

theorem rootIs_wp {m : M} {a : Nat} {d : Bytes} (hk : Base m) (hd : readMem m.mem C_ROOT 32 = d)
    (ha : a + 32 ≤ CELL) :
    wp P (Inp pub cb pb) (pRootIs a) m (fun m' => d = readMem m.mem a 32 ∧ m'.mem = m.mem ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  sorry

theorem rootIs_twp {m : M} {a : Nat} {d : Bytes} (hk : Base m) (hd : readMem m.mem C_ROOT 32 = d)
    (ha : a + 32 ≤ CELL) (he : d = readMem m.mem a 32) :
    twp P (Inp pub cb pb) (pRootIs a) m (fun m' c => m'.mem = m.mem ∧ (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      m'.regs j = m.regs j) ∧ c ≤ 20) := by
  sorry

end

end ReexecNpai
