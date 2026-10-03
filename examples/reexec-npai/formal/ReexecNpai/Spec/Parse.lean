import ReexecNpai.Spec.Record

/-!
# Phase spec: the trie section (record parse into the arena)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes}

theorem parse_wp {m : M} {rs : List Receipt} {R : Nat} (h : RcptsSt cb pb rs R m) :
    wp P (Inp pub cb pb) pParse m (fun m' => ∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m') := by
  sorry

theorem parse_twp {m : M} {rs : List Receipt} {R : Nat} (h : RcptsSt cb pb rs R m) {t : PTrie}
    (hd : decTrie (pb.drop R) = some t) (hs : t.revealedBytes ≤ Params.maxWitnessBytes) :
    twp P (Inp pub cb pb) pParse m (fun m' c => ∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m' ∧
      rootT A K (vals0 pb A) = t ∧ c ≤ 80 * pb.length + 10000) := by
  sorry

end

end ReexecNpai
