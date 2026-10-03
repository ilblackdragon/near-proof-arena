import ReexecNpai.Spec.RecAux32

/-!
# One record of the trie section

`pRecord` (followed by the loop test `LTU 4 10 9`) decodes the post-order
record at `P = PF + o` exactly like `decRec`, appends the arena entry, pops its
revealed children (setting their `pslot`, appending them to the child list)
and pushes the new entry.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes}

theorem record_wp {rs : List Receipt} {R N o : Nat} {A : List Ent} {K : List Nat} {S : List Nat} {m : M}
    (h : ParseInv cb pb rs R N o A K S m) (hlt : o < pb.length) :
    wp P (Inp pub cb pb) (.seq pRecord (LTU 4 10 9)) m (fun m' => ∃ o' A' K' S',
      ParseInv cb pb rs R N o' A' K' S' m' ∧ A'.length = A.length + 1 ∧ o < o' ∧
      m'.regs 4 = (if o' < pb.length then 1 else 0)) :=
  rec_wp h hlt

theorem record_twp {rs : List Receipt} {R N o : Nat} {A : List Ent} {K : List Nat} {S : List Nat} {m : M}
    (h : ParseInv cb pb rs R N o A K S m) (hlt : o < pb.length) (hcap : A.length < NCAP)
    {stk' : List PTrie} {o' : Nat}
    (hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) = some (stk', pb.drop o'))
    (ho' : o' ≤ pb.length) :
    twp P (Inp pub cb pb) (.seq pRecord (LTU 4 10 9)) m (fun m' c => ∃ A' K' S',
      ParseInv cb pb rs R N o' A' K' S' m' ∧ A'.length = A.length + 1 ∧
      m'.regs 4 = (if o' < pb.length then 1 else 0) ∧ c ≤ 80 * (o' - o)) :=
  twp_mono (rec_twp h hlt hcap hd ho') (fun _ _ ⟨⟨A', K', S', a, b, d⟩, hc⟩ => ⟨A', K', S', a, b, d, hc⟩)

end

end ReexecNpai
