import ZkFormal.Near.Render.Proof.NodeLinks

/-!
# ZkFormal.Near.Render.Proof.NodeLinks2 — `cLinks` on `HPF` and `KEY` rows
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

set_option maxHeartbeats 8000000 in
theorem lnk_hpf (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (fst : Int)
    (h : LinkHyp I ⟨rn, pos, .hpf, j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .hpf, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk_tac

set_option maxHeartbeats 8000000 in
theorem lnk_key (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (fst : Int)
    (h : LinkHyp I ⟨rn, pos, .key, j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .key, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk_tac

end NodeRow

end ZkFormal.Near.Render
