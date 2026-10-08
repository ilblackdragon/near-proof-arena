import ZkFormal.NearV3.Assembly.RcptNativeEndCheckpoint
import ZkFormal.Near.Render.Proof.RcptChars1

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The unchanged byte-local account-character equations. The system and named
receiver aggregate checks occur later in cChars and are not included here. -/
def charLocalConstraints : List Expr := cChars.take 32

theorem charLocalConstraints_legacy : charLocalConstraints=Rcpt.cChars.take 32 := rfl

set_option maxRecDepth 4096 in
theorem charLocalConstraints_shape : charLocalConstraints.length=32 ∧
    charLocalConstraints.all ZkFormal.Near.Render.RcptP.charLoc=true ∧
    charLocalConstraints.all currentExpr=true ∧
    charLocalConstraints.all noEmissionExpr=true := by decide

theorem charLocalConstraints_string (ch s : Nat) (hc : ch<256)
    (hv : ZkFormal.Near.Render.RcptP.vch ch=true) (hs : s∈[sP,sV,sS]) :
    ∀e∈charLocalConstraints,
      ZkFormal.Near.Render.RcptP.evR (ZkFormal.Near.Render.RcptP.chRow ch s)
        (fun _=>0) false false [] e=0 := by
  intro e he
  have hm : e∈Rcpt.cChars := List.mem_of_mem_take (charLocalConstraints_legacy ▸ he)
  have hf := List.all_eq_true.mp charLocalConstraints_shape.2.1 e he
  exact ZkFormal.Near.Render.RcptP.char_local ch hc hv s hs e hm hf

end ZkFormal.NearV3.Assembly.RcptSkeleton
