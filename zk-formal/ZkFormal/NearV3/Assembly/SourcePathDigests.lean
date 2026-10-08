import ZkFormal.NearV3.Rcpt.Render.Srcp.FromProofFacts
import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near Render.SrcpGen

def sourceItemOutput (it : SrcpItem) : Msg := Render.digestMsg ⟨msgId K_SRC it.q,it.bytes⟩
def sourceItemInput (it : SrcpItem) : Msg := digMsg (msgId K_SRC it.pq) it.pl it.acc

private theorem step_digest (q len : Nat) (acc : Bytes) (step : Bytes×Nat)
    (ha : acc.length=32) (hs : step.1.length=32) :
    sourceItemOutput ({ q := q+1, dir := decide (step.2≠0), sib := step.1.map UInt8.toNat, acc := acc.map UInt8.toNat, pq := q, pl := len } : SrcpItem)=
      digMsg (msgId K_SRC (q+1)) 64 ((proofHashStep acc step).map UInt8.toNat) := by
  by_cases hd : step.2=0 <;>
    simp [sourceItemOutput,SrcpItem.bytes,Render.digestMsg,Render.shaN,Render.ofNats,
      Render.toNats,digMsg,proofHashStep,hd,List.map_map,Function.comp_def,ha,hs]

/-- Executable proofItems form a digest chain. Every intermediate output is
consumed exactly once; the only remaining output is the actual computed root. -/
theorem proofItems_digest_chain (path : List (Bytes×Nat)) (q len : Nat) (acc : Bytes)
    (ha : acc.length=32) (hp : ∀step∈path,step.1.length=32) :
    digMsg (msgId K_SRC q) len (acc.map UInt8.toNat)::
      (proofItems q len acc path).map sourceItemOutput =
    (proofItems q len acc path).map sourceItemInput ++
      [digMsg (msgId K_SRC (q+path.length)) (if path=[] then len else 64)
        ((rootFromPath acc path).map UInt8.toNat)] := by
  induction path generalizing q len acc with
  | nil => simp [proofItems,rootFromPath]
  | cons step rest ih =>
    have hs := hp step (by simp)
    have hi := ih (q+1) 64 (proofHashStep acc step) (proofHashStep_length _ _)
      (fun s h=>hp s (by simp [h]))
    simp only [proofItems,List.map_cons,List.cons_append,sourceItemInput]
    rw [step_digest q len acc step ha hs]
    have hr : rootFromPath acc (step::rest)=rootFromPath (proofHashStep acc step) rest := by
      cases step; rfl
    rw [hr]
    simp only [List.length_cons,List.cons_ne_nil,ite_false]
    rw [hi]
    have hq : q+1+rest.length=q+(rest.length+1) := by omega
    rw [hq]
    simp

end ZkFormal.NearV3.Assembly
