import ZkFormal.NearV3.Qv.Extract.NativeQueueValue
import ZkFormal.NearV3.Link.Chain3

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

def queueTree (vs : List NodeS3) (es : List ValE) (hs : List HeadE) (tau : Nat) : NearSpec.PTrie :=
  fullTree (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsOf3 vs es) (headAt hs tau).rid

/-- ROOT/MIDROOT authentication puts all reads for one transition on the same
canonical head; physical constraints supply the absent bit. -/
theorem queue_root_read {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) (i : Nat) (hi : i<q.segs.length)
    {vs : List NodeS3} {es : List ValE} {hs : List HeadE} {ws : List WalkR}
    {us : List UpsE} {K : Nat} {r0 rK : List Nat}
    (C : RootChain hs us K r0 rK)
    (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hs ws)
    {w : WalkR} (hw : w∈ws)
    (hkey : w.key3=NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))
    (hfinal : Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt (q.segs[i]'hi).1 pub) :
    (queueTree vs es hs (cv tr tt (q.segs[i]'hi).1 Candidates.ValueTable.tau)).find
      (NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))=
      some (queueValue vs es tr tt (q.segs[i]'hi).1) := by
  have hab := isBool hL (q.start_lt i hi) (x:=absent) (by simp [walkBools])
  have ha : cv tr tt (q.segs[i]'hi).1 absent=0 ∨ cv tr tt (q.segs[i]'hi).1 absent=1 := by
    rcases hab with hb|hb
    · left; simp only [cv,hb]; decide
    · right; simp only [cv,hb]; decide
  obtain ⟨head,hh,ht,hread⟩ := queue_value_read G hw _ hkey hfinal ha
  have he := (C.head_all head hh).2
  rw [ht] at he
  rw [he] at hread
  exact hread

/-- All three fixed main keys read the same authenticated pre-state head. -/
theorem main_fixed_root_read {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) (i : Nat) (hi : i<q.segs.length)
    (hm : tr.cell tt (q.segs[i]'hi).1 main=1) (hsmall : i<3)
    {vs : List NodeS3} {es : List ValE} {hs : List HeadE}
    (hr : (queueTree vs es hs (cv tr tt (q.segs[i]'hi).1 Candidates.ValueTable.tau)).find
      (NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))=
      some (queueValue vs es tr tt (q.segs[i]'hi).1)) :
    (queueTree vs es hs 0).find (if i=0 then NearSpecV3.keyDelayedIdx else
      if i=1 then NearSpecV3.keyBufferedIdx else NearSpecV3.keyYieldIdx)=
      some (queueValue vs es tr tt (q.segs[i]'hi).1) := by
  have ht := con hL (q.start_lt i hi) (e:=.mul (c main) (c Candidates.ValueTable.tau))
    (by simp [constraints])
  simp only [eval_mul,eval_c,hm] at ht
  have hz : tr.cell tt (q.segs[i]'hi).1 Candidates.ValueTable.tau=0 := by grind
  have hc : cv tr tt (q.segs[i]'hi).1 Candidates.ValueTable.tau=0 := by simp only [cv,hz]; decide
  rw [hc,main_fixed_key hL q i hi hm hsmall] at hr
  exact hr

end ZkFormal.NearV3.Qv.Extract
