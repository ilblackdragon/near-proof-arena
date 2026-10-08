import ZkFormal.NearV3.Qv.Extract.NativeValueLookup

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (vid tau)

/-- Deterministic native value recovered from a physical queue request. -/
def queueValue (vs : List NodeS3) (es : List ValE) (tr : Trace Fp) (tt r : Nat) :
    Option NearSpec.Bytes :=
  if cv tr tt r absent=0 then
    some (valOf (Link3.valsOf3 vs es) (Link3.vpos (Link3.vid0 es) (cv tr tt r vid)))
  else none

theorem queue_value_read {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    {vs : List NodeS3} {es : List ValE} {hs : List HeadE} {ws : List WalkR}
    (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hs ws)
    {w : WalkR} (hw : w∈ws) (bs : NearSpec.Bytes)
    (hkey : w.key3=NearSpec.nibbles bs)
    (hfinal : Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt r pub)
    (ha : cv tr tt r absent=0 ∨ cv tr tt r absent=1) :
    ∃ head∈hs, head.tau=cv tr tt r tau ∧
      (fullTree (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs)
        (Link3.valsOf3 vs es) head.rid).find (NearSpec.nibbles bs)=some (queueValue vs es tr tt r) := by
  obtain ⟨head,hh,ht,hval,habs⟩ := native_trie_read_of_walk G hw bs hkey hfinal
  refine ⟨head,hh,ht,?_⟩
  rcases ha with ha|ha
  · simpa only [queueValue,ha,ite_true] using hval ha
  · simpa only [queueValue,ha,show ¬(1:Nat)=0 by decide,ite_false] using habs ha

/-- Existing physical empty-parser evidence certifies the recovered value,
including absent requests. -/
theorem queue_value_empty (vs : List NodeS3) {es : List ValE} (hv : ValWf es)
    (tr : Trace Fp) (tt r : Nat)
    (hp : cv tr tt r absent=0 →
      ∃ e∈es, e.vid=cv tr tt r vid ∧ EmptyQueue (some (toBytes e.bytes))) :
    EmptyQueue (queueValue vs es tr tt r) := by
  unfold queueValue
  split
  next ha =>
    obtain ⟨e,he,hid,hv'⟩ := hp ha
    rw [←hid,native_value_at vs hv he]
    exact hv'
  next => trivial

/-- Buffered parser evidence and its absent-count rule recover the SAME native
shard list used for the group-key requests. -/
theorem queue_value_buffered (vs : List NodeS3) {es : List ValE} (hv : ValWf es)
    (tr : Trace Fp) (tt r : Nat) (ss : List Nat)
    (hp : cv tr tt r absent=0 →
      ∃ e∈es, e.vid=cv tr tt r vid ∧ BufferedValue (some (toBytes e.bytes)) ss)
    (ha : cv tr tt r absent≠0 → ss=[]) :
    BufferedValue (queueValue vs es tr tt r) ss := by
  unfold queueValue
  split
  next hz =>
    obtain ⟨e,he,hid,hv'⟩ := hp hz
    rw [←hid,native_value_at vs hv he]
    exact hv'
  next hz => simpa only [BufferedValue] using ha hz

end ZkFormal.NearV3.Qv.Extract
