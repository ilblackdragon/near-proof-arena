import ZkFormal.NearV3.Qv.Extract.NativeTrieRead

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (tau vid)

/-- The record trie's value at an actual ValE ID is exactly that record's
native bytes, even when the consecutive field IDs wrap. -/
theorem native_value_at (vs : List NodeS3) {es : List ValE} (hv : ValWf es)
    {e : ValE} (he : e∈es) :
    valOf (Link3.valsOf3 vs es) (Link3.vpos (Link3.vid0 es) e.vid)=toBytes e.bytes := by
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem he
  rw [Link3.vpos_at hv (Link3.vlen_le hv) hj]
  simp [valOf,Link3.valsOf3,List.getElem?_eq_getElem hj]
  rfl

/-- The parser-selected ValE bytes are the actual native lookup result, using
KEYNIB/FINAL bindings and authenticated trie semantics for the same walk. -/
theorem native_trie_value_read {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    {vs : List NodeS3} {es : List ValE} {hs : List HeadE} {ws : List WalkR}
    (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hs ws)
    (hv : ValWf es) {e : ValE} (he : e∈es) (hid : e.vid=cv tr tt r vid)
    {w : WalkR} (hw : w∈ws) (bs : NearSpec.Bytes)
    (hkey : w.key3=NearSpec.nibbles bs)
    (hfinal : Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt r pub)
    (hpresent : cv tr tt r absent=0) :
    ∃ head∈hs, head.tau=cv tr tt r tau ∧
      (fullTree (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs)
        (Link3.valsOf3 vs es) head.rid).find (NearSpec.nibbles bs)=some (some (toBytes e.bytes)) := by
  obtain ⟨head,hh,ht,hval,_⟩ := native_trie_read_of_walk G hw bs hkey hfinal
  have hfind := hval hpresent
  rw [←hid,native_value_at vs hv he] at hfind
  exact ⟨head,hh,ht,hfind⟩

end ZkFormal.NearV3.Qv.Extract
