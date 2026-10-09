import ZkFormal.NearV3.Qv.Extract.BalancedFinal

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (tau vid)

/-- Canonical walk metadata turns the physical FINAL equality into ordinary
natural transition, terminal-kind and value-record equality. -/
theorem final_natural {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    {ws : List WalkR} (hW : WalkWf3 ws) {w : WalkR} (hw : w∈ws)
    (he : Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt r pub) :
    w.tau=cv tr tt r tau ∧ w.fk=cv tr tt r absent ∧ w.k=cv tr tt r vid := by
  have hc := hW.canon w hw
  have hlen := hW.len w hw
  have hlast := hc.2.2 w.last (Walk3.row_mem (by omega))
  have hfk : w.fk<P := by
    unfold WalkR.fk
    split <;> decide
  have hk : w.k<P := by
    unfold WalkR.k
    split
    · exact Link.getD_lt hlast.2.2.2 _
    · unfold P; omega
  have ht := congrArg (fun xs : List Fp => xs.getD 1 0) he
  have hf := congrArg (fun xs : List Fp => xs.getD 2 0) he
  have hv := congrArg (fun xs : List Fp => xs.getD 3 0) he
  change (w.tau:Fp)=tr.cell tt r tau at ht
  change (w.fk:Fp)=tr.cell tt r absent at hf
  change (w.k:Fp)=tr.cell tt r vid at hv
  rw [cell_eq_cast] at ht hf hv
  exact ⟨ofNat_inj hc.2.1 (cv_lt _ _ _ _) ht,
    ofNat_inj hfk (cv_lt _ _ _ _) hf,ofNat_inj hk (cv_lt _ _ _ _) hv⟩

/-- Compose the actual key/FINAL bindings with existing authenticated trie
soundness. The queue value ID now selects the native trie lookup result. -/
theorem native_trie_read_of_walk {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    {f : Nat→Nat} {vs : List NodeS3} {V : List ValRec3} {hs : List HeadE} {ws : List WalkR}
    (G : Walk3.WalkHyp f vs V hs ws) {w : WalkR} (hw : w∈ws) (bs : NearSpec.Bytes)
    (hkey : w.key3=NearSpec.nibbles bs)
    (hfinal : Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt r pub) :
    ∃ head∈hs, head.tau=cv tr tt r tau ∧
      (cv tr tt r absent=FK_VAL →
        (fullTree (Link3.recsOf f vs) V head.rid).find (NearSpec.nibbles bs)=
          some (some (valOf V (f (cv tr tt r vid))))) ∧
      (cv tr tt r absent=FK_ABS →
        (fullTree (Link3.recsOf f vs) V head.rid).find (NearSpec.nibbles bs)=some none) := by
  obtain ⟨ht,hfk,hv⟩ := final_natural G.walk hw hfinal
  obtain ⟨head,hh,htau,hval,habs⟩ := Walk3.walk3_find_of G hw
  rw [hkey,hfk,hv] at hval
  rw [hkey,hfk] at habs
  exact ⟨head,hh,htau.trans ht,hval,habs⟩

end ZkFormal.NearV3.Qv.Extract
