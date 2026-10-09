import ZkFormal.NearV3.Assembly.CompactDigestWindows
import ZkFormal.NearV3.Assembly.SchedulerChildDigests

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- The allocated output-byte vector is the exact native serialized part,
using the same index as its SHA job. -/
theorem allocated_node_bytes {u : SchedulerUpsertWitness} {I : Render.UpsInst}
    (hs : NativeShaFamily u I) {k : Nat} (hk : k<nQ I) :
    ∃p,u.run.parts[k]?=some p ∧ (part I k).q=(nodeEnc p.output).map UInt8.toNat := by
  have hb : k<u.run.parts.length := by rw [←hs.1];exact hk
  let p:=u.run.parts[k]
  have hp : u.run.parts[k]?=some p := List.getElem?_eq_getElem hb
  obtain ⟨M,hM,_,hbytes⟩:=hs.2 k hk
  rw [upsertShaJobs_part,hp] at hM
  have he : upsertShaJob I.tau (k+1) (nodeEnc p.output)=M := Option.some.inj hM
  subst M
  exact ⟨p,hp,hbytes.symm⟩

/-- Every physical requested node window is a slice of the SAME native
output serialization. This is exact even when its field cells wrap; it does
not yet assert the child-reference demand permutation. -/
theorem allocated_node_window {u : SchedulerUpsertWitness} {I : Render.UpsInst}
    (hs : NativeShaFamily u I) {k : Nat} (hk : k<nQ I) (pos : Nat) :
    ∃p,u.run.parts[k]?=some p ∧
      nodeDigestMsgs I k pos=
        let Q:=part I k
        let f:=fieldAt Q.shape pos
        if GdB I Q f.1 f.2.1 f.2.2.2=true then
          [digMsg ((dIV I Q f.1 f.2.1 f.2.2.2 k : Fp).toNat)
            ((dLV I Q f.1 f.2.1 f.2.2.2 : Fp).toNat)
            ((List.range 32).map fun i=>
              (Fp.ofNat (((nodeEnc p.output).map UInt8.toNat).getD (pos+i) 0)).toNat)] else [] := by
  obtain ⟨p,hp,hq⟩:=allocated_node_bytes hs hk
  refine ⟨p,hp,?_⟩
  dsimp only [nodeDigestMsgs]
  rw [hq]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
