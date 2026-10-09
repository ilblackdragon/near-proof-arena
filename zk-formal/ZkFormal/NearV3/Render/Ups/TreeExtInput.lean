import ZkFormal.NearV3.Render.Ups.TreePartEncoding
import ZkFormal.NearV3.Render.Ups.RdeInput
import ZkFormal.NearV3.Render.Ups.PtInput
import ZkFormal.NearV3.Extract.Ups.UpsLink

/-! Both runtime extension-ancestor cases derive byte completeness from the actual
recursive upsert result. Output well-formedness and memory bounds are not assumed. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec ZkFormal.Near ZkFormal.Near.Render

theorem treeKid_upsert_wf {t result : PTrie} {key : List Nat} {v : Bytes}
    (hu : t.upsert key v=some result) : (treeKid result).wf := by
  have hn := upsert_isNode t key v result hu
  simp [treeKid,NKid.wf,hashOf_eq_enc result hn]

def treeExt_byteInput (I : UpsInst) (base : UpsPartI) (key : List Nat) (child : PTrie)
    (mem cm : Nat) (rest : List Nat) (v : Bytes) (run : TreeRun) (Q : UpsPartI)
    (hr : traceUpsert child rest v=some run)
    (he : encodeTreePart base ⟨if key.isEmpty then .PT else .RDE,
      .ext key child mem,qRDE key mem run.output cm,0⟩=some Q)
    (hs : (PTrie.ext key child mem).wf=true)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  have hu : child.upsert rest v=some run.output := by
    have h := traceUpsert_output child rest v
    simpa [hr] using h.symm
  have hsrc := treeNode_wf hs rfl
  have hdst : (NodeV3.ext key (treeKid run.output)
      ((u64 (mem+run.output.memD-cm)).map UInt8.toNat)).wf :=
    ⟨hsrc.1,by simp [treeKid],treeKid_upsert_wf hu,by simp⟩
  have hb := treeNode_byte_bound hs rfl true
  cases key with
  | nil =>
    simp [encodeTreePart,treeNode,qRDE] at he
    subst Q
    exact pt_byteInput I _ rfl _ _ _ _ hsrc hdst hb hts hx
  | cons n ns =>
    simp [encodeTreePart,treeNode,qRDE] at he
    subst Q
    exact rde_byteInput I _ rfl _ _ _ _ _ hsrc hdst hb hts hx

end ZkFormal.NearV3.Render.UpsGen
