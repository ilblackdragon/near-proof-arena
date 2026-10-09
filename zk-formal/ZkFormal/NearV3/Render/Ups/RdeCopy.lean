import ZkFormal.NearV3.Render.Ups.EncodePart
import ZkFormal.NearV3.Render.Ups.CopyPrefix

/-! Actual extension-child replacement preserves the complete serialized key prefix. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem rde_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=1)
    (key : List Nat) (old new : NKid) (oldMem newMem : List Nat)
    (hw : (NodeV3.ext key new newMem).wf) :
    CopyFields I (encodePart base (.ext key old oldMem) (.ext key new newMem)) := by
  let Q := encodePart base (.ext key old oldMem) (.ext key new newMem)
  have hf : FieldsOk Q := encodePart_fields _ _ _ hw
  have ht : Q.ty=1 := rfl
  have hkind : Q.kind=1 := hk
  have hn : nWin Q.shape=1 := hf.extension ht
  let fields := valuePrefix 0 Q.qhk
  let headBytes := [3] ++ u32Bytes (hpN key false).length ++ hpN key false
  have hshape : Q.shape=fields++[(7,32),(8,8)] := by
    calc Q.shape = nodeFields Q.ty Q.qhk (nWin Q.shape) := hf.shape
         _ = _ := by simp [fields,nodeFields,valuePrefix,ht,hn,List.append_assoc]
  have hheadBytes : fieldsLen fields=headBytes.length := by
    have hh : 1≤Q.qhk := hf.prefixLength (by omega)
    have hq : Q.qhk=1+key.length/2 := rfl
    by_cases h : 1<Q.qhk <;>
      simp [fields,valuePrefix,h,fieldsLen_append,headBytes,u32Bytes,NodeGen3.hpN_len] <;> omega
  refine ⟨?_⟩
  intro pre post st width he hc
  change Q.shape=pre++(st,width)::post at he
  change CpB I Q st (nWin pre)=true at hc
  have hnot : (st,width) ∉ [(7,32),(8,8)] := by
    intro hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with he | he <;> cases he <;> simp [CpB,VcpB,WfrB,hkind] at hc
  have hb := field_headBytes_bound fields [(7,32),(8,8)] pre post (st,width) (hshape.symm.trans he) hnot
  have hstart : sourceFieldStart I Q st (nWin pre) (fieldsLen pre)=(fieldsLen pre : Int) := by
    simp [sourceFieldStart,hkind]
  refine ⟨by simp [encodePart,hk],by rw [hstart]; omega,?_⟩
  change FieldPayloadEdit (Q.kind==5 && st==6) (if I.ts=1 then 0 else 15)
    ((Q.pb.drop (sourceFieldStart I Q st (nWin pre) (fieldsLen pre)).toNat).take width)
    ((Q.q.drop (fieldsLen pre)).take width)
  simp only [hkind,Nat.reduceBEq,Bool.false_and,hstart]
  have hnat : ((fieldsLen pre : Nat) : Int).toNat=fieldsLen pre := by omega
  rw [hnat]
  have hbytes : ((Q.q.drop (fieldsLen pre)).take width)=((Q.pb.drop (fieldsLen pre)).take width) := by
    change (((headBytes++new.bytes false++newMem).drop (fieldsLen pre)).take width)=
      (((headBytes++old.bytes true++oldMem).drop (fieldsLen pre)).take width)
    simpa only [List.append_assoc] using slice_common_headBytes headBytes (new.bytes false++newMem) (old.bytes true++oldMem) (fieldsLen pre) width (by rw [← hheadBytes]; exact hb)
  rw [hbytes]
  exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
