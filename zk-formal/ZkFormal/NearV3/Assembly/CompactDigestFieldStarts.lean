import ZkFormal.NearV3.Assembly.PhysicalFieldStarts

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- Concrete request at a known field start, preserving its byte position and
child-window ordinal. -/
def fieldDigestMsgs (I : Render.UpsInst) (k pos st wi : Nat) : List Msg :=
  let Q:=part I k
  if WinFrB I Q st wi=true then
    [digMsg ((dIV I Q st 0 wi k : Fp).toNat) ((dLV I Q st 0 wi : Fp).toNat)
      ((List.range 32).map fun i=>(Fp.ofNat (Q.q.getD (pos+i) 0)).toNat)] else []

theorem nodeDigestMsgs_start (I : Render.UpsInst) (k pos : Nat) :
    nodeDigestMsgs I k pos=
      let a:=fieldAt (part I k).shape pos
      if a.2.1=0 then fieldDigestMsgs I k pos a.1 a.2.2.2 else [] := by
  dsimp only [nodeDigestMsgs,fieldDigestMsgs]
  by_cases hz:(fieldAt (part I k).shape pos).2.1=0
  · simp only [hz,GdB,beq_self_eq_true,Bool.true_and,ite_true]
  · simp only [GdB,show ((fieldAt (part I k).shape pos).2.1==0)=false from beq_eq_false_iff_ne.mpr hz,
      Bool.false_and,Bool.false_eq_true,ite_false,hz]

/-- Actual physical node bytes collapse to field starts with exact multiplicity
and offsets, using the checked field-size equality of this same part. -/
theorem node_digest_field_starts (I : Render.UpsInst) (k : Nat) (hf : FieldsOk (part I k)) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      fieldStarts (fieldDigestMsgs I k) (part I k).shape 0 0 := by
  rw [hf.bytes]
  rw [←field_start_scan (fieldDigestMsgs I k) (part I k).shape 0 0]
  apply congrArg (fun f=>(List.range (fieldBytes (part I k).shape)).flatMap f)
  funext pos
  rw [nodeDigestMsgs_start]
  simp only [Nat.zero_add]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
