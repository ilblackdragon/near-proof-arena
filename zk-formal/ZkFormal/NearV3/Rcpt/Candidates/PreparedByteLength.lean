import ZkFormal.NearV3.Assembly.RoutingBoundedPublicFit

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Public

/-- Exact statement byte cost: overhead value changes fixed-width bytes only. -/
theorem prepared_byte_length (p : Prep) (overhead : Nat) (hr : RootsSized p)
    (hs : ∀s∈p.lists,s.root.length=32) :
    (preparedBytes p overhead).length=340+33*p.lists.length+195*p.bnds.length+
      (p.body.length-8)+7*(schedulerRecords p).pubb.length+
      11*(schedulerRecords p).par.length+5*(schedulerRecords p).dlSend.length+
      5*(schedulerRecords p).dlRecv.length := by
  have hsrc:=payload_length (sourcePayload p.lists) sourcePlan.width (sourcePayload_width p.lists hs)
  have hbody:=payload_length (bodyPayload p.body) bodyPlan.width (bodyPayload_width p.body)
  have hp:=payload_length (natPayload (schedulerRecords p).pubb) 7
    (natPayload_width _ 7 (render_pubb_width _ _))
  have hpar:=payload_length (natPayload (schedulerRecords p).par) 11
    (natPayload_width _ 11 (render_par_width _ _))
  have hd:=payload_length (natPayload (schedulerRecords p).dlSend) 5
    (natPayload_width _ 5 (dl_width _ _))
  have he:=payload_length (natPayload (schedulerRecords p).dlRecv) 5
    (natPayload_width _ 5 (dl_width _ _))
  simp only [sourcePayload_length,bodyPayload_length,natPayload,List.length_map] at hsrc hbody hp hpar hd he
  rw [preparedBytes,encode_length,prepared_dataStart p overhead hr]
  simp only [preparedBlocks,dataBytes,
    List.flatMap_cons,List.flatMap_nil,List.length_append,List.length_nil,hsrc,hbody,hp,hpar,hd,he,
    Assembly.RoutingBoundedLayout.boundary_payload_bytes]
  simp only [rootPayload,payloadBytes,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.length_append,List.length_cons,List.length_nil,hr.1,hr.2.1]
  simp only [payloadBytes,natPayload] at hp hpar hd he
  simp only [natPayload]
  simp only [sourcePlan,bodyPlan,Nat.mul_one] at *
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
