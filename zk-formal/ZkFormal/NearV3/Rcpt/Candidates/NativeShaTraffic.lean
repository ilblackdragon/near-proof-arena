import ZkFormal.NearV3.Rcpt.Candidates.NativeShaJobs

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

/-- Byte messages of whole SHA preimages, retaining job order. -/
def jobBytes (ms : List Render.Msg) : List Msg :=
  ms.flatMap (fun m => emitAt m.id 0 m.bytes)

theorem nodeJobs_bytes_from (n : Nat) (ns : List NodeS3) :
    jobBytes (nativeNodeShaJobsFrom n ns)=
      (ns.zipIdx n).flatMap (fun p => emitAt (msgId K_NPRE p.2) 0 (p.1.v.ser false)++
        emitAt (msgId K_NPOST p.2) 0 (p.1.v.ser true)) := by
  induction ns generalizing n with
  | nil => simp [nativeNodeShaJobsFrom,jobBytes]
  | cons s ss ih => simp [nativeNodeShaJobsFrom,jobBytes,List.zipIdx_cons,←ih,List.append_assoc]

theorem nodeJobs_bytes (ns : List NodeS3) :
    jobBytes (nativeNodeShaJobsFrom 0 ns)=nodeSends3 ns B_BYTES := by
  rw [nodeJobs_bytes_from,List.zipIdx_eq_zip_range']
  simp [nodeSends3,List.range_eq_range']

theorem valueJobs_bytes (vs : List ValE) (h : ValWf vs) :
    jobBytes (nativeValueShaJobs vs)=valSends vs B_BYTES := by
  have aux : ∀es : List ValE,
      (∀e∈es,(e.vz=true → e.len=0 ∧ e.bytes=[]) ∧
        (e.vz=false → e.bytes.length=e.len ∧ 0<e.len)) →
      jobBytes (nativeValueShaJobs es)=es.flatMap (fun e => if e.vz then [] else emitAt (eidV e) 0 e.bytes) := by
    intro es hs
    induction es with
    | nil => simp [nativeValueShaJobs,jobBytes]
    | cons e es ih =>
      have he := hs e (by simp)
      have ht := ih (fun e he => hs e (by simp [he]))
      cases hz : e.vz
      · have hb : e.bytes≠[] := by
          have hh := he.2 hz
          intro hh'
          simp only [hh',List.length_nil] at hh
          omega
        simpa [nativeValueShaJobs,hb,jobBytes,hz,eidV] using ht
      · have hb := (he.1 hz).2
        simpa [nativeValueShaJobs,hb,jobBytes,hz] using ht
  simpa [valSends] using aux vs h.shape

theorem nativeJobs_bytes (ns : List NodeS3) (vs : List ValE) (h : ValWf vs) :
    jobBytes (nativeShaJobs ns vs)=nodeSends3 ns B_BYTES++valSends vs B_BYTES := by
  change jobBytes (nativeNodeShaJobsFrom 0 ns++nativeValueShaJobs vs)=_
  simp only [jobBytes,List.flatMap_append]
  rw [show (nativeNodeShaJobsFrom 0 ns).flatMap (fun m => emitAt m.id 0 m.bytes)=_ from nodeJobs_bytes ns,
    show (nativeValueShaJobs vs).flatMap (fun m => emitAt m.id 0 m.bytes)=_ from valueJobs_bytes vs h]

end ZkFormal.NearV3.Rcpt.Candidates
