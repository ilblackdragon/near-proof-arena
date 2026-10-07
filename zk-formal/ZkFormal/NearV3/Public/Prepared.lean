import ZkFormal.NearV3.Public.Header
import ZkFormal.NearV3.Public.Body
import ZkFormal.NearV3.Public.Boundary
import ZkFormal.NearV3.Public.NatRecords
import ZkFormal.NearV3.Sched.Pub.Raw

/-! Concrete candidate-side packed prepared statement. These definitions do not
change the frozen NEAR relation or install a native verifier. Width/byte bounds,
root consistency, and witness overhead must be discharged by assembly. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 NearSpecV3

def plainPlan (bus : Nat) (send : Bool) (width : Nat) : PubSeg :=
  { bus, send, width, countAt := 0, start := 0 }

/-- Nine fixed descriptors; counts and offsets are read from the metadata header. -/
def plans : List PubSeg :=
  [sourcePlan, boundaryPlan, bodyPlan,
   plainPlan Sched.B_SPUBB true 7, plainPlan Sched.B_SPAR true 11,
   plainPlan Sched.B_SDL true 5, plainPlan Sched.B_SDL false 5,
   plainPlan B_ROOT true 33, plainPlan B_ROOT false 33]

def schedulerRecords (p : Prep) : Sched.PubRecs := Sched.render (p.sched.map Sched.instOf) p.fwd

def rootPayload (tau : Nat) (root : ByteString) : Payload := [[UInt8.ofNat tau] ++ root]

def preparedBlocks (p : Prep) : List Payload :=
  [sourcePayload p.lists, boundaryPayload p.bnds, bodyPayload p.body,
   natPayload (schedulerRecords p).pubb, natPayload (schedulerRecords p).par,
   natPayload (schedulerRecords p).dlSend, natPayload (schedulerRecords p).dlRecv,
   rootPayload 0 p.hdr.prevStateRoot, rootPayload (p.hdr.K+1) p.hdr.postStateRoot]

def preparedBytes (p : Prep) (witnessOverhead : Nat) : ByteString :=
  encode (headerBytes p witnessOverhead) (preparedBlocks p)

/-- Static segment header locations, independent of the prepared statement. -/
def preparedSegments : List PubSeg :=
  (List.range plans.length).map (fun i => descriptor (plans.getD i sourcePlan) 202 i)

theorem preparedBlocks_length (p : Prep) : (preparedBlocks p).length = 9 := rfl

theorem preparedSegments_length : preparedSegments.length = 9 := by
  simp only [preparedSegments,List.length_map,List.length_range]; rfl

theorem prepared_dataStart (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p) :
    dataStart (headerBytes p witnessOverhead) (preparedBlocks p) = 274 := by
  unfold dataStart
  rw [headerBytes_length p witnessOverhead hr,preparedBlocks_length]

/-- The actual root bytes are retained; the instance number is representable as
one byte under the D0 instance cap. -/
theorem rootPayload_record (tau : Nat) (root : ByteString) (ht : tau < 256)
    (bus : Nat) (send : Bool) :
    recordValues (plainPlan bus send 33) 0 ((rootPayload tau root).getD 0 []) =
      [ZkFormal.Algebra.Fp.ofNat tau] ++ root.map byteF := by
  simp only [recordValues,plainPlan,rootPayload,List.getD_cons_zero,List.map_nil,
    List.nil_append,List.map_append,List.map_cons]
  rw [byteF_ofNat tau ht]

end ZkFormal.NearV3.Public
