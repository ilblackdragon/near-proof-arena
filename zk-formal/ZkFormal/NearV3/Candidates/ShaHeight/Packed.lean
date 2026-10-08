import ZkFormal.NearV3.Candidates.ShaHeight.Traffic
import ZkFormal.NearV3.Candidates.ShaPackingEncode
import ZkFormal.NearV3.Assembly.ShaBinRender
namespace ZkFormal.NearV3.Candidates.ShaHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha ZkFormal.NearV3.Assembly

/-- Honest actual width-512 SHA renderer at the fusion clock. -/
def packedTrace (msgs : List Gen.Msg) : Trace Fp :=
  ShaPackingEncode.encodeTrace (fixedTrace msgs 22)

theorem packed_log (msgs : List Gen.Msg) (t : Nat) : (packedTrace msgs).log t=22 := rfl

theorem packed_local (msgs : List Gen.Msg) (hok : MsgsOk msgs) (t bb bd : Nat) (pub : List Fp) :
    TableLocal (ShaCarryKinds.table bb bd) (packedTrace msgs) t pub :=
  ShaPackingEncode.encode_local (fixed_local msgs hok 22 t pub bb bd ⟨by decide,by decide⟩ hok.rows)

theorem packed_count (msgs : List Gen.Msg) (hok : MsgsOk msgs) (t bb bd : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (ShaCarryKinds.table bb bd).interactions (packedTrace msgs) t pub bus send msg=
      tableBusCount (Sha.Table.interactions bb bd) (honestTrace msgs) t pub bus send msg := by
  rw [show packedTrace msgs=ShaPackingEncode.encodeTrace (fixedTrace msgs 22) from rfl,
    ShaPackingEncode.encode_traffic (fixed_local msgs hok 22 t pub bb bd ⟨by decide,by decide⟩ hok.rows)]
  exact fixed_count msgs 22 t pub bb bd bus send msg hok.rows

theorem packed_traffic (msgs : List Gen.Msg) (hok : MsgsOk msgs) (t : Nat) (pub : List Fp) :
    TableTraffic (ShaCarryKinds.table B_BYTES B_DIGEST).interactions (packedTrace msgs) t pub
      (shaBinTraffic msgs) := by
  have hold : TableTraffic (Sha.Table.interactions B_BYTES B_DIGEST) (honestTrace msgs) t pub
      (shaBinTraffic msgs) := shaBin_traffic [msgs] 0 pub hok
  intro b m
  rw [packed_count msgs hok,packed_count msgs hok]
  exact hold b m
end ZkFormal.NearV3.Candidates.ShaHeight
