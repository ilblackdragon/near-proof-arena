import ZkFormal.NearV3.Sched.View.CodecEnc
import ZkFormal.Size.Model
import ZkFormal.NearV3.Render.Ups.AllocatedRowCost

/-! Isolated capacity-repair candidate. Active tables and protocol admission are
unchanged. This replaces the codec's fresh-state SPOST send by its SHA BYTES send;
removing the corresponding UPS value rows still requires a separate AIR proof. -/
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open ZkFormal.NearV3.Sched

/-- Same byte and position, with the actual fresh scheduler SHA identifier. -/
def relay : Interaction :=
  { bus := B_BYTES, mult := [Codec.encG], send := true,
    msg := [mid 12 (smul 512 (c Codec.tau)),c Codec.pos,c Codec.bpost] }

def codecTable : ZkFormal.Air.Table := { Codec.table with interactions := Codec.interactions.set 1 relay }

def relayMsg (m : List Fp) : List Fp :=
  [Fp.ofNat 12+Fp.ofNat 16*(Fp.ofNat 512*m.getD 0 0),m.getD 1 0,m.getD 2 0]

theorem relay_gate (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    relay.multNat tr t r pub=(Codec.interactions[1]!).multNat tr t r pub := rfl

theorem relay_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    relay.msgVal tr t r pub=relayMsg ((Codec.interactions[1]!).msgVal tr t r pub) := rfl

/-- The relay sends the byte to exactly the scheduler SHA job identifier. -/
theorem relayMsg_native (tau pos byte : Nat) :
    relayMsg ([tau,pos,byte].map Fp.ofNat)=
      [ZkFormal.NearV3.Assembly.upsertJobId tau 0,pos,byte].map Fp.ofNat := by
  change [Fp.ofNat 12+Fp.ofNat 16*(Fp.ofNat 512*Fp.ofNat tau),Fp.ofNat pos,Fp.ofNat byte]=_
  rw [ofNat_mul',ofNat_mul',ofNat_add']
  rfl

/-- The candidate preserves each actual encoding-row multiplicity and redirects
its authenticated SPOST byte to the matching fresh-value SHA job. -/
theorem relay_native_message (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    {tau pos byte : Nat}
    (hm : (Codec.interactions[1]!).msgVal tr t r pub=[tau,pos,byte].map Fp.ofNat) :
    relay.msgVal tr t r pub=
      [ZkFormal.NearV3.Assembly.upsertJobId tau 0,pos,byte].map Fp.ofNat := by
  rw [relay_message,hm,relayMsg_native]

theorem codec_constraints : codecTable.constraints=Codec.table.constraints := rfl
theorem codec_width : codecTable.width=Codec.table.width := rfl
theorem codec_log : codecTable.maxLog=22 := rfl

set_option maxHeartbeats 2000000 in
/-- Same commitment widths, aux groups, quotient columns and maxLog. -/
theorem codec_shape : ZkFormal.Size.shapeOf 2 codecTable=ZkFormal.Size.shapeOf 2 Codec.table := by
  decide +kernel

/-- Removing redundant fresh-value rows suffices under the already proved
accepted output-byte budget. This is arithmetic, not candidate AIR completeness. -/
theorem compact_rows_fit {instances outputBytes : Nat}
    (hi : instances≤32) (ho : outputBytes≤2131072) :
    4*instances+outputBytes+1≤2^22 := by omega

/-- A full duplicate UPS table can also partition ≤32 instances at 16 each,
but incurs another wide table in the proof. -/
theorem half_rows_fit {instances valueBytes outputBytes : Nat}
    (hi : instances≤16) (hv : valueBytes≤98341*instances) (ho : outputBytes≤2131072) :
    4*instances+valueBytes+outputBytes+1≤2^22 := by omega

/-- Raising maxLog is not an admissible repair under the unchanged protocol. -/
theorem log23_rejected (A : Air) (maxDeg : Nat) (T : ZkFormal.Air.Table) (h : T.maxLog=23) :
    T.wf A maxDeg=false := by simp [ZkFormal.Air.Table.wf,h]
end ZkFormal.NearV3.Render.UpsRelay
