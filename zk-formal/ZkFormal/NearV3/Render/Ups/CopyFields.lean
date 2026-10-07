import ZkFormal.NearV3.Render.Ups.FieldDecompose
import ZkFormal.NearV3.Render.Ups.ByteFlags

/-! Whole-field preservation for the semantic update constructor. These are explicit
list-level edit obligations, not row-wise AIR equalities. The constructor must show that
each inherited serialized field comes from the source slice specified by its edit, with
RBI's two-byte bitmap being the insertion of one previously absent child slot. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- Source field start under the ordinary serialized edit's insertions/removals. -/
def sourceFieldStart (I : UpsInst) (Q : UpsPartI) (st wi start : Nat) : Int :=
  if Q.kind=4 then (start : Int)-36
  else if Q.kind=5 then (start : Int)-32*(if st=7 ∧ wi≠0 ∧ I.ts=1 then 1 else 0)
  else if Q.kind=6 ∨ Q.kind=7 then (start : Int)+Q.phk-Q.qhk
  else if Q.kind=10 then (if st=7 then (Q.pb.length : Int)-40 else (Q.pb.length : Int)-45+start)
  else start

/-- The bitmap insertion is an ordinary 16-bit set operation with the old bit clear. -/
inductive FieldPayloadEdit : Bool → Nat → List Nat → List Nat → Prop
  | preserve (x bytes) : FieldPayloadEdit false x bytes bytes
  | insert (x old : Nat) (hx : x<16) (ho : old<65536) (clear : old / 2^x % 2=0) :
      FieldPayloadEdit true x [old%256,old/256] [(old+2^x)%256,(old+2^x)/256]

/-- Inherited fields of the actual output node preserve a complete source field payload.
Fresh fields carry no obligation here. Valid starts are ordinary source-slice addresses.
The new-leaf case has no inherited fields. -/
structure CopyFields (I : UpsInst) (Q : UpsPartI) : Prop where
  fields : ∀ (pre post : List (Nat × Nat)) (st width : Nat),
    Q.shape=pre++(st,width)::post → CpB I Q st (nWin pre)=true →
    Q.kind≠8 ∧ 0≤sourceFieldStart I Q st (nWin pre) (fieldsLen pre) ∧
    FieldPayloadEdit (Q.kind==5 && st==6) (if I.ts=1 then 0 else 15)
      ((Q.pb.drop (sourceFieldStart I Q st (nWin pre) (fieldsLen pre)).toNat).take width)
      ((Q.q.drop (fieldsLen pre)).take width)

end ZkFormal.NearV3.Render.UpsGen
