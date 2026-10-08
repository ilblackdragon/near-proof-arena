import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestPhysical
import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueMessages
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def preSlotDigests (s : NodeS3) : List ZkFormal.Near.Msg :=
  match s.v.value with
  | some (i,l,pre,_,_)=>[digMsg (msgId K_VPRE i) l pre]
  | none=>[]
def postSlotDigests (s : NodeS3) : List ZkFormal.Near.Msg :=
  match s.v.value with
  | some (i,l,_,post,w)=>if w then [digMsg (msgId K_VPOST i) l post] else []
  | none=>[]

theorem slot_digest_split (s : NodeS3) : slotDigests s=preSlotDigests s++postSlotDigests s := by
  unfold slotDigests preSlotDigests postSlotDigests
  cases s.v.value <;> rfl

theorem update_preSlot (u : Inputs) (s : NodeS3) : preSlotDigests (record u s)=preSlotDigests s := by
  rcases s with ⟨v,tau,depth,res,uses,ubm,dup,hd,repE,ucid,mU⟩
  cases v with
  | leaf k sl m=>cases sl with
    | ref l h=>rfl
    | val l i n pre po w=>cases hu:u.value i <;> simp only [preSlotDigests,record,node,Option.map_some,slot,hu] <;> rfl
  | ext k kd m=>rfl
  | branch sv cs m=>cases sv with
    | none=>rfl
    | some sl=>cases sl with
      | ref l h=>rfl
      | val l i n pre po w=>cases hu:u.value i <;> simp only [preSlotDigests,record,node,Option.map_some,slot,hu] <;> rfl

def valueDigestFrom : Nat→List Bytes→List ZkFormal.Near.Msg
  | _,[]=>[]
  | i,b::bs=>digMsg (msgId K_VPRE i) b.length ((sha256 b).map UInt8.toNat)::valueDigestFrom (i+1) bs

theorem valueDigestFrom_append (i : Nat) (bs cs : List Bytes) :
    valueDigestFrom i (bs++cs)=valueDigestFrom i bs++valueDigestFrom (i+bs.length) cs := by
  induction bs generalizing i with
  | nil=>simp [valueDigestFrom]
  | cons b bs ih=>simp [valueDigestFrom,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem seed_preSlot (t : PTrie) (tau d n v : Nat) :
    preSlotDigests (seedNodeView tau d n v t)=valueDigestFrom v (ownVals t) := by
  cases t with
  | hash h=>rfl
  | leaf k sl m=>cases sl <;> rfl
  | ext k c m=>rfl
  | branch sv cs m=>cases sv with
    | none=>rfl
    | some sl=>cases sl <;> rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
