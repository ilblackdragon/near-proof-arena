import ZkFormal.NearV3.Render.Ups.CodecRelayValue
import ZkFormal.Near.Link.ShaCore
namespace ZkFormal.NearV3.Render.UpsRelay
open NearSpec Assembly ZkFormal.Near ZkFormal.Algebra UpsGen

def relayValueMsgs (tau : Nat) (bs : Bytes) : List Msg :=
  (List.range bs.length).map fun p=>[upsertJobId tau 0,p,(bs.map UInt8.toNat).getD p 0]

def relayInventory (taus : List Nat) (values : Nat→Bytes)
    (nodes : List ZkFormal.Sha.Gen.Msg) (others : List Msg) : List Msg :=
  taus.flatMap (fun tau=>relayValueMsgs tau (values tau))++nodes.flatMap shaByteMsgs++others

private theorem id_lt {tau j : Nat} (ht : tau<32) (hj : j<512) : upsertJobId tau j<P := by
  have := upsertJobId_bound ht hj
  have : 262144<P := by decide
  omega

/-- A fresh digest is fixed by the actual codec values and disjoint positive-index
output jobs. Only global SHA balance and the DIGEST lookup remain bus hypotheses;
no fresh digest or per-byte AIR equation is assumed. -/
theorem relay_fresh_digest {shaS shaR : Nat→List Fp→Nat}
    (hsha : ShaFacts shaS shaR) (taus : List Nat) (values : Nat→Bytes)
    (nodes : List ZkFormal.Sha.Gen.Msg) (others : List Msg)
    (htaus : ∀tau∈taus,tau<32)
    (hnodes : ∀M∈nodes,∃tau j,tau<32 ∧ 1≤j ∧ j<512 ∧ M.id=upsertJobId tau j)
    (hothers : ∀m∈others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS)
    (hbytes : ∀m,shaR B_BYTES m=cnt (relayInventory taus values nodes others) m)
    {tau : Nat} (ht : tau<32) (hlen : (values tau).length<2^24)
    {digest : List Nat} (hd : ∀b∈digest,b<P)
    (hrecv : 0<shaS B_DIGEST (digMsg (upsertJobId tau 0) (values tau).length digest).toFp) :
    digest=(sha256 (values tau)).map UInt8.toNat := by
  let enc := (values tau).map UInt8.toNat
  have hencL : enc.length=(values tau).length := by simp [enc]
  have hid:=id_lt ht (by decide : 0<512)
  have hp : 2^24<P := by decide
  have hb : ∀b∈enc,b<P := by
    intro b hb
    obtain ⟨x,_,rfl⟩:=List.mem_map.mp hb
    have := x.toNat_lt
    omega
  have hs : ∀m∈relayInventory taus values nodes others,∀a,m.head?=some a →
      Fp.ofNat a=Fp.ofNat (upsertJobId tau 0) →
      ∃j,j<enc.length ∧ m=[upsertJobId tau 0,j,enc.getD j 0] := by
    intro m hm a ha he
    simp only [relayInventory,List.mem_append] at hm
    rcases hm with (hm|hm)|hm
    · obtain ⟨tau',htau',hm⟩:=List.mem_flatMap.mp hm
      obtain ⟨p,hp',rfl⟩:=List.mem_map.mp hm
      simp only [List.head?_cons,Option.some.injEq] at ha
      subst a
      have he':=Link.ofNat_inj (id_lt (htaus tau' htau') (by decide)) hid he
      have ht':=(upsertJobId_injective (by decide : 0<512) (by decide : 0<512) he').1
      subst tau'
      exact ⟨p,by simpa [hencL] using List.mem_range.mp hp',rfl⟩
    · obtain ⟨M,hM,hm⟩:=List.mem_flatMap.mp hm
      obtain ⟨p,_,rfl⟩:=List.mem_map.mp hm
      simp only [List.head?_cons,Option.some.injEq] at ha
      subst a
      obtain ⟨tau',j,ht',hj,hj',hid'⟩:=hnodes M hM
      rw [hid',Nat.mod_eq_of_lt (id_lt ht' hj')] at he
      have he':=Link.ofNat_inj (id_lt ht' hj') hid he
      have hj0:=(upsertJobId_injective hj' (by decide : 0<512) he').2
      omega
    · obtain ⟨hbound,hkind⟩:=hothers m hm a ha
      have he':=Link.ofNat_inj hbound hid he
      rw [he',upsertJobId_kind] at hkind
      exact False.elim (hkind rfl)
  have hc:=Link.sha_core hsha _ hbytes hid hb (by rw [hencL]; omega) hd hs
    (by simpa only [hencL] using hrecv)
  rw [hc.2]
  simp only [enc,toBytes,List.map_map]
  congr 2
  conv => rhs; rw [←List.map_id (values tau)]
  apply List.map_congr_left
  intro x hx
  simp
end ZkFormal.NearV3.Render.UpsRelay
