import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorDecodedIdentity
open NearSpec NearSpec.Bandwidth

theorem bytes (a b:Bytes) (h:a.map UInt8.toNat=b.map UInt8.toNat):a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at h
      have he:x=y:=UInt8.toNat.inj h.1
      rw [he,ih ys h.2]

theorem state (a b:Bytes) (sa sb:State)
    (hbytes:a.map UInt8.toNat=b.map UInt8.toNat)
    (ha:State.decode a=some sa) (hb:State.decode b=some sb):sa=sb := by
  have he:=bytes a b hbytes
  subst b
  exact Option.some.inj (ha.symm.trans hb)

theorem record (a b:Bytes) (sa sb:State) (ra rb:LinkAllowance) (k:Nat)
    (hbytes:a.map UInt8.toNat=b.map UInt8.toNat)
    (ha:State.decode a=some sa) (hb:State.decode b=some sb)
    (hra:sa.links[k]?=some ra) (hrb:sb.links[k]?=some rb):ra=rb := by
  have he:=state a b sa sb hbytes ha hb
  subst sb
  exact Option.some.inj (hra.symm.trans hrb)
end ZkFormal.NearV3.Candidates.ProcPriorDecodedIdentity
