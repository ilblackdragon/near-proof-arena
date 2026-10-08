import ZkFormal.NearV3.Candidates.ProcPriorBudget
import ZkFormal.NearV3.Candidates.ProcPriorMemoryTable
namespace ZkFormal.NearV3.Candidates.ProcPriorCanonical
open NearSpec NearSpec.Bandwidth ZkFormal.Algebra ProcPriorEvents ProcPriorDecode

theorem event_ranges (ids : List Nat) (bs : Bytes) (st : Bandwidth.State)
    (hd:Bandwidth.State.decode bs=some st) (hb:bs.length≤2000000) (hn:ids.length≤64)
    (tau : Nat) (ht:tau<33) (e : Event) (he:e∈events ids st.links) :
    e.link<4096 ∧ e.stamp<16777216 ∧ e.lo<16777216 ∧ 4096*tau+e.link<135168 := by
  obtain ⟨hl,hs,hlo⟩:=event_bounds ids st.links e he
  have hn2:ids.length*ids.length≤4096 := Nat.mul_le_mul hn hn
  have hb':=decode_length bs st hd
  omega

theorem packed_injective (t u a b : Nat) (ha:a<4096) (hb:b<4096)
    (h:4096*t+a=4096*u+b) : t=u ∧ a=b := by omega

/-- Field equality identifies the same native instance/link only after the
actual parser and canonical query ranges have been established. -/
theorem packed_field_injective (t u a b : Nat) (ht:t<33) (hu:u<33)
    (ha:a<4096) (hb:b<4096) (h:Fp.ofNat (4096*t+a)=Fp.ofNat (4096*u+b)) : t=u ∧ a=b := by
  have h1:4096*t+a<P := by unfold P; omega
  have h2:4096*u+b<P := by unfold P; omega
  have he:=congrArg Fp.toNat h
  simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2] at he
  exact packed_injective t u a b ha hb he

end ZkFormal.NearV3.Candidates.ProcPriorCanonical
