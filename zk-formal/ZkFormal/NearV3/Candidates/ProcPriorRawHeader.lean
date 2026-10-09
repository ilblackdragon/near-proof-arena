import ZkFormal.NearV3.Candidates.ProcPriorRawChecks
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHeader
open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.Bandwidth

theorem header_byte (st : State) (g : Nat) (hg:g<5) :
    st.encode.getD g 0=if g=0 then 0 else UInt8.ofNat (st.links.length/256^(g-1)) := by
  have h:g=0 ∨ g=1 ∨ g=2 ∨ g=3 ∨ g=4:=by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  all_goals simp [State.encode,u32,leN,List.getD]
  all_goals apply UInt8.toNat_inj.mp
  all_goals simp only [UInt8.toNat_ofNat']
  all_goals omega

theorem header_last (st : State) (hn:st.links.length<16777216) :
    st.encode.getD 4 0=0 ∧ st.links.length/256^3=0 := by
  have hn':st.links.length/256^3=0:=by omega
  rw [header_byte st 4 (by decide +kernel)]
  simp [hn']

theorem header_acc (st : State) (g : Nat) (hg:1≤g ∧ g<4) :
    st.links.length/256^(g-1)=(st.encode.getD g 0).toNat+256*(st.links.length/256^g) := by
  rw [header_byte st g (by omega),ite_eq_right (by omega)]
  simp only [UInt8.toNat_ofNat']
  have h:g=1 ∨ g=2 ∨ g=3:=by omega
  rcases h with rfl|rfl|rfl <;> simp
  all_goals omega

theorem header_acc_field (st : State) (g : Nat) (hg:1≤g ∧ g<4) :
    Fp.ofNat (st.links.length/256^(g-1))=
      Fp.ofNat (st.encode.getD g 0).toNat+(256:Fp)*Fp.ofNat (st.links.length/256^g) := by
  have h:=congrArg Fp.ofNat (header_acc st g hg)
  change (↑(st.links.length/256^(g-1)):Fp)=↑((st.encode.getD g 0).toNat)+256*↑(st.links.length/256^g)
  change (↑(st.links.length/256^(g-1)):Fp)=↑((st.encode.getD g 0).toNat+256*(st.links.length/256^g)) at h
  grind

end ZkFormal.NearV3.Candidates.ProcPriorRawHeader
