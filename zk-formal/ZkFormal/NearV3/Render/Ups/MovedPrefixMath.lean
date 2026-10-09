import ZkFormal.NearV3.Render.Node.ByteFacts

/-! The low nibble of the source packed key supplies the first surviving nibble after
removing a nonempty prefix. This is ordinary hex-prefix serialization arithmetic. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

 theorem hpN_drop_head (key : List Nat) (leaf : Bool) (cut : Nat)
    (hk : ∀ x ∈ key, x<16) (hc : 1 ≤ cut) :
    (hpN (key.drop cut) leaf).getD 0 0 =
      32*NodeGen.b2n leaf + 16*((key.drop cut).length%2) +
      ((key.drop cut).length%2) * ((hpN key leaf).getD (key.length/2-(key.drop cut).length/2) 0 % 16) := by
  have hd : ∀ x ∈ key.drop cut, x<16 := by intro x hx; exact hk x (List.mem_of_mem_drop hx)
  rw [NodeLay.hp_head _ _ hd]
  by_cases ho : (key.drop cut).length%2=1
  · have hlen : (key.drop cut).length=key.length-cut := List.length_drop
    have hcut : cut < key.length := by omega
    have hm : 1 ≤ key.length/2-(key.drop cut).length/2 := by omega
    have hr : key.length/2-(key.drop cut).length/2-1 < key.length/2 := by omega
    have hi : 2*(key.length/2-(key.drop cut).length/2-1)+key.length%2+1=cut := by omega
    have hh := NodeLay.hp_tail key leaf hk (key.length/2-(key.drop cut).length/2-1) hr
    rw [show key.length/2-(key.drop cut).length/2-1+1=key.length/2-(key.drop cut).length/2 by omega,hi] at hh
    have hb : key.getD cut 0 < 16 := by
      rw [List.getD_eq_getElem?_getD]
      cases he : key[cut]? with
      | none => simp
      | some b => exact hk b (List.mem_of_getElem? he)
    have he : (key.drop cut).getD 0 0=key.getD cut 0 := by simp [List.getD_eq_getElem?_getD]
    rw [ho,if_pos rfl,hh,he]
    omega
  · have hz : (key.drop cut).length%2=0 := by omega
    rw [hz]
    simp
    omega

end ZkFormal.NearV3.Render.UpsGen
