import ZkFormal.NearV3.Render.Ups.MemConstruct

/-! Bounds on the total signed inside-chain scalar, including every source,
child, fresh-memory, length, and fixed-cost contribution. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

private theorem bytes_pfx_bound (f : Nat → Int) (h : ∀ i,0≤f i ∧ f i<256) :
    0≤pfx f 8 ∧ pfx f 8<256^8 := by
  have h0:=h 0; have h1:=h 1; have h2:=h 2; have h3:=h 3
  have h4:=h 4; have h5:=h 5; have h6:=h 6; have h7:=h 7
  simp only [pfx,Int.reducePow,Int.zero_add,Int.mul_one]
  omega

private theorem byte_get_bound {xs : List Nat} (hb : ∀ b∈xs,b<256) (i : Nat) :
    0≤(xs.getD i 0:Int) ∧ (xs.getD i 0:Int)<256 := by
  have hh : xs.getD i 0<256 := by
    rw [List.getD_eq_getElem?_getD]
    cases he : xs[i]? with
    | none => simp
    | some b => exact hb b (List.mem_of_getElem? he)
  omega

private theorem bit_product_bound {a x bound : Int} (ha : 0≤a ∧ a≤1)
    (hx : 0≤x ∧ x<bound) : 0≤a*x ∧ a*x<bound := by
  rcases (show a=0 ∨ a=1 by omega) with rfl|rfl <;> simp_all <;> omega

theorem memory_total_bound (I : UpsInst) (Q : UpsPartI)
    (hk : Q.kind<12) (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hL : L I<2^24) (hb : ∀ b∈Q.pb,b<256)
    (hchild : ∀ b∈(child I Q).pb,b<256) (hm : Q.mB<2^74) :
    -(131072*256^8)<pfx (X1V I Q) 8 ∧ pfx (X1V I Q) 8<131072*256^8 := by
  obtain ⟨ha,hn,hl,ho,hs,_,_,_,hC⟩ := scalar_metadata_bounds I Q hk hc hq hp
  have hA := bit_product_bound ha (bytes_pfx_bound (memRb Q) (fun i => byte_get_bound hb _))
  have hN := bit_product_bound hn (show 0≤(Q.mB:Int) ∧ (Q.mB:Int)<2^74 by omega)
  have hLv := bit_product_bound hl (show 0≤(L I:Int) ∧ (L I:Int)<2^24 by omega)
  have hO := bit_product_bound ho (bytes_pfx_bound (memByte (child I Q)) (fun i => byte_get_bound hchild _))
  have hS := bit_product_bound hs (bytes_pfx_bound (slb Q) (by
    intro i; unfold slb; split
    · exact byte_get_bound hb _
    · omega))
  rw [memory_subtraction_scalar I Q hL]
  omega

/-- Once ordinary byte serialization and native fresh-memory bounds hold, the
caller supplies only the native modular result equation, not carry or sign facts. -/
theorem construct_memOk_bounded (I : UpsInst) (Q : UpsPartI) (e : NodeEncoding Q)
    (hk : Q.kind<12) (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hL : L I<2^24) (hb : ∀ b∈Q.pb,b<256)
    (hchild : ∀ b∈(child I Q).pb,b<256)
    (hout : ∀ b∈NodeGen3.memOf e.node,b<256) (hm : Q.mB<2^74)
    (hr : (pfx (EinV I Q) 8+(if pfx (X1V I Q) 8<0 then 0 else pfx (X1V I Q) 8))%256^8=
      (le256 (NodeGen3.memOf e.node):Int)) : MemOk I (withMemorySign I Q) := by
  have hs := memory_total_bound I Q hk hc hq hp hL hb hchild hm
  exact construct_memOk I Q e hk hc hq hp hL hb hchild hout hs.1 hs.2 hr
end ZkFormal.NearV3.Render.UpsGen
