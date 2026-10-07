import ZkFormal.NearV3.Rcpt.Extract.V.RclViewProof

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The concrete header-byte values are canonical field representatives. -/
theorem ListBlock.view_header_canon (tr : Trace Fp) (tt : Nat) (B : ListBlock) :
    (B.view tr tt).n0<P ∧ (B.view tr tt).n1<P := by
  exact ⟨Fp.toNat_lt _,Fp.toNat_lt _⟩

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- The unchanged view's nj field equation holds without any extra byte-range assumption. -/
theorem ListBlockWf.view_nj {B : ListBlock} (h : ListBlockWf tr tt B) :
    Fp.ofNat ((B.view tr tt).n0+256*(B.view tr tt).n1)=Fp.ofNat (B.view tr tt).rs.length := by
  change (((B.view tr tt).n0+256*(B.view tr tt).n1 : Nat) : Fp)=((B.view tr tt).rs.length : Fp)
  rw [B.view_length,natCast_add,natCast_mul]
  have h0 : (((B.view tr tt).n0 : Nat) : Fp)=tr.cell tt B.start (reg 8) := Fp.ofNat_toNat _
  have h1 : (((B.view tr tt).n1 : Nat) : Fp)=tr.cell tt B.start (reg 9) := Fp.ofNat_toNat _
  rw [h0,h1]
  exact (h.count_registers hL).1.symm

/-- Three complete table-view fields: nonemptiness, count-header equations, header canonicity. -/
theorem ListChain.view_header_facts {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    bs.map (ListBlock.view tr tt)≠[] ∧
    (∀ L∈bs.map (ListBlock.view tr tt), Fp.ofNat (L.n0+256*L.n1)=Fp.ofNat L.rs.length) ∧
    (∀ L∈bs.map (ListBlock.view tr tt), L.n0<P ∧ L.n1<P) := by
  refine ⟨?_,?_,?_⟩
  · simpa using h.nonempty
  · intro L hLmem
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hLmem
    exact (h.blocks B hB).view_nj hL
  · intro L hLmem
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hLmem
    exact B.view_header_canon tr tt

end ZkFormal.NearV3.RcptV3Proof
