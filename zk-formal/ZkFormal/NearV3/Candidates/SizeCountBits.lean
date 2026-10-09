import ZkFormal.NearV3.Candidates.SizeCountReceiver
namespace ZkFormal.NearV3.Candidates.SizeCountBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open SizeCountReceiver Rcpt.Candidates.SizeCount ZkFormal.Near.Dsl

theorem bit_cell (pub : List Fp) (v : SizeV) (ns : Counts) (t r e : Nat) (he : e<24) :
    (trace pub v ns).cell t r (SizeV3.bt e)=Fp.ofNat ((slack pub v ns r/2^e)%2) := by
  change Fp.ofNat (cell pub v ns r (7+e))=_
  simp [cell,count,countTotal,SizeV3.width,show 7+e≠31 by omega,show 7+e≠32 by omega,
    show 7+e<31 by omega]

theorem bool_cols (pub : List Fp) (v : SizeV) (ns : Counts) (t r y : Nat)
    (hy : y∈[SizeV3.act,SizeV3.lb,SizeV3.la]++(List.range 24).map SizeV3.bt) :
    (trace pub v ns).cell t r y=0 ∨ (trace pub v ns).cell t r y=1 := by
  rcases List.mem_append.mp hy with hy|hy
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl|rfl|rfl <;>
      simp [trace,cell,count,countTotal,SizeV3.width,SizeV3.act,SizeV3.lb,SizeV3.la,SizeGen.cell]
    all_goals split <;> simp [SizeRender.ofNat0,SizeRender.ofNat1]
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hy
    rw [bit_cell pub v ns t r e (List.mem_range.mp he)]
    rcases Nat.mod_two_eq_zero_or_one (slack pub v ns r/2^e) with h|h <;>
      rw [h] <;> simp [SizeRender.ofNat0,SizeRender.ofNat1]

theorem bits_value (pub : List Fp) (v : SizeV) (ns : Counts) (t r : Nat) :
    SizeV3.bitsE.eval (trace pub v ns) t r pub=Fp.ofNat (slack pub v ns r) := by
  rw [show SizeV3.bitsE=bits (fun e=>c (SizeV3.bt e)) 0 24 from rfl,
    eval_bits (trace pub v ns) t r pub SizeV3.bt 0 24 (fun e he=>bool_cols pub v ns t r _ (by
      rw [Nat.zero_add]; exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr he)))),
    SizeRender.bitsVal_congr _ (fun e=>(slack pub v ns r/2^e)%2) 24 (fun e he=>by
      simp only [cv,bit_cell pub v ns t r e he,Fp.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (slack pub v ns r/2^e) (by decide : 0<2); unfold ZkFormal.Algebra.P; omega)),
    SizeRender.bitsVal_bits,Nat.mod_eq_of_lt (slack_bound pub v ns r)]
  rfl
end ZkFormal.NearV3.Candidates.SizeCountBits
