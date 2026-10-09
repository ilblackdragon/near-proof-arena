import ZkFormal.NearV3.Qv.Extract.WalkLength

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s len : Nat} (hfit : s+len≤tr.height tt)
variable (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
include hL hfit hs

theorem walk_metadata {x : Nat}
    (hx : x∈[lo,hi,slot,Candidates.ValueTable.vid,Candidates.ValueTable.tau,
      Candidates.ValueTable.users,absent,main,lastMain,Candidates.ValueTable.count]) :
    ∀ r, s≤r → r<s+len → tr.cell tt r x=tr.cell tt s x := by
  apply const_of (f:=fun r => tr.cell tt r x)
  intro r hr hn
  have ha : tr.cell tt r walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr (by omega)
  have hl := zero_of_false hL (show r<tr.height tt by omega) (x:=wl) (by simp [walkBools]) (hs.2.2.2.2.2 r hr hn)
  have he : eqG inside (n x) (c x) ∈ constraints := by
    have hm := List.mem_map_of_mem (f:=fun x => eqG inside (n x) (c x)) hx
    exact List.mem_append_right _ hm
  have hh := con hL (r:=r) (by omega) he
  simp only [inside,eval_eqG,eval_mul,eval_not,eval_c,eval_n,ha,hl,
    Nat.mod_eq_of_lt (show r+1<tr.height tt by omega)] at hh
  grind

/-- The first key byte is fixed by the two kind bits, not supplied by a renderer. -/
theorem walk_header : tr.cell tt s wb=7+6*tr.cell tt s lo+3*tr.cell tt s hi := by
  have hlen := hs.1
  have hf : tr.cell tt s wf=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.1
  have hh := con hL (show s<tr.height tt by omega)
    (e:=eqG (c wf) (c wb) (sum [k 7,smul 6 (c lo),smul 3 (c hi)])) (by simp [constraints])
  simp only [eval_eqG,eval_c,eval_sum_cons,eval_sum_nil,eval_k,eval_smul,hf] at hh
  grind

/-- A group key has exactly nine bytes; every other kind has one. -/
theorem walk_kind_length :
    (tr.cell tt s lo=1 ∧ tr.cell tt s hi=1 → len=9) ∧
    (tr.cell tt s lo=0 ∨ tr.cell tt s hi=0 → len=1) := by
  have hlen := hs.1
  have hr : s+len-1<tr.height tt := by omega
  have hl : tr.cell tt (s+len-1) wl=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
  have hp := walk_position hL hfit hs (s+len-1) (by omega) (by omega)
  have hlo := walk_metadata hL hfit hs (x:=lo) (by simp) (s+len-1) (by omega) (by omega)
  have hhi := walk_metadata hL hfit hs (x:=hi) (by simp) (s+len-1) (by omega) (by omega)
  have hh := con hL hr (e:=eqG (c wl) (c wp) (smul 8 group)) (by simp [constraints])
  simp only [eval_eqG,eval_c,eval_smul,group,eval_mul,hl,hp,hlo,hhi] at hh
  have hb := height_le hL
  have hsmall : s+len-1-s<P := by unfold P; omega
  constructor
  · rintro ⟨ha,hb⟩
    rw [ha,hb] at hh
    have he : ((s+len-1-s:Nat):Fp)=(8:Nat) := by grind
    have := ofNat_inj hsmall (by decide) he
    omega
  · intro hz
    have he : ((s+len-1-s:Nat):Fp)=(0:Nat) := by rcases hz with hz | hz <;> rw [hz] at hh <;> grind
    have := ofNat_inj hsmall (by decide) he
    omega

end ZkFormal.NearV3.Qv.Extract
