import ZkFormal.NearV3.Qv.Extract.WalkRows

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s len : Nat} (hfit : s+len≤tr.height tt)
variable (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
include hL hfit hs

theorem walk_position : ∀ r, s≤r → r<s+len → tr.cell tt r wp=((r-s : Nat):Fp) := by
  have hlen := hs.1
  have hfirst : tr.cell tt s wf=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.1
  have h0 := con hL (show s<tr.height tt by omega) (e:=.mul (c wf) (c wp)) (by simp [constraints])
  simp only [eval_mul,eval_c,hfirst] at h0
  have hstep : ∀ r, s≤r → r+1<s+len → tr.cell tt (r+1) wp=tr.cell tt r wp+1 := by
    intro r hr hn
    have ha : tr.cell tt r walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr (by omega)
    have hl := zero_of_false hL (show r<tr.height tt by omega) (x:=wl) (by simp [walkBools]) (hs.2.2.2.2.2 r hr hn)
    have hh := con hL (r:=r) (by omega) (e:=eqG inside (n wp) (.add (c wp) (k 1))) (by simp [constraints])
    simp only [inside,eval_eqG,eval_mul,eval_not,eval_c,eval_n,eval_add,eval_k,ha,hl,
      Nat.mod_eq_of_lt (show r+1<tr.height tt by omega)] at hh
    grind
  have hz : tr.cell tt s wp=(0:Nat) := by grind
  simpa only [Nat.zero_add] using counter_of (f:=fun r => tr.cell tt r wp) (ℓ:=len) hz hstep

/-- Key segments cannot hide a counter wrap: their physical length is at most
2^22, below the field modulus, so the terminal counter gives length 1 or 9. -/
theorem walk_length : len=1 ∨ len=9 := by
  have hlen := hs.1
  have hl : tr.cell tt (s+len-1) wl=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
  have hr : s+len-1<tr.height tt := by omega
  have hp := walk_position hL hfit hs (s+len-1) (by omega) (by omega)
  have hh := con hL hr (e:=eqG (c wl) (c wp) (smul 8 group)) (by simp [constraints])
  simp only [eval_eqG,eval_c,eval_smul,group,eval_mul,hl,hp] at hh
  have hbound := height_le hL
  have hsmall : s+len-1-s<P := by unfold P; omega
  rcases isBool hL hr (x:=lo) (by simp [walkBools]) with hlo | hlo <;>
    rcases isBool hL hr (x:=hi) (by simp [walkBools]) with hhi | hhi
  all_goals rw [hlo,hhi] at hh
  · have he : ((s+len-1-s:Nat):Fp)=(0:Nat) := by grind
    have := ofNat_inj hsmall (by decide) he
    omega
  · have he : ((s+len-1-s:Nat):Fp)=(0:Nat) := by grind
    have := ofNat_inj hsmall (by decide) he
    omega
  · have he : ((s+len-1-s:Nat):Fp)=(0:Nat) := by grind
    have := ofNat_inj hsmall (by decide) he
    omega
  · have he : ((s+len-1-s:Nat):Fp)=(8:Nat) := by grind
    have := ofNat_inj hsmall (by decide) he
    omega

end ZkFormal.NearV3.Qv.Extract
