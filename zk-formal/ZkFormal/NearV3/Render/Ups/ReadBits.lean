import ZkFormal.NearV3.Render.Ups.GByteFlags

/-! Header read registers reconstruct the two nibbles of an ordinary source byte. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def SourceBytes (Q : UpsPartI) : Prop := ∀ b ∈ Q.pb, b < 256

theorem rb_bounds {I : UpsInst} {Q : UpsPartI} (h : SourceBytes Q) (st ix wi p : Nat) :
    0 ≤ rbV I Q st ix wi p ∧ rbV I Q st ix wi p < 256 := by
  unfold rbV
  have hb : Q.pb.getD (sposV I Q st ix wi p).toNat 0 < 256 := by
    rw [List.getD_eq_getElem?_getD]
    cases he : Q.pb[(sposV I Q st ix wi p).toNat]? with
    | none => simp
    | some b => exact h b (List.mem_of_getElem? he)
  omega

theorem nibble_bits (x : Int) (h0 : 0 ≤ x) (h1 : x < 16) :
    x = x % 2 + 2*(x/2%2) + 4*(x/4%2) + 8*(x/8%2) := by omega

section
variable {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
variable (hb : SourceBytes Q) (hs : st=0 ∨ st=2)
variable {C D P : Nat → Int} {fst lst trn : Int}
variable (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x)

include hb hs hC

theorem read_hi : ev C D fst lst trn P hiE = rbV I Q st ix wi p / 16 := by
  have hr := rb_bounds (I:=I) hb st ix wi p
  have hi := nibble_bits (rbV I Q st ix wi p / 16) (by omega) (by omega)
  have hw : winFrV I Q st wi=0 := by rcases hs with rfl | rfl <;> rfl
  ups_ev [hC]
  cellsimp
  simp only [hw,show (0 : Int) ≠ 1 by decide,ite_false,hs,ite_true,
    Nat.reduceEqDiff,Nat.reduceLT,Nat.reduceSub,Int.reducePow,Int.ediv_one,Int.zero_add,Int.one_mul,
    Lean.Omega.Int.natCast_ofNat]
  omega

theorem read_lo : ev C D fst lst trn P loE = rbV I Q st ix wi p % 16 := by
  have hi := nibble_bits (rbV I Q st ix wi p % 16) (by omega) (by omega)
  have hw : winFrV I Q st wi=0 := by rcases hs with rfl | rfl <;> rfl
  ups_ev [hC]
  cellsimp
  simp only [hw,show (0 : Int) ≠ 1 by decide,ite_false,hs,ite_true,
    Nat.reduceEqDiff,Nat.reduceLT,Nat.reduceSub,Int.reducePow,Int.ediv_one,Int.zero_add,Int.one_mul,
    Lean.Omega.Int.natCast_ofNat]
  omega

theorem read_reconstruct :
    ev C D fst lst trn P (sub (c rb) (.add (smul 16 hiE) loE))=0 := by
  change C 103 + -((16 : Nat) * ev C D fst lst trn P hiE + ev C D fst lst trn P loE)=0
  rw [read_hi hb hs hC,read_lo hb hs hC,hC 103 (by decide)]
  cellsimp
  simp only [Lean.Omega.Int.natCast_ofNat]
  omega

end
end UpsGen
end ZkFormal.NearV3.Render
