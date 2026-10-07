import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.ReadBits

/-! TAG and HPL constraints derived from the ordinary NodeV3 serializer. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteReadBits : List Expr := (UpsV3.cBytes.drop 53).take 1 ++ (UpsV3.cBytes.drop 55).take 1

theorem byte_read_bits_q {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hb : SourceBytes Q)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ cByteReadBits, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    mul3 (.add kM (c xcp)) (c sTAG) (sub (c rb) (.add (smul 16 hiE) loE)),
    mul3 (c sHPF) kM (sub (c rb) (.add (smul 16 hiE) loE))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl <;> apply cast0
  · by_cases hs : st=0
    · change _ * ev C D fst lst trn P (sub (c rb) (.add (smul 16 hiE) loE))=0
      rw [read_reconstruct hb (Or.inl hs) hC]; simp
    · ups_ev [hC]; cellsimp; simp [ind,hs]
  · by_cases hs : st=2
    · change _ * ev C D fst lst trn P (sub (c rb) (.add (smul 16 hiE) loE))=0
      rw [read_reconstruct hb (Or.inr hs) hC]; simp
    · ups_ev [hC]; cellsimp; simp [ind,hs]

/-- Bit decomposition of source bytes on both header-read row types. -/
theorem cByteReadBits_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hb : ∀ I ∈ insts, ∀ k, k < nQ I → SourceBytes (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteReadBits := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := by
      rcases List.mem_append.1 he with h | h <;>
        exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteReadBits.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_read_bits_q (hb _ (inst_mem hi) k hk) hC

end UpsGen
end ZkFormal.NearV3.Render
