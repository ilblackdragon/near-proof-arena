import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.FreshPrefix

/-! TAG and HPL constraints derived from the ordinary NodeV3 serializer. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteFreshPrefix : List Expr := (UpsV3.cBytes.drop 15).take 4

theorem byte_fresh_prefix_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (enc : NodeEncoding Q) (hpref : FreshPrefix I Q enc) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteFreshPrefix, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    mul3 (c sHPF) (c kNLF) (sub (c UpsV3.b) (.add (Dsl.k 32) (smul 31 (c ts1)))),
    mul3 (c sHPF) (c kWEX) (sub (c UpsV3.b) (.add (smul 16 (.mul (c ts2) (c ti1))) (smul 31 (.mul (c ts3) (c ti1))))),
    mul3 (c sKEY) (c kWEX) (sub (c UpsV3.b) (Dsl.k 15)),
    mul3 (c sHPF) (c kPT) (c UpsV3.b)] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl <;> apply cast0 <;> ups_ev [hC] <;> cellsimp
  · by_cases hs : (fieldAt Q.shape p).1=2 <;> by_cases hk : Q.kind=8
    · have hb := hpref.nlf_byte hp hs hk
      rw [hb]
      by_cases ht : I.ts=1 <;> simp [ind,ht,Lean.Omega.Int.natCast_ofNat]
    all_goals simp [ind,hs,hk]
  · by_cases hs : (fieldAt Q.shape p).1=2 <;> by_cases hk : Q.kind=9
    · have hb := hpref.wrap_byte hp hs hk
      rw [hb]
      rcases (hpref.wrap hk).1 with ⟨ht,hi⟩ | ⟨ht,hi⟩ | ⟨ht,hi⟩ <;>
        simp [ind,ht,hi,Lean.Omega.Int.natCast_ofNat]
    all_goals simp [ind,hs,hk]
  · by_cases hs : (fieldAt Q.shape p).1=3 <;> by_cases hk : Q.kind=9
    · have hb := hpref.wrap_key hp hs hk
      rw [hb]; simp [Lean.Omega.Int.natCast_ofNat]
    all_goals simp [ind,hs,hk]
  · by_cases hs : (fieldAt Q.shape p).1=2 <;> by_cases hk : Q.kind=11
    · have hb := hpref.pass_byte hp hs hk
      rw [hb]; simp
    all_goals simp [ind,hs,hk]

/-- Fresh HPF/KEY bytes derived from the ordinary nibble strings of new nodes. -/
theorem cByteFreshPrefix_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hpref : ∀ I (hI : I ∈ insts) k (hk : k < nQ I), FreshPrefix I (part I k) (he I hI k hk))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteFreshPrefix := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteFreshPrefix.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_fresh_prefix_q (he _ (inst_mem hi) k hk) (hpref _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render
