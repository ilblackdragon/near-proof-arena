import ZkFormal.NearV3.Render.Ups.GByteWindows
import ZkFormal.NearV3.Render.Ups.ByteFlags

/-! Copy and source-read flags, the first ten update-byte constraints. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteFlags : List Expr := UpsV3.cBytes.take 10

def extraReadE : Expr := Dsl.sum [
  .mul (c sTAG) (sumc [kRBV,kMVL,kMVE,xcp]),
  mul3 (c sHPL) (c fs) kM,.mul (c sHPF) kM,.mul (c sVLEN) (c kRBR),
  mul3 (c sBM) (c fs) (c xcp),.mul (c sMEM) (Dsl.not (c kNLF)),c rdc]

theorem byte_flags_q {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hk : Q.kind < 12) (hs : st < 9)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ cByteFlags, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    .mul (Dsl.not (c qb)) (c cp),.mul (Dsl.not (c qb)) (c rd),
    .mul (c sTAG) (sub (c cp) (sumc [kRDB,kRDE,kRLP,kRBR,kRBI,kPT])),
    .mul (.add (c sHPL) (c sHPF)) (sub (c cp) (sumc [kRDE,kRLP,kPT])),
    .mul (c sKEY) (sub (c cp) (sumc [kRDE,kRLP,kMVL,kMVE])),
    .mul (.add (c sVLEN) (c sVH)) (sub (c cp) (c vcp)),
    .mul (c sBM) (sub (c cp) (sumc [kRDB,kRBR,kRBV,kRBI])),
    .mul (c sCH) (sub (c cp) (Dsl.not (c wfr))),
    .mul (c sMEM) (c cp),
    .mul (c qb) (sub (c rd) (.add (c cp) extraReadE))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply cast0 <;> ups_ev [hC,extraReadE] <;> cellsimp
  · change (0 : Int) * cpV I Q st wi = 0; rw [Int.zero_mul]
  · change (0 : Int) * rdV I Q st ix wi = 0; rw [Int.zero_mul]
  · by_cases ht : st=0
    · subst st; exact gate_sub_eq (copy_tag I Q wi hk)
    · simp [ind,ht]
  · by_cases ht : st=1 ∨ st=2
    · exact gate_sub_eq (copy_prefix I Q st wi hk ht)
    · simp only [not_or] at ht; simp [ind,ht.1,ht.2]
  · by_cases ht : st=3
    · subst st; exact gate_sub_eq (copy_key I Q wi hk)
    · simp [ind,ht]
  · by_cases ht : st=4 ∨ st=5
    · exact gate_sub_eq (copy_value I Q st wi hk ht)
    · simp only [not_or] at ht; simp [ind,ht.1,ht.2]
  · by_cases ht : st=6
    · subst st; exact gate_sub_eq (copy_bitmap I Q wi hk)
    · simp [ind,ht]
  · by_cases ht : st=7
    · subst st; exact gate_sub_eq (copy_child I Q wi)
    · simp [ind,ht]
  · by_cases ht : st=8
    · subst st; rw [copy_mem]; rfl
    · simp [ind,ht]
  · apply Int.sub_eq_zero.mpr
    rw [read_copy_extra I Q st ix wi hk hs]
    apply congrArg (fun z : Int => cpV I Q st wi + z)
    unfold extraSum kin
    simp only [List.map,List.sum_cons,List.sum_nil,Int.add_zero,Int.sub_eq_add_neg,Lean.Omega.Int.natCast_ofNat]
    ac_rfl

/-- The copy/read selectors satisfy their AIR constraints on every generated row. -/
theorem cByteFlags_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hk : ∀ I ∈ insts, ∀ k, k < nQ I → (part I k).kind < 12)
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteFlags := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_take he
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteFlags.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hki hp q _ _ C D P hC _
    exact byte_flags_q (hk _ (inst_mem hi) k hki) ((hf _ (inst_mem hi) k hki).state hp) hC

end UpsGen
end ZkFormal.NearV3.Render
