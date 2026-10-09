import ZkFormal.NearV3.Render.Ups.MovedPrefix
import ZkFormal.NearV3.Render.Ups.GByteReadBits

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteMovedPrefix : List Expr := (UpsV3.cBytes.drop 14).take 1

theorem byte_moved_prefix_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (enc : NodeEncoding Q) (hm : Q.kind=6 ∨ Q.kind=7 → MovedPrefix I Q enc)
    (hb : SourceBytes Q) (hf : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteMovedPrefix, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [.mul (.mul (c sHPF) kM) (sub (c UpsV3.b) (sum [smul 32 (c qtl),smul 16 (c UpsV3.qodd),.mul (c UpsV3.qodd) loE]))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  subst ex
  apply cast0
  by_cases hs : (fieldAt Q.shape p).1=2
  · by_cases hk : Q.kind=6 ∨ Q.kind=7
    · let m := hm hk
      have he := m.flag_byte hf hk hp hs
      have ho : Q.qodd<2 := by rw [enc.odd]; simp [NodeGen3.oddOf,m.prefixNode]; omega
      have hl : NodeGen.b2n (NodeGen3.isLeaf enc.node)=if Q.ty=0 then 1 else 0 := by
        rw [enc.ty]
        cases enc.node with
        | leaf => rfl
        | ext => rfl
        | branch sv => cases sv <;> rfl
      have heq : ev C D fst lst trn P (c UpsV3.b) =
          ev C D fst lst trn P (sum [smul 32 (c qtl),smul 16 (c UpsV3.qodd),.mul (c UpsV3.qodd) loE]) := by
        have hr := read_lo hb (Or.inr hs) hC (fst:=fst) (lst:=lst) (trn:=trn) (P:=P) (D:=D)
        change C 101 = 32 * C 70 + (16 * C 75 + (C 75 * ev C D fst lst trn P loE + 0))
        rw [hr]
        rw [hC 101 (by decide),hC 70 (by decide),hC 75 (by decide)]
        cellsimp
        rw [hs]
        unfold rbV
        rw [hl] at he
        rcases (show Q.qodd=0 ∨ Q.qodd=1 by omega) with ho | ho <;>
          by_cases ht : Q.ty=0 <;> simp [ho,ht,ind] at he ⊢ <;> omega
      change _ * (ev C D fst lst trn P (c UpsV3.b) + -ev C D fst lst trn P (sum [smul 32 (c qtl),smul 16 (c UpsV3.qodd),.mul (c UpsV3.qodd) loE]))=0
      exact gate_sub_eq heq
    · simp only [not_or] at hk
      ups_ev [hC]; cellsimp; simp [ind,hk.1,hk.2]
  · ups_ev [hC]; cellsimp; simp [ind,hs]

theorem cByteMovedPrefix_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hm : ∀ I (hI : I ∈ insts) k (hk : k < nQ I),
      (part I k).kind=6 ∨ (part I k).kind=7 → MovedPrefix I (part I k) (he I hI k hk))
    (hb : ∀ I ∈ insts, ∀ k, k < nQ I → SourceBytes (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteMovedPrefix := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteMovedPrefix.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_moved_prefix_q (he _ (inst_mem hi) k hk) (hm _ (inst_mem hi) k hk)
      (hb _ (inst_mem hi) k hk) (hf _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render
