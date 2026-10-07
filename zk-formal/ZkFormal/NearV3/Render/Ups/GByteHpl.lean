import ZkFormal.NearV3.Render.Ups.GByteSourceHeader
import ZkFormal.NearV3.Render.Ups.HeaderBounds
import ZkFormal.NearV3.Render.Ups.HeaderRegisters

/-! Full HPL accumulators for output headers. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteHpl : List Expr := UpsV3.cBytes.drop 76

/-- Appended header constraints vanish off HPL, independently of the successor row. -/
theorem byte_hpl_off {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hs : st≠1) {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x<200 → C x=QC I Q k p st ix fl wi u x) :
    ∀ ex∈cByteHpl, ((ev C D fst lst trn P ex : Int) : Fp)=0 := by
  intro ex hex
  simp only [cByteHpl,UpsV3.cBytes,List.drop,List.map,List.range_succ,List.range_zero,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl <;> apply cast0 <;>
    ups_ev [hC] <;> cellsimp <;> simp [ind,hs]

theorem byte_hpl_qmid {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (enc : NodeEncoding Q) (hf : FieldsOk Q) (hp : p<Q.q.length) (hp1 : p+1<Q.q.length)
    (hqh : Q.qhk<16777216)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x<200 → C x=QC I Q k p (fieldAt Q.shape p).1
      (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x<200 → D x=QC I Q k (p+1) (fieldAt Q.shape (p+1)).1
      (fieldAt Q.shape (p+1)).2.1 (fieldAt Q.shape (p+1)).2.2.1 (fieldAt Q.shape (p+1)).2.2.2 u' x) :
    ∀ ex∈cByteHpl, ((ev C D fst lst trn P ex : Int) : Fp)=0 := by
  by_cases hs : (fieldAt Q.shape p).1=1
  case neg => exact byte_hpl_off hs hC
  have hl := hf.header_width hp hs
  have hi := (fieldAt_bounds Q.shape p (by rw [← hf.bytes]; exact hp)).1
  have hnext : (fieldAt Q.shape p).2.1+1<4 →
      fieldAt Q.shape (p+1)=((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.1+1,
        (fieldAt Q.shape p).2.2.1,(fieldAt Q.shape p).2.2.2) := by
    intro h; exact fieldAt_next_inside Q.shape p (by omega)
  intro ex hex
  simp only [cByteHpl,UpsV3.cBytes,List.drop,List.map,List.range_succ,List.range_zero,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl <;> apply cast0
  · by_cases he : (fieldAt Q.shape p).2.1+1=4
    · ups_ev [hC]; cellsimp; simp [ind,hs,hl,he]
    · have hn := hnext (by omega)
      have hb := enc.hpl hp1 (by rw [hn]; exact hs)
      rw [hn] at hb
      have ha := NodeGen3.le256_take_succ (u32Bytes Q.qhk) (fieldAt Q.shape p).2.1 (by simp; omega)
      simp only [List.getD_eq_getElem?_getD] at hb ha
      ups_ev [hC,hD]; cellsimp
      simp only [hn,hs,hl] at *
      simp [winFrV,WinFrB,ind,he,ha,hb,Int.natCast_add,Int.natCast_mul,Nat.add_assoc,Int.add_right_neg]
  · by_cases he : (fieldAt Q.shape p).2.1+1=4
    · ups_ev [hC]; cellsimp; simp [ind,hs,hl,he]
    · have hn := hnext (by omega)
      ups_ev [hC,hD]; cellsimp
      simp [hn,hs,hl,winFrV,WinFrB,ind,he,Nat.pow_succ,Int.natCast_mul,Int.mul_comm,Int.add_right_neg]
  · by_cases he : (fieldAt Q.shape p).2.1+1=4
    · have ht : (u32Bytes Q.qhk).take 4 = u32Bytes Q.qhk := List.take_of_length_le (by simp)
      ups_ev [hC]; cellsimp
      simp [hs,hl,he,winFrV,WinFrB,ind,ht,u32Bytes_value (by omega : Q.qhk<4294967296),Int.add_right_neg]
    · ups_ev [hC]; cellsimp; simp [ind,hs,hl,he]
  · by_cases he : (fieldAt Q.shape p).2.1+1=4
    · have hb := enc.hpl hp hs
      rw [show (fieldAt Q.shape p).2.1=3 by omega,u32Bytes_top_zero hqh] at hb
      simp only [List.getD_eq_getElem?_getD] at hb
      ups_ev [hC]; cellsimp; simp [hb]
    · ups_ev [hC]; cellsimp; simp [ind,hs,hl,he]
  · have hb := enc.hpl hp hs
    have hbound : Q.q.getD p 0 < 256 := by
      rw [hb]
      rw [List.getD_eq_getElem?_getD]
      cases he : (u32Bytes Q.qhk)[(fieldAt Q.shape p).2.1]? with
      | none => simp
      | some v => exact u32Bytes_lt _ _ (List.mem_of_getElem? he)
    have hhi := nibble_bits (Q.q.getD p 0 / 16 : Int) (by omega) (by omega)
    have hlo := nibble_bits (Q.q.getD p 0 % 16 : Int) (by omega) (by omega)
    simp only [List.getD_eq_getElem?_getD] at hhi hlo hbound
    ups_ev [hC]; cellsimp
    simp [hs,winFrV,WinFrB,ind]
    omega

/-- Complete padded-table HPL proof, with all bounds derived from prior semantic inputs. -/
theorem cByteHpl_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I∈insts, ∀ k, k<nQ I → NodeEncoding (part I k))
    (hf : ∀ I∈insts, ∀ k, k<nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts+1≤H) : GroupOk insts H cByteHpl := by
  apply groupOk_by ok hH (fun e h => by
    have hm : e∈UpsV3.cBytes := List.mem_of_mem_drop h
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc:=zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteHpl.all (vz zW (fun _ => false) false false false)=true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hpp q hq hr C D P hC hD
    have enc := he _ (inst_mem hi) k hk
    by_cases hn : p+1<(part (inst insts i) k).q.length
    · apply byte_hpl_qmid enc (hf _ (inst_mem hi) k hk) hpp hn
        (output_hplen_lt24 ok hi hk enc)
        hC
      intro x hx
      rw [hD x hx,nextRow ok.shape hq hr (rk':=.q k (p+1)) (by simp [nextRK,hn]),rowCell_q]
    · have hl : p+1=(part (inst insts i) k).q.length := by omega
      have hs := (((ok.inst _ (inst_mem hi)).memEnd k hk p hpp).1 hl).1
      exact byte_hpl_off (by omega) hC

end UpsGen
end ZkFormal.NearV3.Render
