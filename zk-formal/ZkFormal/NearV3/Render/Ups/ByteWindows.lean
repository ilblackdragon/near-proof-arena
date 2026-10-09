import ZkFormal.NearV3.Render.Ups.GFieldsComplete

/-! Fresh digest windows store the current and following serialized bytes. -/
set_option maxHeartbeats 1000000
namespace ZkFormal.NearV3.Render.UpsGen

theorem winFr_formula (I : UpsInst) (Q : UpsPartI) (st wi : Nat) :
    winFrV I Q st wi = ind (st = 5) * (1 - cpV I Q st wi) + ind (st = 7) * wfrV I Q st wi := by
  by_cases h5 : st = 5
  · subst st
    cases hc : CpB I Q 5 wi <;> simp [winFrV,WinFrB,cpV,wfrV,ind,hc]
  · by_cases h7 : st = 7
    · subst st
      cases hw : WfrB I Q 7 wi <;> simp [winFrV,WinFrB,cpV,wfrV,ind,hw]
    · simp [winFrV,WinFrB,cpV,wfrV,ind,h5,h7]

theorem winFr_states {I : UpsInst} {Q : UpsPartI} {st wi : Nat}
    (h : winFrV I Q st wi = 1) : st = 5 ∨ st = 7 := by
  unfold winFrV WinFrB ind at h
  split at h
  · rename_i hb
    simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at hb
    rcases hb with ⟨hs,_⟩ | ⟨hs,_⟩ <;> omega
  · omega

/-- The fresh digest registers read ahead within the current 32-byte field. -/
theorem fresh_reg {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u i : Nat}
    (hi : i < 32) (hw : winFrV I Q st wi = 1) :
    QC I Q k p st ix fl wi u (129+i) =
      if i < 32-ix then (Q.q.getD (p+i) 0 : Int) else 0 := by
  have hs : isSeg (129+i) = false := by simp [isSeg]; omega
  have hc : isPC (129+i) = false := by simp [isPC]; omega
  simp only [QC,hs,hc,Bool.false_eq_true,ite_false]
  unfold qRow
  split <;> (try omega)
  simp only [show ¬ (106 ≤ 129+i ∧ 129+i < 115) by omega,
    show 129 ≤ 129+i ∧ 129+i < 161 by omega,ite_false,ite_true,hw,Nat.add_sub_cancel_left,and_self]

/-- Shifting the fresh window by one byte preserves the read-ahead bytes. -/
theorem fresh_reg_shift {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u u' i : Nat}
    (hi : i < 31) (hx : ix+1 < 32) (hw : winFrV I Q st wi = 1) :
    QC I Q k (p+1) st (ix+1) fl wi u' (129+i) = QC I Q k p st ix fl wi u (129+(i+1)) := by
  rw [fresh_reg (by omega) hw,fresh_reg (by omega) hw]
  have he : p+1+i = p+(i+1) := by omega
  have hb : i < 32-(ix+1) ↔ i+1 < 32-ix := by omega
  simp only [he,hb]

/-- Fresh windows are either a value digest or child digest, both exactly32bytes. -/
theorem FieldsOk.fresh_width {I : UpsInst} {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hp : p < Q.q.length)
    (hw : winFrV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = 1) :
    (fieldAt Q.shape p).2.2.1 = 32 := by
  have hm := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; exact hp)).2
  have hn : ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.2.1) ∈
      nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← ok.shape]; exact hm
  have hlen := nodeFields_length hn
  rcases winFr_states hw with hs | hs
  · exact hlen.2.2.2.2.2.1 hs
  · exact hlen.2.2.2.2.2.2.2.1 hs

end ZkFormal.NearV3.Render.UpsGen
