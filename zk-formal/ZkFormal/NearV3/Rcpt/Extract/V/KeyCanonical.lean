import ZkFormal.NearV3.Rcpt.Extract.V.KeyMarkerLayout

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem nibble_length (xs : List Nat) : (xs.flatMap (fun ch => [ch/16,ch%16])).length=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem key_account_canonical (w : Nat) (x : RcptE) :
    RcptE.keyMsgs w x.keySyms=
      [[w,0,0,0],[w,1,0,0]]++symbolMsgs w 2 (x.v.flatMap (fun ch => [ch/16,ch%16]))++
      [[w,2+2*x.v.length,SYM_END,1]] := by
  rw [Near.RcptV.keySyms,keyMsgs_marker,symbolMsgs_append]
  simp only [List.length_append,List.length_cons,List.length_nil,nibble_length,Nat.zero_add]
  have hh : symbolMsgs w 0 [0,0]=[[w,0,0,0],[w,1,0,0]] := by simp [symbolMsgs,List.range_succ]
  rw [hh]

/-- Access-key canonical order places the separator after signer bytes. -/
theorem key_access_canonical (w : Nat) (x : RcptE) (hk : x.kt≤1) :
    RcptE.keyMsgs w x.akSyms=
      [[w,0,0,0],[w,1,2,0]]++symbolMsgs w 2 (x.s.flatMap (fun ch => [ch/16,ch%16]))++
      [[w,2+2*x.s.length,0,0],[w,3+2*x.s.length,2,0]]++
      [[w,4+2*x.s.length,0,0],[w,5+2*x.s.length,x.kt,0]]++
      symbolMsgs w (6+2*x.s.length) (x.pk.flatMap (fun ch => [ch/16,ch%16]))++
      [[w,6+2*x.s.length+2*x.pk.length,SYM_END,1]] := by
  have hd : x.kt/16=0 := by omega
  have hm : x.kt%16=x.kt := by omega
  rw [RcptE.akSyms,keyMsgs_marker]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    Nat.reduceDiv,Nat.reduceMod,hd,hm,symbolMsgs_append,List.length_append,List.length_cons,List.length_nil,nibble_length]
  have hh (o a b : Nat) : symbolMsgs w o [a,b]=[[w,o,a,0],[w,o+1,b,0]] := by
    simp [symbolMsgs,List.range_succ]
  simp only [hh,Nat.zero_add]
  simp only [List.append_assoc]
  simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [show 2+(2+(2+2*x.s.length))=2*x.s.length+6 by omega]
  exact ⟨by omega,by omega,by omega,rfl,by omega⟩

/-- Physical key-field order differs only by the location of the separator. -/
def accessPhysicalMsgs (w : Nat) (x : RcptE) : List Msg :=
  [[w,0,0,0],[w,1,2,0]]++
  [[w,2+2*x.s.length,0,0],[w,3+2*x.s.length,2,0]]++
  symbolMsgs w 2 (x.s.flatMap (fun ch => [ch/16,ch%16]))++
  [[w,4+2*x.s.length,0,0],[w,5+2*x.s.length,x.kt,0]]++
  symbolMsgs w (6+2*x.s.length) (x.pk.flatMap (fun ch => [ch/16,ch%16]))++
  [[w,70+2*x.s.length+64*x.kt,SYM_END,1]]

theorem accessPhysicalMsgs_perm (w : Nat) (x : RcptE) (hk : x.kt≤1)
    (hp : x.pk.length=32+32*x.kt) :
    (accessPhysicalMsgs w x).Perm (RcptE.keyMsgs w x.akSyms) := by
  rw [key_access_canonical w x hk]
  unfold accessPhysicalMsgs
  rw [show 6+2*x.s.length+2*x.pk.length=70+2*x.s.length+64*x.kt by omega]
  simp only [List.append_assoc]
  apply List.Perm.append_left
  simpa only [List.append_assoc] using (List.perm_append_comm
    (l₁:=[[w,2+2*x.s.length,0,0],[w,3+2*x.s.length,2,0]])
    (l₂:=symbolMsgs w 2 (x.s.flatMap (fun ch => [ch/16,ch%16])))).append_right
      ([[w,4+2*x.s.length,0,0],[w,5+2*x.s.length,x.kt,0]]++
        symbolMsgs w (6+2*x.s.length) (x.pk.flatMap (fun ch => [ch/16,ch%16]))++
        [[w,70+2*x.s.length+64*x.kt,SYM_END,1]])

end ZkFormal.NearV3.RcptV3Proof
