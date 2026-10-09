import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountClosingVersion
import ZkFormal.NearV3.Rcpt.Candidates.NativeMemChain
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

theorem closingKeyVersion_snoc (key x : List Nat) (start : Nat) (ks : List (List Nat)) :
    closingKeyVersion key start (ks++[x])=
      if x=key then start+ks.length+1 else closingKeyVersion key start ks := by
  induction ks generalizing start with
  | nil=>simp [closingKeyVersion]
  | cons k ks ih=>
    by_cases hx:x=key
    · subst x
      simp [closingKeyVersion,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [closingKeyVersion,ih,hx]

/-- Indexed timestamp recurrence agrees with native key-based previous-write
selection whenever occurrence IDs faithfully identify the queried key. -/
theorem closingKeyVersion_prefix_lb (keys : List (List Nat)) (slot : Nat→Nat)
    (key : List Nat) (vid : Nat)
    (he:∀j,(hj:j<keys.length)→(slot j=vid ↔ keys[j]'hj=key)) :
    ∀b,b≤keys.length→closingKeyVersion key 0 (keys.take b)=NativeMemChain.lb slot vid b
  | 0,_=>rfl
  | b+1,hb=>by
    have hbi:b<keys.length:=by omega
    have ht:keys.take (b+1)=keys.take b++[keys[b]]:=by
      exact List.take_succ_eq_append_getElem hbi
    rw [ht,closingKeyVersion_snoc,NativeMemChain.lb]
    have hl:(keys.take b).length=b:=by simp [List.length_take,Nat.min_eq_left (by omega : b≤keys.length)]
    by_cases hs:slot b=vid
    · simp [hs,(he b hbi).mp hs,hl]
    · have hk:keys[b]≠key:=fun h=>hs ((he b hbi).mpr h)
      simp only [hs,hk,if_false]
      exact closingKeyVersion_prefix_lb keys slot key vid he b (by omega)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
