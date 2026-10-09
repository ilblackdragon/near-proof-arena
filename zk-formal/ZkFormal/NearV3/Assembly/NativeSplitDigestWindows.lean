import ZkFormal.NearV3.Assembly.NativeSerializedDigests

namespace ZkFormal.NearV3.Assembly
open NearSpec Render.UpsGen

private theorem kidsFrom_child (len start : Nat) (f : Nat→Option PTrie)
    (i : Nat) (hi : i<len) : nativeChildAt (kidsFrom len start f) i=f (start+i) := by
  induction len generalizing start i with
  | zero=>omega
  | succ len ih=>
    cases i with
    | zero=>cases h:f start <;> simp [kidsFrom,h,nativeChildAt]
    | succ i=>
      cases h:f start <;> simp only [kidsFrom,h,nativeChildAt]
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1) i (by omega)
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1) i (by omega)

/-- The one-child split branch retains the selected native output occurrence. -/
theorem kids1_selected (x : Nat) (child : PTrie) (hx : x<16) :
    nativeChildAt (kids1 x child) x=some child := by
  unfold kids1
  rw [kidsFrom_child _ _ _ x hx]
  simp

/-- Both children of a two-way split retain their identity independently of
which child appears first in serialization. -/
theorem kids2_selected (x y : Nat) (a b : PTrie) (hx : x<16) (hy : y<16) (hne : x≠y) :
    nativeChildAt (kids2 x a y b) x=some a ∧ nativeChildAt (kids2 x a y b) y=some b := by
  unfold kids2
  rw [kidsFrom_child _ _ _ x hx,kidsFrom_child _ _ _ y hy]
  simp [Ne.symm hne]

/-- Both actual split-child digests are present in the serialized branch at
separate occurrence offsets; equal hashes are not merged. -/
theorem split_two_digest_windows (x y : Nat) (a b : PTrie) (mem : Nat)
    (hx : x<16) (hy : y<16) (hne : x≠y) (ha : a.hashOf.length=32) (hb : b.hashOf.length=32) :
    let kids:=kids2 x a y b
    ((nodeEnc (.branch none kids mem)).drop
      ((branchHashPrefix none kids).length+childHashOffset kids x)).take 32=a.hashOf ∧
    ((nodeEnc (.branch none kids mem)).drop
      ((branchHashPrefix none kids).length+childHashOffset kids y)).take 32=b.hashOf := by
  obtain ⟨hax,hby⟩:=kids2_selected x y a b hx hy hne
  exact ⟨branch_child_digest_window none _ mem x a hax ha,
    branch_child_digest_window none _ mem y b hby hb⟩

end ZkFormal.NearV3.Assembly
