import ZkFormal.NearV3.Assembly.NativeSplitDigestWindows
import ZkFormal.NearV3.Render.Ups.TreeSplitKids

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- One split child contributes precisely its native hash serialization. -/
theorem kids1_hashes (x : Nat) (child : PTrie) (hx : x<16) :
    Kids.hashes (kids1 x child)=child.hashOf := by
  have h:=treeKids_bytes (kids1 x child) false
  rw [treeKids_one x child hx,oneKid_bytes] at h
  change child.hashOf.map UInt8.toNat=(Kids.hashes (kids1 x child)).map UInt8.toNat at h
  have hh:=congrArg (List.map UInt8.ofNat) h
  simpa only [nativeBytes_roundtrip] using hh.symm

/-- Two split hashes are serialized in slot order, retaining both occurrences
regardless of whether their bytes happen to be equal. -/
theorem kids2_hashes (ts x : Nat) (old new : PTrie) (hx : x<16)
    (hd : x≠if ts=1 then 0 else 15) :
    Kids.hashes (kids2 x old (if ts=1 then 0 else 15) new)=
      if ts=1 then new.hashOf++old.hashOf else old.hashOf++new.hashOf := by
  have h:=treeKids_bytes (kids2 x old (if ts=1 then 0 else 15) new) false
  rw [treeKids_two ts x old new hx hd,twoEdgeKids_bytes] at h
  have hh:=congrArg (List.map UInt8.ofNat) h
  by_cases ht:ts=1 <;> simpa [ht,treeKid,NKid.bytes,List.map_append,nativeBytes_roundtrip,Function.comp_def] using hh.symm

private theorem prefix_slice (pre hash post : Bytes) (hh : hash.length=32) :
    ((pre++hash++post).drop pre.length).take 32=hash := by
  rw [List.append_assoc,List.drop_left,←hh,List.take_left]

/-- The singleton child starts after the exact native branch header. -/
theorem split_single_child_slice (sv : Option Slot) (x : Nat) (child : PTrie) (mem : Nat)
    (hx : x<16) (hh : child.hashOf.length=32) :
    ((nodeEnc (.branch sv (kids1 x child) mem)).drop
      (branchHashPrefix sv (kids1 x child)).length).take 32=child.hashOf := by
  have he : nodeEnc (.branch sv (kids1 x child) mem)=
      branchHashPrefix sv (kids1 x child)++child.hashOf++u64 mem := by
    cases sv <;> simp [nodeEnc,branchHashPrefix,kids1_hashes x child hx,List.append_assoc]
  rw [he]
  exact prefix_slice _ _ _ hh

/-- Both split-window payloads at physical offsets3 and35 have native order. -/
theorem split_pair_child_slices (ts x : Nat) (old new : PTrie) (mem : Nat)
    (hx : x<16) (hd : x≠if ts=1 then 0 else 15)
    (ho : old.hashOf.length=32) (hn : new.hashOf.length=32) :
    let out:=PTrie.branch none (kids2 x old (if ts=1 then 0 else 15) new) mem
    ((nodeEnc out).drop 3).take 32=(if ts=1 then new.hashOf else old.hashOf) ∧
    ((nodeEnc out).drop 35).take 32=(if ts=1 then old.hashOf else new.hashOf) := by
  dsimp only
  rw [nodeEnc,kids2_hashes ts x old new hx hd]
  by_cases ht:ts=1 <;> simp only [ht,ite_true,ite_false,List.append_assoc]
  all_goals constructor
  all_goals simp only [List.drop_append,List.length_cons,List.length_nil,u16_len,Nat.reduceAdd]
  all_goals simp [ht,ho,hn,List.take_append,List.drop_append,u16,leN,
    List.drop_eq_nil_of_le (show old.hashOf.length≤32 by omega),
    List.drop_eq_nil_of_le (show new.hashOf.length≤32 by omega)]

end ZkFormal.NearV3.Assembly
