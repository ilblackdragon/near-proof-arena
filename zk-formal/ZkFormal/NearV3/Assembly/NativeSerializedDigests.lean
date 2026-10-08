import ZkFormal.NearV3.Assembly.SchedulerChildDigests

namespace ZkFormal.NearV3.Assembly
open NearSpec Render.UpsGen

private theorem slice_append (pre hash post : Bytes) (hh : hash.length=32) :
    ((pre++hash++post).drop pre.length).take 32=hash := by
  rw [List.append_assoc,List.drop_left,←hh,List.take_left]

/-- Native leaf value digest at its exact full-u32 header offset. No small-key
or constant node-length hypothesis is used. -/
theorem leaf_value_digest_window (key : List Nat) (v : Bytes) (mem : Nat) :
    ((nodeEnc (.leaf key (.val v) mem)).drop
      (1+(u32 (hexPrefix key true).length).length+(hexPrefix key true).length+(u32 v.length).length)).take 32=
      sha256 v := by
  have h:=slice_append ([0]++u32 (hexPrefix key true).length++hexPrefix key true++u32 v.length)
    (sha256 v) (u64 mem) (ArenaCore.sha256_length _)
  simpa only [nodeEnc,Slot.valueRef,List.length_append,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.reduceAdd,Nat.add_assoc,List.append_assoc] using h

/-- Native branch value digest, independent of branch arity or child shape. -/
theorem branch_value_digest_window (v : Bytes) (kids : Kids) (mem : Nat) :
    ((nodeEnc (.branch (some (.val v)) kids mem)).drop (1+(u32 v.length).length)).take 32=sha256 v := by
  have h:=slice_append ([2]++u32 v.length) (sha256 v)
    (u16 (kidsBitmap kids 0)++Kids.hashes kids++u64 mem) (ArenaCore.sha256_length _)
  simpa only [nodeEnc,Slot.valueRef,List.length_append,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.reduceAdd,Nat.add_assoc,List.append_assoc] using h

/-- Native extension digest at its exact serialized header length. -/
theorem extension_digest_window (key : List Nat) (child : PTrie) (mem : Nat)
    (hh : child.hashOf.length=32) :
    ((nodeEnc (.ext key child mem)).drop
      (1+(u32 (hexPrefix key false).length).length+(hexPrefix key false).length)).take 32=child.hashOf := by
  have h:=slice_append ([3]++u32 (hexPrefix key false).length++hexPrefix key false)
    child.hashOf (u64 mem) hh
  simpa only [nodeEnc,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,
    Nat.reduceAdd,Nat.add_assoc,List.append_assoc] using h

/-- Serialized offset sums actual preceding child hashes; it does not assume
flat children or deduplicate structurally equal occurrences. -/
def childHashOffset : Kids→Nat→Nat
  | .nil,_=>0
  | .none _,0=>0
  | .some _ _,0=>0
  | .none rest,n+1=>childHashOffset rest n
  | .some c rest,n+1=>c.hashOf.length+childHashOffset rest n

/-- The selected native child is embedded at its actual occurrence offset. -/
theorem kids_digest_window : ∀(kids : Kids)(n : Nat)(child : PTrie),
    nativeChildAt kids n=some child → child.hashOf.length=32 →
    ((Kids.hashes kids).drop (childHashOffset kids n)).take 32=child.hashOf
  | .nil,n,child,h,hh=>by simp [nativeChildAt] at h
  | .none rest,0,child,h,hh=>by simp [nativeChildAt] at h
  | .some c rest,0,child,h,hh=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child
    simp only [childHashOffset,Nat.zero_add,List.drop_zero,Kids.hashes]
    rw [←hh,List.take_left]
  | .none rest,n+1,child,h,hh=>by
    exact kids_digest_window rest n child h hh
  | .some c rest,n+1,child,h,hh=>by
    simp only [Kids.hashes,childHashOffset]
    rw [←List.drop_drop,List.drop_left]
    exact kids_digest_window rest n child h hh

theorem kids_digest_window_tail : ∀(kids : Kids)(n : Nat)(child : PTrie)(tail : Bytes),
    nativeChildAt kids n=some child → child.hashOf.length=32 →
    ((Kids.hashes kids++tail).drop (childHashOffset kids n)).take 32=child.hashOf
  | .nil,n,child,tail,h,hh=>by simp [nativeChildAt] at h
  | .none rest,0,child,tail,h,hh=>by simp [nativeChildAt] at h
  | .some c rest,0,child,tail,h,hh=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child
    simp only [childHashOffset,List.drop_zero,Kids.hashes,List.append_assoc]
    rw [←hh,List.take_left]
  | .none rest,n+1,child,tail,h,hh=>by
    exact kids_digest_window_tail rest n child tail h hh
  | .some c rest,n+1,child,tail,h,hh=>by
    simp only [Kids.hashes,childHashOffset,List.append_assoc]
    rw [←List.drop_drop,List.drop_left]
    exact kids_digest_window_tail rest n child tail h hh

def branchHashPrefix (value : Option Slot) (kids : Kids) : Bytes :=
  match value with
  | none=>[1]++u16 (kidsBitmap kids 0)
  | some v=>[2]++v.valueRef++u16 (kidsBitmap kids 0)

/-- Branch output serialization exposes the actual selected child at its full
header plus preceding-occurrence byte offset. Both value/no-value cases. -/
theorem branch_child_digest_window (value : Option Slot) (kids : Kids) (mem n : Nat)
    (child : PTrie) (hc : nativeChildAt kids n=some child) (hh : child.hashOf.length=32) :
    ((nodeEnc (.branch value kids mem)).drop
      ((branchHashPrefix value kids).length+childHashOffset kids n)).take 32=child.hashOf := by
  have he : nodeEnc (.branch value kids mem)=branchHashPrefix value kids++(Kids.hashes kids++u64 mem) := by
    cases value <;> simp only [nodeEnc,branchHashPrefix,List.append_assoc]
  rw [he,←List.drop_drop,List.drop_left]
  exact kids_digest_window_tail kids n child (u64 mem) hc hh

end ZkFormal.NearV3.Assembly
