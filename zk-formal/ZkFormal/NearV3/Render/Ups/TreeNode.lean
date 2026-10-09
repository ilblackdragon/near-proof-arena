import ZkFormal.NearV3.Render.Ups.EncodePart
import ZkFormal.NearV3.Spec.Codec

/-! Executable shallow serialization view of an ordinary runtime trie node. Children
are represented by their actual hashes here; allocation of revealed child IDs belongs
to the path/node-store assembly layer. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

def treeSlot : Slot → NSlot3
  | .val value => .ref ((u32 value.length).map UInt8.toNat) ((sha256 value).map UInt8.toNat)
  | .ref len hash => .ref ((u32 len).map UInt8.toNat) (hash.map UInt8.toNat)

def treeKid (t : PTrie) : NKid := .hash (t.hashOf.map UInt8.toNat)

def treeKids : Kids → List NKid
  | .nil => []
  | .none rest => .none::treeKids rest
  | .some child rest => treeKid child::treeKids rest

def treeNode : PTrie → Option NodeV3
  | .hash _ => none
  | .leaf key value mem => some (.leaf key (treeSlot value) ((u64 mem).map UInt8.toNat))
  | .ext key child mem => some (.ext key (treeKid child) ((u64 mem).map UInt8.toNat))
  | .branch value kids mem => some (.branch (value.map treeSlot) (treeKids kids) ((u64 mem).map UInt8.toNat))

@[simp] theorem treeSlot_bytes (s : Slot) (post : Bool) :
    (treeSlot s).bytes post=s.valueRef.map UInt8.toNat := by
  cases s <;> simp [treeSlot,NSlot3.bytes,Slot.valueRef]

@[simp] theorem treeSlot_lenB (s : Slot) :
    (treeSlot s).lenB=(u32 s.len).map UInt8.toNat := by cases s <;> rfl

@[simp] theorem treeKid_bytes (t : PTrie) (post : Bool) :
    (treeKid t).bytes post=t.hashOf.map UInt8.toNat := rfl

@[simp] theorem treeKids_bytes : ∀(cs : Kids)(post : Bool),
    (treeKids cs).flatMap (NKid.bytes post)=(Kids.hashes cs).map UInt8.toNat
  | .nil,_ => rfl
  | .none rest,post => by simpa [treeKids,NKid.bytes,Kids.hashes] using treeKids_bytes rest post
  | .some c rest,post => by simp [treeKids,Kids.hashes,treeKids_bytes rest post]

theorem treeSlot_wf {s : Slot} (h : slotOk s=true) : (treeSlot s).wf := by
  cases s <;> simp_all [slotOk,treeSlot,NSlot3.wf]

theorem treeKid_wf {t : PTrie} (h : t.wf=true) : (treeKid t).wf := by
  simp [treeKid,NKid.wf,hashOf_len_of_wf _ h]

theorem treeKids_wf : ∀(cs : Kids)(n : Nat), Kids.wf cs n=true →
    (treeKids cs).length=n ∧ ∀k∈treeKids cs,k.wf
  | .nil,n,h => by simp [Kids.wf] at h; simp [treeKids,h]
  | .none rest,n,h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at h
    obtain ⟨hl,hw⟩ := treeKids_wf rest (n-1) h.2
    refine ⟨?_,?_⟩
    · simp [treeKids,hl]; omega
    · intro k hk; simp only [treeKids,List.mem_cons] at hk
      rcases hk with rfl|hk; trivial; exact hw k hk
  | .some c rest,n,h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at h
    obtain ⟨hl,hw⟩ := treeKids_wf rest (n-1) h.2
    refine ⟨?_,?_⟩
    · simp [treeKids,hl]; omega
    · intro k hk; simp only [treeKids,List.mem_cons] at hk
      rcases hk with rfl|hk; exact treeKid_wf h.1.2; exact hw k hk

theorem treeNode_wf {t : PTrie} {node : NodeV3} (hw : t.wf=true) (hn : treeNode t=some node) : node.wf := by
  cases t with
  | hash => simp [treeNode] at hn
  | leaf key value mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    refine ⟨?_,treeSlot_wf hw.1.1.2,by simp⟩
    simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
  | ext key child mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    refine ⟨?_,by simp [treeKid],treeKid_wf hw.1.1.2,by simp⟩
    simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
  | branch value kids mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    have hh := treeKids_wf kids 16 hw.1.2
    refine ⟨hh.1,?_,hh.2,by simp⟩
    intro s hs
    cases value with
    | none => simp at hs
    | some v => simp only [Option.map_some,Option.some.injEq] at hs; subst s; exact treeSlot_wf hw.1.1

end ZkFormal.NearV3.Render.UpsGen
