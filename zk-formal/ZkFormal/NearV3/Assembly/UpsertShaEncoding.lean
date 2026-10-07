import ZkFormal.NearV3.Assembly.UpsertShaJobs
import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts
import ZkFormal.NearV3.Assembly.UpsertOutputWidth

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen ZkFormal.Near

@[simp] theorem nativeBytes_roundtrip (bs : Bytes) :
    (bs.map UInt8.toNat).map UInt8.ofNat=bs := by
  simp [List.map_map,Function.comp_def]

/-- Converting the renderer's shallow view back to bytes is exactly the native
serializer, even if a caller supplies an oversized bitmap or memory integer.
This does not by itself prove the renderer's Nat entries are valid bytes. -/
theorem treeNode_native_bytes {t : PTrie} {node : NodeV3}
    (hn : treeNode t=some node) (post : Bool) :
    (node.ser post).map UInt8.ofNat=nodeEnc t := by
  cases t with
  | hash => simp [treeNode] at hn
  | leaf key val mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN,List.map_append,Function.comp_def]
  | ext key child mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN,List.map_append,Function.comp_def]
  | branch value kids mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    cases value <;> simp [NodeV3.ser,nodeEnc,u16,leN,List.map_append,Function.comp_def] <;>
      exact (show UInt8.ofNat ((kidsBitmap kids 0 / 256)%256)=UInt8.ofNat (kidsBitmap kids 0 / 256) from UInt8.ofNat_mod_size).symm

theorem encodeTreePart_native_bytes {base Q : Render.UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) :
    Q.pb.map UInt8.ofNat=nodeEnc p.source ∧ Q.q.map UInt8.ofNat=nodeEnc p.output := by
  unfold encodeTreePart at he
  cases hs : treeNode p.source <;> cases hd : treeNode p.output <;> simp [hs,hd] at he
  subst Q
  exact ⟨treeNode_native_bytes hs true,treeNode_native_bytes hd false⟩

/-- Actual encoded node outputs hash to the native output digest; no post-u64
memory bound or SHA injectivity hypothesis is needed. -/
theorem nativeInstance_part_digest (recordId : PTrie→Nat) (baseI : Render.UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→Render.UpsPartI) {Qs : List Render.UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<Qs.length) : ∃ p,
      run.parts[k]?=some p ∧
      (part (nativeInstance recordId baseI root run v Qs) k).q.map UInt8.ofNat=nodeEnc p.output ∧
      sha256 ((part (nativeInstance recordId baseI root run v Qs) k).q.map UInt8.ofNat)=p.output.hashOf := by
  obtain ⟨p,Q,hp,_,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  have hb := (encodeTreePart_native_bytes henc).2
  refine ⟨p,hp,?_,?_⟩
  · rw [hpart]; exact hb
  · rw [hpart]
    change sha256 (Q.q.map UInt8.ofNat)=p.output.hashOf
    rw [hb]
    exact upsertShaJob_node_digest hr (List.mem_of_getElem? hp)

/-- The concrete SHA allocator and actual encoded part agree after interpreting
renderer Nat entries as bytes. The later exact theorem also discharges Nat preimage equality
from ordinary input well-formedness. -/
theorem nativeInstance_part_shaJob (recordId : PTrie→Nat) (baseI : Render.UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→Render.UpsPartI) {Qs : List Render.UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<Qs.length) : ∃ M,
      (upsertShaJobs baseI.tau v run)[k+1]?=some M ∧
      M.id=upsertJobId baseI.tau (k+1) ∧
      M.bytes.map UInt8.ofNat=(part (nativeInstance recordId baseI root run v Qs) k).q.map UInt8.ofNat := by
  obtain ⟨p,hp,hbytes,_⟩ := nativeInstance_part_digest recordId baseI hr base he k hk
  refine ⟨upsertShaJob baseI.tau (k+1) (nodeEnc p.output),?_,rfl,?_⟩
  · rw [upsertShaJobs_part,hp]; rfl
  · change ((nodeEnc p.output).map UInt8.toNat).map UInt8.ofNat=_
    rw [nativeBytes_roundtrip,hbytes]

/-- A native branch's 16 slots are the only extra condition needed for exact
Nat serialization. Memory need not fit u64, and child hashes need no injectivity. -/
theorem treeNode_nat_bytes {t : PTrie} {node : NodeV3}
    (hn : treeNode t=some node) (hw : NativeBranchWidth t) (post : Bool) :
    node.ser post=(nodeEnc t).map UInt8.toNat := by
  cases t with
  | hash => simp [treeNode] at hn
  | leaf key val mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN]
  | ext key child mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN]
  | branch value kids mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    have hb := Link.kidBitmap_lt hw
    rw [treeKids_bitmap] at hb
    cases value <;> simp [NodeV3.ser,nodeEnc,map_u16_small _ hb]

theorem encodeTreePart_nat_output {base Q : Render.UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) (hw : NativeBranchWidth p.output) :
    Q.q=(nodeEnc p.output).map UInt8.toNat := by
  unfold encodeTreePart at he
  cases hs : treeNode p.source <;> cases hd : treeNode p.output <;> simp [hs,hd] at he
  subst Q
  exact treeNode_nat_bytes hd hw false

/-- Exact preimages for actual native inputs: source wf discharges all output
branch widths. There is no output-wf, per-byte, or post-memory-width premise. -/
theorem nativeInstance_part_shaJob_exact (recordId : PTrie→Nat) (baseI : Render.UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→Render.UpsPartI) {Qs : List Render.UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<Qs.length) : ∃ M,
      (upsertShaJobs baseI.tau v run)[k+1]?=some M ∧
      M.id=upsertJobId baseI.tau (k+1) ∧
      M.bytes=(part (nativeInstance recordId baseI root run v Qs) k).q := by
  obtain ⟨p,Q,hp,_,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  have hb := encodeTreePart_nat_output henc
    (traceUpsert_branchWidth root [0,15] v run hr hw p (List.mem_of_getElem? hp))
  refine ⟨upsertShaJob baseI.tau (k+1) (nodeEnc p.output),?_,rfl,?_⟩
  · rw [upsertShaJobs_part,hp]; rfl
  · rw [hpart]; exact hb.symm

end ZkFormal.NearV3.Assembly
