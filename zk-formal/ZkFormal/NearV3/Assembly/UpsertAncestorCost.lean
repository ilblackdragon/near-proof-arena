import ZkFormal.NearV3.Assembly.UpsertShaEncoding
import ZkFormal.NearV3.Render.Ups.TreeKidsTrace

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen UpsSpec UpsRows

theorem traceUpsert_output_hash_length {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) : run.output.hashOf.length=32 := by
  have hu : t.upsert key v=some run.output := by
    have h := traceUpsert_output t key v
    simpa [hr] using h.symm
  rw [hashOf_eq_enc _ (upsert_isNode t key v run.output hu)]
  simp

/-- Extension ancestors change hash bytes and memory, but neither serialized width. -/
theorem traceUpsert_extension_bytes {child : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert child key v=some run) (hw : child.wf=true)
    (path : List Nat) (mem newMem : Nat) :
    (nodeEnc (.ext path run.output newMem)).length=(nodeEnc (.ext path child mem)).length := by
  simp [nodeEnc,traceUpsert_output_hash_length hr,hashOf_len_of_wf child hw]

/-- Descending into an existing child preserves branch hash-list length. Inserting
one new child adds exactly32 bytes, regardless of any overflowed memory scalar. -/
theorem traceKids_hash_bytes : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → ∀ width, Kids.wf cs width=true →
    (Kids.hashes run.output).length=(Kids.hashes cs).length+(if run.inserted then 32 else 0)
  | _,_,.nil,_,_,_,_,hr,_,_ => by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr,width,hw => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    simp [newLeaf,Kids.hashes,PTrie.hashOf,Nat.add_comm]
  | source,whole,.some c rest,0,key,v,run,hr,width,hw => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert c key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        have cw : c.wf=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.1.2
        simp [Kids.hashes,hashOf_len_of_wf c cw,traceUpsert_output_hash_length hc]
  | source,whole,.none rest,n+1,key,v,run,hr,width,hw => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have rw : Kids.wf rest (width-1)=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.2
      exact traceKids_hash_bytes source whole rest n key v inner hc (width-1) rw
  | source,whole,.some c rest,n+1,key,v,run,hr,width,hw => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have rw : Kids.wf rest (width-1)=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.2
      have ih := traceKids_hash_bytes source whole rest n key v inner hc (width-1) rw
      simp [Kids.hashes,ih,Nat.add_assoc]

theorem traceKids_branch_bytes {source : PTrie} {wholeKey : List Nat} {cs : Kids}
    {n : Nat} {key : List Nat} {v : Bytes} {run : KidsRun}
    (hr : traceKids source wholeKey cs n key v=some run) (hw : Kids.wf cs 16=true)
    (sv : Option Slot) (mem newMem : Nat) :
    (nodeEnc (.branch sv run.output newMem)).length=
      (nodeEnc (.branch sv cs mem)).length+(if run.inserted then 32 else 0) := by
  have h := traceKids_hash_bytes source wholeKey cs n key v run hr 16 hw
  cases sv <;> simp [nodeEnc,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem slot_valueRef_width {slot : Slot} (hw : NearSpec.slotOk slot=true) : slot.valueRef.length=36 := by
  cases slot <;> simp_all [NearSpec.slotOk,Slot.valueRef]

theorem native_leaf_size (key : List Nat) (slot : Slot) (mem : Nat)
    (hs : slot.valueRef.length=36) :
    (nodeEnc (.leaf key slot mem)).length=50+key.length/2 := by
  simp [nodeEnc,hs,ZkFormal.Near.Render.NodeInfo.hexPrefix_len]
  omega

theorem native_ext_size (key : List Nat) (child : PTrie) (mem : Nat)
    (hs : child.hashOf.length=32) :
    (nodeEnc (.ext key child mem)).length=46+key.length/2 := by
  simp [nodeEnc,hs,ZkFormal.Near.Render.NodeInfo.hexPrefix_len]
  omega

theorem newLeaf_byte_size (key : List Nat) (v : Bytes) (hk : key.length≤2) :
    (nodeEnc (newLeaf key v)).length≤51 := by
  unfold newLeaf
  rw [native_leaf_size _ _ _ (by simp [Slot.valueRef])]
  omega

theorem movedLeaf_byte_size {oldKey newKey : List Nat} (slot : Slot) (oldMem newMem : Nat)
    (hs : NearSpec.slotOk slot=true) (hk : newKey.length≤oldKey.length) :
    (nodeEnc (.leaf newKey slot newMem)).length≤(nodeEnc (.leaf oldKey slot oldMem)).length := by
  rw [native_leaf_size _ _ _ (slot_valueRef_width hs),native_leaf_size _ _ _ (slot_valueRef_width hs)]
  omega

theorem movedExt_byte_size {oldKey newKey : List Nat} (child : PTrie) (oldMem newMem : Nat)
    (hs : child.wf=true) (hk : newKey.length≤oldKey.length) :
    (nodeEnc (.ext newKey child newMem)).length≤(nodeEnc (.ext oldKey child oldMem)).length := by
  rw [native_ext_size _ _ _ (hashOf_len_of_wf child hs),native_ext_size _ _ _ (hashOf_len_of_wf child hs)]
  omega

theorem branch_value_byte_growth (sv : Option Slot) (cs : Kids) (oldMem newMem : Nat) (v : Bytes) :
    (nodeEnc (.branch (some (.val v)) cs newMem)).length≤
      (nodeEnc (.branch sv cs oldMem)).length+36 := by
  cases sv <;> simp [nodeEnc,Slot.valueRef] <;> omega

end ZkFormal.NearV3.Assembly
