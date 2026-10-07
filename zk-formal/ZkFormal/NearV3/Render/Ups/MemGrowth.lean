import ZkFormal.NearV3.Render.Ups.MemGrowthTerminal

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 ZkFormal.Near
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

mutual
theorem upsert_memory_growth : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (out : PTrie),
    t.wf=true → key.length≤2 → v.length<2^24 → t.upsert key v=some out →
    out.memD≤2^65*(fdepth t key+1)
  | .hash _, _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, v, out, hw, hk, hv, h => by
    have hwo := hw
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    have hs : s.len<2^32 := by have hh := hw.1.1.2; cases s <;> simp_all [slotOk,Slot.len]
    have hkey : k.length<2^34 := by rw [Render.NodeInfo.hexPrefix_len] at hw; omega
    by_cases he : k=key
    · simp only [PTrie.upsert,he,ite_true,Option.some.injEq] at h
      subst out
      simp [newLeaf,PTrie.memD,PTrie.mem?,leafMem,Render.NodeInfo.hexPrefix_len,fdepth]
      omega
    · simp only [PTrie.upsert,he,ite_false,Option.some.injEq] at h
      subst out
      have hb := splitLeaf_memory_bound k key s v hk hkey hs hv
      simp only [fdepth]; omega
  | .ext k c m, key, v, out, hw, hk, hv, h => by
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    have hkey : k.length<2^34 := by rw [Render.NodeInfo.hexPrefix_len] at hw; omega
    cases hp : isPrefix k key with
    | false =>
      simp only [PTrie.upsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst out
      have hb := splitExt_memory_bound k key c m v hk hkey hw.1.2 hv
      simp only [fdepth,hp]; omega
    | true =>
      cases hm : c.mem? with
      | none => simp [PTrie.upsert,hp,hm] at h
      | some cm =>
        cases hr : c.upsert (key.drop k.length) v with
        | none => simp [PTrie.upsert,hp,hm,hr] at h
        | some inner =>
          simp only [PTrie.upsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst out
          have ih := upsert_memory_growth c (key.drop k.length) v inner hw.1.1.2
            (by simp only [List.length_drop]; omega) hv hr
          change m+inner.memD-cm≤_
          simp only [fdepth,hp,ite_true,Nat.mul_add]
          omega
  | .branch bv cs m, [], v, out, hw, hk, hv, h => by
    simp only [PTrie.upsert,Option.some.injEq] at h
    subst out
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    simp [PTrie.memD,PTrie.mem?,fdepth,valueMem]
    omega
  | .branch bv cs m, n::key, v, out, hw, hk, hv, h => by
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    cases hr : cs.upsert n key v with
    | none => simp [PTrie.upsert,hr] at h
    | some inner =>
      simp only [PTrie.upsert,hr,Option.map_some,Option.some.injEq] at h
      subst out
      have ih := kids_memory_growth cs 16 n key v inner hw.1.2 (by simp only [List.length_cons] at hk; omega) hv hr
      simp [PTrie.memD,PTrie.mem?,fdepth,Nat.mul_add]
      omega
theorem kids_memory_growth : ∀ (cs : Kids) (slots n : Nat) (key : List Nat)
    (v : Bytes) (out : Kids × Nat × Nat),
    Kids.wf cs slots=true → key.length≤2 → v.length<2^24 → cs.upsert n key v=some out →
    out.2.2≤2^65*(kfdepth cs n key+1)
  | .nil, _, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | .none rest, _, 0, key, v, out, _, hk, hv, h => by
    simp only [Kids.upsert,Option.some.injEq] at h
    subst out
    simp [kfdepth,leafMem,Render.NodeInfo.hexPrefix_len]
    omega
  | .some c rest, slots, 0, key, v, out, hw, hk, hv, h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : c.mem? with
    | none => simp [Kids.upsert,hm] at h
    | some cm =>
      cases hr : c.upsert key v with
      | none => simp [Kids.upsert,hm,hr] at h
      | some inner =>
        simp only [Kids.upsert,hm,hr,Option.some.injEq] at h
        subst out
        exact upsert_memory_growth c key v inner hw.1.2 hk hv hr
  | .none rest, slots, n+1, key, v, out, hw, hk, hv, h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hr : rest.upsert n key v with
    | none => simp [Kids.upsert,hr] at h
    | some inner =>
      simp only [Kids.upsert,hr,Option.map_some,Option.some.injEq] at h
      subst out
      exact kids_memory_growth rest (slots-1) n key v inner hw.2 hk hv hr
  | .some c rest, slots, n+1, key, v, out, hw, hk, hv, h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hr : rest.upsert n key v with
    | none => simp [Kids.upsert,hr] at h
    | some inner =>
      simp only [Kids.upsert,hr,Option.map_some,Option.some.injEq] at h
      subst out
      exact kids_memory_growth rest (slots-1) n key v inner hw.2 hk hv hr
end
/-- The accepted source builder's fixed fuel controls exact output memory even
when stored parent/child memory totals are mutually inconsistent. -/
theorem partialTrie_memory_bound (values : List Bytes) (root : Bytes) (keys : List (List Nat))
    (hr : root.length=32) (key : List Nat) (v : Bytes) (out : PTrie)
    (hk : key.length≤2) (hv : v.length<2^24)
    (hu : (partialTrie values root keys).upsert key v=some out) : out.memD<2^74 := by
  have hbuilt := built_spec values 400 root keys hr
  have hw : (partialTrie values root keys).wf=true := hbuilt.2.1
  have hd : fdepth (partialTrie values root keys) key≤400 := hbuilt.2.2.2 key
  have hg := upsert_memory_growth (partialTrie values root keys) key v out hw hk hv hu
  omega

end ZkFormal.NearV3.Render.UpsGen
