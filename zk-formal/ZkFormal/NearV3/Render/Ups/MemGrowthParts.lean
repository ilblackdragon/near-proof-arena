import ZkFormal.NearV3.Render.Ups.MemGrowth

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 ZkFormal.Near
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem trace_output_memory_growth (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun)
    (hw : t.wf=true) (hk : key.length≤2) (hv : v.length<2^24)
    (h : traceUpsert t key v=some run) : run.output.memD≤2^65*(fdepth t key+1) := by
  apply upsert_memory_growth t key v run.output hw hk hv
  simpa [h] using (traceUpsert_output t key v).symm

mutual
theorem trace_parts_memory_growth : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    t.wf=true → key.length≤2 → v.length<2^24 → traceUpsert t key v=some run →
    ∀ part∈run.parts,part.output.memD≤2^65*(fdepth t key+1)
  | .hash _, _, _, _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, hw, hk, hv, h => by
    have hb := trace_output_memory_growth (.leaf k s m) key v run hw hk hv h
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run
      simpa [terminalRun] using hb
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
      have hs : s.len<2^32 := by have hh := hw.1.1.2; cases s <;> simp_all [slotOk,Slot.len]
      have hkey : k.length<2^34 := by rw [Render.NodeInfo.hexPrefix_len] at hw; omega
      intro part hpart
      have hp := leafSplitRun_memory_bound k key s m v hk hkey hs hv part hpart
      simp only [fdepth]; omega
  | .ext k c m, key, v, run, hw, hk, hv, h => by
    have hb := trace_output_memory_growth (.ext k c m) key v run hw hk hv h
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      have hkey : k.length<2^34 := by rw [Render.NodeInfo.hexPrefix_len] at hw; omega
      intro part hpart
      have hpartbound := extSplitRun_memory_bound k key c m v hk hkey hw.1.2 hv part hpart
      simp only [fdepth,hp]; omega
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          intro part hpart
          simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
          rcases hpart with hpart|rfl
          · have ih := trace_parts_memory_growth c (key.drop k.length) v inner hw.1.1.2
              (by simp only [List.length_drop]; omega) hv hr part hpart
            simp only [fdepth,hp,ite_true,Nat.mul_add]; omega
          · exact hb
  | .branch bv cs m, [], v, run, hw, hk, hv, h => by
    have hb := trace_output_memory_growth (.branch bv cs m) [] v run hw hk hv h
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    simpa [terminalRun] using hb
  | .branch bv cs m, n::key, v, run, hw, hk, hv, h => by
    have hb := trace_output_memory_growth (.branch bv cs m) (n::key) v run hw hk hv h
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      intro part hpart
      simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
      rcases hpart with hpart|rfl
      · have ih := trace_kids_parts_memory_growth (.branch bv cs m) (n::key) cs 16 n key v inner
          hw.1.2 (by simp only [List.length_cons] at hk; omega) hv hr part hpart
        simp only [fdepth,Nat.mul_add]; omega
      · exact hb
theorem trace_kids_parts_memory_growth : ∀ (src : PTrie) (wholeKey : List Nat)
    (cs : Kids) (slots n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun),
    Kids.wf cs slots=true → key.length≤2 → v.length<2^24 →
    traceKids src wholeKey cs n key v=some run →
    ∀ part∈run.inner.parts,part.output.memD≤2^65*(kfdepth cs n key+1)
  | _, _, .nil, _, _, _, _, _, _, _, _, h => by simp [traceKids] at h
  | src, wholeKey, .none rest, slots, 0, key, v, run, _, hk, hv, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    simp [terminalRun,kfdepth,newLeaf,PTrie.memD,PTrie.mem?,leafMem,Render.NodeInfo.hexPrefix_len]
    omega
  | src, wholeKey, .some c rest, slots, 0, key, v, run, hw, hk, hv, h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact trace_parts_memory_growth c key v inner hw.1.2 hk hv hr
  | src, wholeKey, .none rest, slots, n+1, key, v, run, hw, hk, hv, h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hr : traceKids src wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact trace_kids_parts_memory_growth src wholeKey rest (slots-1) n key v inner hw.2 hk hv hr
  | src, wholeKey, .some c rest, slots, n+1, key, v, run, hw, hk, hv, h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hr : traceKids src wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact trace_kids_parts_memory_growth src wholeKey rest (slots-1) n key v inner hw.2 hk hv hr
end
theorem partialTrie_parts_memory_bound (values : List Bytes) (root : Bytes) (keys : List (List Nat))
    (hr : root.length=32) (key : List Nat) (v : Bytes) (run : TreeRun)
    (hk : key.length≤2) (hv : v.length<2^24)
    (hu : traceUpsert (partialTrie values root keys) key v=some run) :
    ∀ part∈run.parts,part.output.memD<2^74 := by
  have hbuilt := built_spec values 400 root keys hr
  have hw : (partialTrie values root keys).wf=true := hbuilt.2.1
  have hd : fdepth (partialTrie values root keys) key≤400 := hbuilt.2.2.2 key
  intro part hpart
  have hg := trace_parts_memory_growth (partialTrie values root keys) key v run hw hk hv hu part hpart
  omega

end ZkFormal.NearV3.Render.UpsGen
