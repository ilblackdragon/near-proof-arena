import ZkFormal.NearV3.Qv.Extract.RepairedKeyTraffic
import ZkFormal.NearV3.Link.Compose3

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

private theorem nibble_not_start (v : Nat) (hv : v<16) :
    (v:Fp)≠(SYM_START:Nat) := by
  intro he
  have hp : v<P := by
    have : 16<P := by decide
    omega
  have he' := ofNat_inj hp (show SYM_START<P by decide) he
  simp [SYM_START] at he'
  omega

/-- Every repaired message is a nibble or END, hence cannot restart a walk. -/
theorem repaired_key_no_start (id : Fp) (bs : NearSpec.Bytes) {m : List Fp}
    (hm : m∈repairedKeyTraffic id bs) : m.getD 2 0≠(SYM_START:Nat) := by
  obtain ⟨i,_,hm⟩ := List.mem_flatMap.mp hm
  have hb := UInt8.toNat_lt (bs.getD i 0)
  simp only [repairedKeyRow,List.mem_append] at hm
  rcases hm with hm|hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact nibble_not_start _ (by omega)
    · exact nibble_not_start _ (by omega)
  · split at hm
    · simp only [List.mem_singleton] at hm
      subst m
      change (SYM_END:Fp)≠(SYM_START:Nat)
      decide
    · simp at hm

theorem repaired_physical_no_start {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    {m : List Fp} (hm : m∈(List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true)) :
    m.getD 2 0≠(SYM_START:Nat) := by
  rw [repaired_key_physical h q] at hm
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hm
  exact repaired_key_no_start _ _ hp

/-- Field-level provider interface for composition with actual physical traffic.
Global KEYNIB balance/ownership must supply `hsub`; no natural-message lift is
required just to rule out a second START in the trie walk. -/
theorem walk_no_start_of_physical {ws : List WalkR} {prov : List (List Fp)}
    (hsub : ∀ m∈walkRecvs3 ws B_KEYNIB, Msg.toFp m∈prov)
    (hsy : ∀ m∈prov, m.getD 2 0≠(SYM_START:Nat)) :
    ∀ wv∈ws, ∀ i, 1≤i → i<wv.steps.length → (wv.step i).sym≠SYM_START := by
  intro wv hw i h1 h2 hs
  have hm : [wv.w,i-1,(wv.step i).sym,if i-1+2=wv.steps.length then 1 else 0]∈
      walkRecvs3 ws B_KEYNIB := by
    unfold walkRecvs3
    rw [if_neg (by decide),if_neg (by decide),if_pos rfl,List.mem_flatMap]
    refine ⟨wv,hw,List.mem_map.mpr ⟨i-1,List.mem_range.mpr (by omega),?_⟩⟩
    rw [show i-1+1=i by omega]
  have hn := hsy _ (hsub _ hm)
  apply hn
  simp only [Msg.toFp,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero,hs]
  rfl

end ZkFormal.NearV3.Qv.Extract
