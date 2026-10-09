import ZkFormal.NearV3.Qv.Extract.NativeKeyTraffic

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

private theorem nibble_ne_start (v : Nat) (hv : v<16) :
    (v:Fp)≠(SYM_START:Nat) := by
  intro he
  have hp : v<P := by
    have : 16<P := by decide
    omega
  have hs : SYM_START<P := by decide
  have he' := ofNat_inj hp hs he
  simp [SYM_START] at he'
  omega

/-- A native key stream cannot emit START at a nonzero position. -/
theorem native_key_start_position (id : Fp) (bs : NearSpec.Bytes) {m : List Fp}
    (hm : m∈nativeKeyTraffic id bs) (hs : m.getD 2 0=(SYM_START:Nat)) :
    m.getD 1 0=0 := by
  obtain ⟨i,_,hm⟩ := List.mem_flatMap.mp hm
  have hb := UInt8.toNat_lt (bs.getD i 0)
  have hh : (bs.getD i 0).toNat/16<16 := by omega
  have hl : (bs.getD i 0).toNat%16<16 := by omega
  simp only [nativeKeyRow,List.mem_append] at hm
  rcases hm with (hm|hm)|hm
  · split at hm
    · simp only [List.mem_singleton] at hm
      subst m
      rfl
    · simp at hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact False.elim (nibble_ne_start _ hh hs)
    · exact False.elim (nibble_ne_start _ hl hs)
  · split at hm
    · simp only [List.mem_singleton] at hm
      subst m
      have he : (SYM_END:Fp)≠(SYM_START:Nat) := by decide
      exact False.elim (he hs)
    · simp at hm

/-- The same marker restriction follows for every actual physical send. -/
theorem physical_key_start_position {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) {m : List Fp}
    (hm : m∈(List.range (tr.height tt)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_KEYNIB true))
    (hs : m.getD 2 0=(SYM_START:Nat)) : m.getD 1 0=0 := by
  rw [native_key_physical hL q] at hm
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hm
  exact native_key_start_position _ _ hp hs

end ZkFormal.NearV3.Qv.Extract
