import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyView
import ZkFormal.NearV3.Qv.Extract.WalkBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySymbols
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Qv.Candidates.CombinedTable
set_option maxHeartbeats 300000
set_option maxRecDepth 32768

theorem local_symbols {pub:List Fp} {tr:Trace Fp} {tt:Nat}
    (hLocal:TableLocal Qv.Candidates.KeyTrafficRepair.table tr tt pub)
    {r:Nat} (hr:r<tr.height tt) {m:List Fp}
    (hm:m∈rowTraffic Qv.Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) :
    m[2]!.toNat<16 ∨ m[2]!.toNat=SYM_END := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base hLocal
  have hrow := Qv.Candidates.KeyTrafficRepair.key_row tr tt r pub
  have hm0 := hrow ▸ hm
  clear hm
  have hm := List.mem_append.mp hm0
  rcases hm with hm|hm
  · split at hm
    · rename_i ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl
      · obtain ⟨n,hn,he⟩:=Qv.Extract.walk_nibble hL hr ha 4 (by decide)
        left
        change ((nibble 4).eval tr tt r pub).toNat<16
        rw [he,toNat_natCast,Nat.mod_eq_of_lt (by unfold P;omega)]
        exact hn
      · obtain ⟨n,hn,he⟩:=Qv.Extract.walk_nibble hL hr ha 0 (by decide)
        left
        change ((nibble 0).eval tr tt r pub).toNat<16
        rw [he,toNat_natCast,Nat.mod_eq_of_lt (by unfold P;omega)]
        exact hn
    · simp at hm
  · split at hm
    · simp only [List.mem_singleton] at hm
      subst m
      right
      change (Fp.ofNat SYM_END).toNat=SYM_END
      rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by decide)]
    · simp at hm
theorem row_symbols {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {r:Nat} (hr:r<tr.height 0) {m:List Fp}
    (hm:m∈rowTraffic Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_KEYNIB true) :
    m[2]!.toNat<16 ∨ m[2]!.toNat=SYM_END :=
  local_symbols (ProcPriorRoutedKeyView.local_key hH htables) hr hm
end ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySymbols
