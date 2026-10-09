import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorBytes
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched
open ProcPriorLookup ProcPriorDecode

theorem link_length (r : LinkAllowance) : r.encode.length=24 := by
  simp [LinkAllowance.encode,u64,canon_leN_length]

theorem record_slice (rs : List LinkAllowance) (tail : Bytes) (k : Nat) (r : LinkAllowance)
    (h : rs[k]?=some r) :
    ((concatAll (rs.map LinkAllowance.encode)++tail).drop (24*k)).take 24=r.encode := by
  induction rs generalizing k with
  | nil => simp at h
  | cons x rs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at h
      subst r
      simp only [List.map_cons,concatAll,List.append_assoc,Nat.mul_zero,List.drop_zero]
      rw [←link_length x,List.take_left]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hd : 24*(k+1)=x.encode.length+24*k := by rw [link_length]; omega
      simp only [List.map_cons,concatAll,List.append_assoc,hd,List.drop_length_add_append]
      exact ih k h

/-- Exact authenticated original position of each decoded record. -/
theorem decoded_record_slice (bs : Bytes) (st : State) (h : State.decode bs=some st)
    (k : Nat) (r : LinkAllowance) (hk : st.links[k]?=some r) :
    (bs.drop (5+24*k)).take 24=r.encode := by
  have he:bs=st.encode := (decode_exact bs st h).2.2.2
  rw [he]
  have hh:([0]++u32 st.links.length).length=5 := by simp [u32,canon_leN_length]
  change ((([0]++u32 st.links.length)++concatAll (st.links.map LinkAllowance.encode)++st.sanityHash).drop (5+24*k)).take 24=r.encode
  rw [List.append_assoc,←hh,List.drop_length_add_append]
  exact record_slice st.links st.sanityHash k r hk

/-- A duplicate shard ID maps to its first index, while a later record wins. -/
theorem duplicate_first_last :
    ProcActualInput.allowances [7,7] ⟨[⟨7,7,3⟩,⟨99,7,11⟩,⟨7,7,9⟩],List.replicate 32 0⟩ = #[9,0,0,0] := by
  decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorBytes
