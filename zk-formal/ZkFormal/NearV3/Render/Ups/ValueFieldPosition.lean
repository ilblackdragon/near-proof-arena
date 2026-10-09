import ZkFormal.NearV3.Render.Ups.UniqueFieldPosition
import ZkFormal.NearV3.Render.Ups.MemPosition

namespace ZkFormal.NearV3.Render.UpsGen

def valuePrefix (ty hk : Nat) : List (Nat × Nat) := [(0,1)] ++
  (if ty=0 then [(1,4),(2,1)] ++ (if 1<hk then [(3,hk-1)] else []) else [])

def valueSuffix (ty n : Nat) : List (Nat × Nat) := [(5,32)] ++
  (if ty=3 then [(6,2)] else []) ++ List.replicate n (7,32) ++ [(8,8)]

theorem valuePrefix_avoid (ty hk : Nat) : ∀ f ∈ valuePrefix ty hk, f.1 ≠ 4 := by
  by_cases h1 : ty=0 <;> by_cases h2 : 1<hk <;> simp [valuePrefix,h1,h2]

theorem valueSuffix_avoid (ty n : Nat) : ∀ f ∈ valueSuffix ty n, f.1 ≠ 4 := by
  by_cases ht : ty=3 <;> simp [valueSuffix,ht] <;> intro a b h <;> omega

theorem FieldsOk.vlen_position {Q : UpsPartI} (f : FieldsOk Q) {p : Nat}
    (ht : Q.ty=0 ∨ Q.ty=3) (hs : (fieldAt Q.shape p).1=4) :
    p = (if Q.ty=0 then 5+Q.qhk else 1) + (fieldAt Q.shape p).2.1 := by
  have he : Q.shape=valuePrefix Q.ty Q.qhk ++ (4,4)::valueSuffix Q.ty (nWin Q.shape) := by
    calc Q.shape = nodeFields Q.ty Q.qhk (nWin Q.shape) := f.shape
         _ = _ := by rcases ht with ht | ht <;> simp [nodeFields,valuePrefix,valueSuffix,ht,List.append_assoc]
  have hp := unique_field_position (valuePrefix Q.ty Q.qhk) (valueSuffix Q.ty (nWin Q.shape)) 4 4 p
    (by decide) (valuePrefix_avoid _ _) (valueSuffix_avoid _ _) (by rw [← he]; exact hs)
  rw [← he] at hp
  have hl : fieldsLen (valuePrefix Q.ty Q.qhk) = if Q.ty=0 then 5+Q.qhk else 1 := by
    by_cases hty : Q.ty=0
    · have hk := f.prefixLength (by omega)
      by_cases hh : 1<Q.qhk <;> simp [valuePrefix,hty,hh,fieldsLen_append] <;> omega
    · simp [valuePrefix,hty]
  rw [hl] at hp
  exact hp

end ZkFormal.NearV3.Render.UpsGen
