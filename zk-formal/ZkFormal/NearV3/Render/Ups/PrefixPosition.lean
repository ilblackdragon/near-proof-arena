import ZkFormal.NearV3.Render.Ups.NodeFieldsBridge

namespace ZkFormal.NearV3.Render.UpsGen

theorem fieldAt_avoid (target : Nat) (ht : 9 ≠ target) (sh : List (Nat × Nat))
    (h : ∀ f ∈ sh, f.1 ≠ target) (p : Nat) : (fieldAt sh p).1 ≠ target := by
  induction sh generalizing p with
  | nil => simpa [fieldAt] using ht
  | cons f fs ih =>
    by_cases hp : p < f.2
    · simp [fieldAt,hp,h f (by simp)]
    · simpa [fieldAt,hp] using ih (fun f hf => h f (by simp [hf])) (p-f.2)

def afterPrefix (ty hk n : Nat) : List (Nat × Nat) :=
  (if 1<hk then [(3,hk-1)] else []) ++
  (if ty=0 ∨ ty=3 then [(4,4),(5,32)] else []) ++
  (if 2≤ty then [(6,2)] else []) ++ List.replicate n (7,32) ++ [(8,8)]

theorem afterPrefix_avoid (ty hk n : Nat) : ∀ f ∈ afterPrefix ty hk n, f.1 ≠ 2 := by
  by_cases h1 : 1<hk <;> by_cases h2 : ty=0 ∨ ty=3 <;> by_cases h3 : 2≤ty <;>
    simp [afterPrefix,h1,h2,h3] <;> intro a b h <;> omega

theorem FieldsOk.hpf_position {Q : UpsPartI} (f : FieldsOk Q) {p : Nat}
    (ht : Q.ty ≤ 1) (hs : (fieldAt Q.shape p).1=2) : p=5 := by
  have he : Q.shape = (0,1)::(1,4)::(2,1)::afterPrefix Q.ty Q.qhk (nWin Q.shape) := by
    calc Q.shape = nodeFields Q.ty Q.qhk (nWin Q.shape) := f.shape
         _ = _ := by simp [nodeFields,afterPrefix,ht,List.append_assoc]
  have hz := fieldAt_avoid 2 (by decide) _ (afterPrefix_avoid Q.ty Q.qhk (nWin Q.shape)) (p-1-4-1)
  rw [he] at hs
  simp only [fieldAt,Nat.reduceEqDiff,ite_false,Nat.add_zero] at hs
  split at hs
  · simp at hs
  · split at hs
    · simp at hs
    · split at hs
      · omega
      · exact False.elim (hz hs)

end ZkFormal.NearV3.Render.UpsGen
