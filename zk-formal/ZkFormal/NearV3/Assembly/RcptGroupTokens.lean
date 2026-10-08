import ZkFormal.NearV3.Assembly.RcptCanonicalNativeEncoding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton

universe u
variable {α : Type u}

/-- None marks a physical list header; Some carries one receipt occurrence. -/
def groupTokenStep : Option α→List (List α)→List (List α)
  | none,ys=>[]::ys
  | some x,[]=>[[x]]
  | some x,y::ys=>(x::y)::ys

def decodeGroups (xs : List (Option α)) : List (List α) :=
  (xs.foldr groupTokenStep [[]]).tail

def groupTokens (xs : List α) : List (Option α) := none::xs.map some

theorem some_tokens_fold (xs first : List α) (rest : List (List α)) :
    (xs.map some).foldr groupTokenStep (first::rest)=(xs++first)::rest := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.foldr_cons,ih,groupTokenStep,List.cons_append]

theorem groups_tokens_fold (ls : List (List α)) :
    (ls.flatMap groupTokens).foldr groupTokenStep [[]]=[]::ls := by
  induction ls with
  | nil => rfl
  | cons xs ls ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,groupTokens,List.foldr_cons,
      some_tokens_fold,List.append_nil,groupTokenStep]

/-- Exact grouping, including empty groups and repeated receipt values. -/
theorem decode_group_tokens (ls : List (List α)) :
    decodeGroups (ls.flatMap groupTokens)=ls := by
  rw [decodeGroups,groups_tokens_fold]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
