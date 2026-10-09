import ZkFormal.NearV3.Candidates.ProcNativeForwardSize
namespace ZkFormal.NearV3.Candidates.ProcNativeForwardFold
open NearSpec NearSpecV3 ProcNativeForwardSize

theorem append (ctx : ApplyCtx) (a b : List Receipt) (ls : List Limit) :
    forwardAll ctx ls (a++b) = (forwardAll ctx ls a).bind (fun mid=>forwardAll ctx mid b) := by
  induction a generalizing ls with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.cons_append,forwardAll]
    cases h : tryForward ctx ls r with
    | none => rfl
    | some mid => exact ih mid

def step (ctx : ApplyCtx) (ls : List Limit) (r : Receipt) : Except String (List Limit) :=
  match tryForward ctx ls r with
  | some out => .ok out
  | none => .error "out of domain (e.forwarded): generated receipt buffered"

theorem fold_success (ctx : ApplyCtx) (rs : List Receipt) (ls out : List Limit)
    (h : rs.foldlM (step ctx) ls=.ok out) : forwardAll ctx ls rs=some out := by
  induction rs generalizing ls with
  | nil => simpa [forwardAll,pure,Except.pure] using h
  | cons r rs ih =>
    simp only [List.foldlM_cons,step] at h
    cases he : tryForward ctx ls r with
    | none => simp [he,bind,Except.bind] at h
    | some mid =>
      simp only [he,bind,Except.bind] at h
      simpa only [forwardAll,he,Option.bind_some] using ih mid h
end ZkFormal.NearV3.Candidates.ProcNativeForwardFold
