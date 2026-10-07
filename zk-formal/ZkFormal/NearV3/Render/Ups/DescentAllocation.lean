import ZkFormal.NearV3.Render.Ups.TreeDescents

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Count the proper ancestors still to be processed at this bottom-up part. -/
def remainingDescents (parts : List TreePart) (index : Nat) : Nat := descentCount (parts.drop index)

theorem remainingDescents_step : ∀ (parts : List TreePart) (k : Nat) (part : TreePart),
    parts[k]?=some part → remainingDescents parts (k+1)+(if descendKind part.kind then 1 else 0)=
      remainingDescents parts k
  | [], _, _, h => by simp at h
  | p::ps, 0, part, h => by
    simp at h; subst part
    cases hd : descendKind p.kind <;> simp [remainingDescents,descentCount,hd]
  | p::ps, k+1, part, h => by
    simpa [remainingDescents] using remainingDescents_step ps k part h

theorem remainingDescents_le : ∀ (parts : List TreePart) (k : Nat),
    remainingDescents parts k≤descentCount parts
  | [], k => by simp [remainingDescents,descentCount]
  | p::ps, 0 => by simp [remainingDescents]
  | p::ps, k+1 => by
    have ih := remainingDescents_le ps k
    cases hd : descendKind p.kind <;> simp [remainingDescents,descentCount,hd] at ih ⊢ <;> omega

theorem remainingDescents_root (parts : List TreePart) (part : TreePart)
    (h : parts[parts.length-1]?=some part) :
    remainingDescents parts (parts.length-1)=(if descendKind part.kind then 1 else 0) := by
  have hn : 0<parts.length := by cases parts <;> simp_all
  have hs := remainingDescents_step parts (parts.length-1) part h
  have he : parts.length-1+1=parts.length := by omega
  simpa [he,remainingDescents,descentCount] using hs.symm

/-- Source-level metadata is computed from proper native descents, independently
of pass-through depth and record IDs. -/
def withDescentPosition (parts : List TreePart) (index : Nat) (part : UpsPartI) : UpsPartI :=
  let rc := remainingDescents parts index
  {part with
    rc := rc
    sd := if part.kind=0 ∨ part.kind=1 then rc-1 else descentCount parts}

theorem allocated_descent_bound {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) (k : Nat) (part : UpsPartI) :
    (withDescentPosition run.parts k part).sd<3 := by
  have hD := fixed_trace_descents hr
  have hrc := remainingDescents_le run.parts k
  simp only [withDescentPosition]
  split <;> omega

theorem allocated_descent_source (parts : List TreePart) (k : Nat) (Q : UpsPartI)
    (part : TreePart) (hk : parts[k]?=some part) (he : Q.kind=part.kind.ix)
    (hd : Q.kind=0 ∨ Q.kind=1) :
    (withDescentPosition parts k Q).sd+1=(withDescentPosition parts k Q).rc := by
  have hb : descendKind part.kind=true := by
    cases hc : part.kind <;> simp_all [UKind.ix,descendKind]
  have hs := remainingDescents_step parts k part hk
  simp only [hb,ite_true] at hs
  simp [withDescentPosition,hd]
  omega

theorem allocated_terminal_source (parts : List TreePart) (k : Nat) (Q : UpsPartI)
    (hk : 2≤Q.kind) : (withDescentPosition parts k Q).sd=descentCount parts := by
  simp [withDescentPosition,show ¬(Q.kind=0 ∨ Q.kind=1) by omega]
end ZkFormal.NearV3.Render.UpsGen
