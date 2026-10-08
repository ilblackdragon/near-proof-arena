import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteLookup

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec

inductive WriteSlotPair : Slot→Slot→Prop
  | ref (n : Nat) (h : Bytes) : WriteSlotPair (.ref n h) (.ref n h)
  | val (a b : Bytes) : WriteSlotPair (.val a) (.val b)

mutual
/-- Exact native shape relation: only revealed value bytes may differ. -/
inductive WriteTreePair : PTrie→PTrie→Prop
  | hash (h : Bytes) : WriteTreePair (.hash h) (.hash h)
  | leaf {a b : Slot} (k : List Nat) (m : Nat) (h : WriteSlotPair a b) :
      WriteTreePair (.leaf k a m) (.leaf k b m)
  | ext {a b : PTrie} (k : List Nat) (m : Nat) (h : WriteTreePair a b) :
      WriteTreePair (.ext k a m) (.ext k b m)
  | branch {a b : Option Slot} {cs ds : Kids} (m : Nat)
      (h : Option.Rel WriteSlotPair a b) (hs : WriteKidsPair cs ds) :
      WriteTreePair (.branch a cs m) (.branch b ds m)
inductive WriteKidsPair : Kids→Kids→Prop
  | nil : WriteKidsPair .nil .nil
  | none {cs ds : Kids} (h : WriteKidsPair cs ds) : WriteKidsPair (.none cs) (.none ds)
  | some {a b : PTrie} {cs ds : Kids} (h : WriteTreePair a b) (hs : WriteKidsPair cs ds) :
      WriteKidsPair (.some a cs) (.some b ds)
end

theorem WriteSlotPair.refl (s : Slot) : WriteSlotPair s s := by
  cases s <;> constructor

mutual
theorem WriteTreePair.refl : ∀t : PTrie,WriteTreePair t t
  | .hash h => .hash h
  | .leaf k s m => .leaf k m (WriteSlotPair.refl s)
  | .ext k c m => .ext k m (WriteTreePair.refl c)
  | .branch v cs m => .branch m (by cases v with
      | none => exact .none
      | some s => exact .some (WriteSlotPair.refl s)) (WriteKidsPair.refl cs)
theorem WriteKidsPair.refl : ∀cs : Kids,WriteKidsPair cs cs
  | .nil => .nil
  | .none cs => .none (WriteKidsPair.refl cs)
  | .some c cs => .some (WriteTreePair.refl c) (WriteKidsPair.refl cs)
end

mutual
theorem native_set_pair : ∀(t : PTrie)(key : List Nat)(nv : Bytes)(out : PTrie),
    t.set key nv=some out → WriteTreePair t out
  | .hash _,_,_,_,h => by simp [PTrie.set] at h
  | .leaf k s m,key,nv,out,h => by
    simp only [PTrie.set] at h
    split at h
    · cases s with
      | ref n hh => simp [Slot.get] at h
      | val b =>
        simp only [Slot.get,Option.map_some,Option.some.injEq] at h
        subst out
        exact .leaf k m (.val b nv)
    · cases h
  | .ext k c m,key,nv,out,h => by
    simp only [PTrie.set] at h
    split at h
    · cases hs : c.set (key.drop k.length) nv with
      | none => simp [hs] at h
      | some post =>
        simp only [hs,Option.map_some,Option.some.injEq] at h
        subst out
        exact .ext k m (native_set_pair c _ nv post hs)
    · cases h
  | .branch v cs m,[],nv,out,h => by
    simp only [PTrie.set] at h
    split at h <;> simp at h
    subst out
    exact .branch m (.some (.val _ nv)) (WriteKidsPair.refl cs)
  | .branch v cs m,n::key,nv,out,h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n key nv with
    | none => simp [hs] at h
    | some ds =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst out
      exact .branch m (by cases v with
        | none => exact .none
        | some s => exact .some (WriteSlotPair.refl s)) (native_set_kids_pair cs n key nv ds hs)
theorem native_set_kids_pair : ∀(cs : Kids)(n : Nat)(key : List Nat)(nv : Bytes)(out : Kids),
    Kids.set cs n key nv=some out → WriteKidsPair cs out
  | .nil,_,_,_,_,h => by simp [Kids.set] at h
  | .none _,0,_,_,_,h => by simp [Kids.set] at h
  | .some c cs,0,key,nv,out,h => by
    simp only [Kids.set] at h
    cases hs : c.set key nv with
    | none => simp [hs] at h
    | some post =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst out
      exact .some (native_set_pair c key nv post hs) (WriteKidsPair.refl cs)
  | .none cs,n+1,key,nv,out,h => by
    simp only [Kids.set] at h
    cases hs : Kids.set cs n key nv with
    | none => simp [hs] at h
    | some ds =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst out
      exact .none (native_set_kids_pair cs n key nv ds hs)
  | .some c cs,n+1,key,nv,out,h => by
    simp only [Kids.set] at h
    cases hs : Kids.set cs n key nv with
    | none => simp [hs] at h
    | some ds =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst out
      exact .some (WriteTreePair.refl c) (native_set_kids_pair cs n key nv ds hs)
end

theorem WriteSlotPair.trans {a b c : Slot} (h : WriteSlotPair a b) (g : WriteSlotPair b c) :
    WriteSlotPair a c := by cases h <;> cases g <;> constructor

mutual
theorem WriteTreePair.trans {a b c : PTrie} : WriteTreePair a b → WriteTreePair b c → WriteTreePair a c
  | .hash h,.hash _ => .hash h
  | .leaf k m h,.leaf _ _ g => .leaf k m (h.trans g)
  | .ext k m h,.ext _ _ g => .ext k m (h.trans g)
  | .branch m h hs,.branch _ g gs => .branch m (by
      cases h with
      | none => cases g; exact .none
      | some h => cases g with | some g => exact .some (h.trans g)) (hs.trans gs)
theorem WriteKidsPair.trans {a b c : Kids} : WriteKidsPair a b → WriteKidsPair b c → WriteKidsPair a c
  | .nil,.nil => .nil
  | .none h,.none g => .none (h.trans g)
  | .some h hs,.some g gs => .some (h.trans g) (hs.trans gs)
end

theorem AccountWriteRun.skeleton {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) : WriteTreePair pre post := by
  induction h with
  | nil t => exact WriteTreePair.refl t
  | cons hs _ ih => exact (native_set_pair _ _ _ _ hs).trans ih

end ZkFormal.NearV3.Rcpt.Candidates
