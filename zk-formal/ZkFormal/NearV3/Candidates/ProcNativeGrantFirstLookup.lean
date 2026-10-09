import ZkFormal.NearV3.Candidates.ProcNativeGrantLookup
namespace ZkFormal.NearV3.Candidates.ProcNativeGrantFirstLookup
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched

/-- Successful indexOf chooses no later than any occurrence, including duplicates. -/
theorem index_go_min (x : Nat) (ids : List Nat) (start i j : Nat)
    (h : indexOf.go x ids start=some i) (hj : ids[j]?=some x) : i≤start+j := by
  induction ids generalizing start j with
  | nil => simp [indexOf.go] at h
  | cons y ys ih =>
    simp only [indexOf.go] at h
    split at h
    · simp only [Option.some.injEq] at h; omega
    · rename_i hy
      cases j with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hj; exact False.elim (hy hj)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        have hh := ih (start+1) j h hj
        omega

theorem index_min (ids : List Nat) (x i j : Nat) (h : indexOf ids x=some i)
    (hj : ids[j]?=some x) : i≤j := by
  simpa using index_go_min x ids 0 i j h hj

/-- In an increasing range, the earliest matching record is selected. -/
theorem find_range (f : Nat → ((Nat×Nat)×Nat)) (key : Nat×Nat)
    (start len k : Nat) (hk : start≤k) (hb : k<start+len)
    (he : (f k).1=key) (hmin : ∀j,start≤j → j<k → (f j).1≠key) :
    (((List.range' start len).map f).find? (·.1==key))=some (f k) := by
  induction len generalizing start with
  | zero => omega
  | succ len ih =>
    rw [List.range'_succ,List.map_cons,List.find?_cons]
    by_cases hs : start=k
    · subst start; simp [he]
    · have hn := hmin start (by omega) (by omega)
      simp only [show ((f start).1==key)=false from beq_eq_false_iff_ne.mpr hn]
      apply ih (start+1) (by omega) (by omega) (fun j hj hjk=>hmin j (by omega) hjk)

/-- Duplicate shard IDs preserve first-match semantics: the earliest pair is
the pair of the first sender and first receiver occurrences. -/
theorem mapped_lookup (ids : List Nat) (grants : Array Nat)
    (a b o r : Nat) (ho : indexOf ids a=some o) (hr : indexOf ids b=some r) :
    ((((List.range (ids.length*ids.length)).map fun l=>
      ((ids.getD (l/ids.length) 0,ids.getD (l%ids.length) 0),grants[l]!)).find?
        (·.1==(a,b))).map Prod.snd).getD 0=grants[o*ids.length+r]! := by
  have hob := (indexOf_spec ho).1
  have hrb := (indexOf_spec hr).1
  have hn : 0<ids.length := by omega
  have hl : o*ids.length+r<ids.length*ids.length := by
    have hm := Nat.mul_le_mul_right ids.length (show o+1≤ids.length by omega)
    rw [Nat.add_mul] at hm
    simp only [Nat.one_mul] at hm
    omega
  have hea : ids.getD o 0=a := by simp [List.getD_eq_getElem?_getD,(indexOf_spec ho).2]
  have heb : ids.getD r 0=b := by simp [List.getD_eq_getElem?_getD,(indexOf_spec hr).2]
  have hdiv : (o*ids.length+r)/ids.length=o := by
    rw [Nat.add_comm,Nat.add_mul_div_right r o hn,Nat.div_eq_of_lt hrb,Nat.zero_add]
  have hmod : (o*ids.length+r)%ids.length=r := by simp [Nat.add_mod,Nat.mod_eq_of_lt hrb]
  let f := fun l=>((ids.getD (l/ids.length) 0,ids.getD (l%ids.length) 0),grants[l]!)
  have hfirst := find_range f (a,b) 0 (ids.length*ids.length) (o*ids.length+r) (by omega)
    (by omega) (by simp only [f,hdiv,hmod,hea,heb]) ?_
  · change ((((List.range (ids.length*ids.length)).map f).find? (·.1==(a,b))).map Prod.snd).getD 0 = _
    rw [List.range_eq_range',hfirst]
    rfl
  · intro j hj hjk he
    have hjn : j<ids.length*ids.length := by omega
    have hjo : j/ids.length<ids.length := (Nat.div_lt_iff_lt_mul hn).mpr hjn
    have hjr : j%ids.length<ids.length := Nat.mod_lt _ hn
    have hja : ids.getD (j/ids.length) 0=a := congrArg Prod.fst he
    have hjb : ids.getD (j%ids.length) 0=b := congrArg Prod.snd he
    have hja' : ids[j/ids.length]?=some a := by
      rw [List.getElem?_eq_getElem hjo]
      simpa [List.getD_eq_getElem?_getD,hjo] using congrArg some hja
    have hjb' : ids[j%ids.length]?=some b := by
      rw [List.getElem?_eq_getElem hjr]
      simpa [List.getD_eq_getElem?_getD,hjr] using congrArg some hjb
    have hmo := index_min ids a o _ ho hja'
    have hmr := index_min ids b r _ hr hjb'
    have hm := Nat.mul_le_mul_right ids.length hmo
    have hdecomp := Nat.mod_add_div j ids.length
    rw [Nat.mul_comm ids.length] at hdecomp
    omega

theorem finish_lookup (sp : SchedPub) (prev : Bandwidth.State) (st : St)
    (a b o r : Nat) (ho : indexOf sp.ids a=some o) (hr : indexOf sp.ids b=some r) :
    ((((ProcActualNativeResult.finish sp prev st).granted.find? (·.1==(a,b))).map Prod.snd).getD 0)=
      (distribute sp.ids.length sp.allowed st).granted[o*sp.ids.length+r]! :=
  mapped_lookup sp.ids _ a b o r ho hr
end ZkFormal.NearV3.Candidates.ProcNativeGrantFirstLookup
