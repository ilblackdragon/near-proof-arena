import ZkFormal.NearV3.Candidates.ProcActualNativeResult
import ZkFormal.NearV3.Sched.Spec.Canon
namespace ZkFormal.NearV3.Candidates.ProcNativeGrantLookup
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched

/-- First-match lookup is exact when every matching key has the same value. -/
theorem find_value (xs : List ((Nat×Nat)×Nat)) (key : Nat×Nat) (v : Nat)
    (hex : ∃x∈xs,x.1=key) (hv : ∀x∈xs,x.1=key → x.2=v) :
    ((xs.find? (·.1==key)).map Prod.snd).getD 0=v := by
  induction xs with
  | nil => simp at hex
  | cons x xs ih =>
    by_cases hx : x.1=key
    · simpa [List.find?_cons,hx] using hv x (by simp) hx
    · have ht : ∃y∈xs,y.1=key := by
        obtain ⟨y,hy,he⟩ := hex
        rcases List.mem_cons.mp hy with rfl|hy
        · exact False.elim (hx he)
        · exact ⟨y,hy,he⟩
      simpa [List.find?_cons,hx] using ih ht (fun y hy=>hv y (by simp [hy]))

/-- A canonical current-layout pair determines one sender-major link index. -/
theorem link_index (ids : List Nat) (hd : ids.Nodup) (a b o r l : Nat)
    (ho : indexOf ids a=some o) (hr : indexOf ids b=some r) (hl : l<ids.length*ids.length)
    (he : (ids.getD (l/ids.length) 0,ids.getD (l%ids.length) 0)=(a,b)) :
    l=o*ids.length+r := by
  have hn : 0<ids.length := by have hh := (indexOf_spec ho).1; omega
  have hlo : l/ids.length<ids.length := (Nat.div_lt_iff_lt_mul hn).mpr hl
  have hlr : l%ids.length<ids.length := Nat.mod_lt _ hn
  have ha := indexOf_nodup hd hlo
  have hb := indexOf_nodup hd hlr
  have he1 : ids.getD (l/ids.length) 0=a := congrArg Prod.fst he
  have he2 : ids.getD (l%ids.length) 0=b := congrArg Prod.snd he
  rw [he1] at ha
  rw [he2] at hb
  have hio : l/ids.length=o := Option.some.inj (ha.symm.trans ho)
  have hir : l%ids.length=r := Option.some.inj (hb.symm.trans hr)
  have hh := Nat.mod_add_div l ids.length
  rw [hio,hir] at hh
  simpa [Nat.mul_comm,Nat.add_comm] using hh.symm

theorem mapped_lookup (ids : List Nat) (hd : ids.Nodup) (grants : Array Nat)
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
  have hdiv : (o*ids.length+r)/ids.length=o := by rw [Nat.add_comm,Nat.add_mul_div_right r o hn,Nat.div_eq_of_lt hrb,Nat.zero_add]
  have hmod : (o*ids.length+r)%ids.length=r := by simp [Nat.add_mod,Nat.mod_eq_of_lt hrb]
  apply find_value
  · refine ⟨((a,b),grants[o*ids.length+r]!),?_,rfl⟩
    apply List.mem_map.mpr
    exact ⟨o*ids.length+r,List.mem_range.mpr hl,by simp only [hdiv,hmod,hea,heb]⟩
  · intro x hx he
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hx
    have hi := link_index ids hd a b o r l ho hr (List.mem_range.mp hl) he
    simp only [hi]

theorem finish_lookup (sp : SchedPub) (prev : Bandwidth.State) (st : St)
    (hd : sp.ids.Nodup) (a b o r : Nat)
    (ho : indexOf sp.ids a=some o) (hr : indexOf sp.ids b=some r) :
    ((((ProcActualNativeResult.finish sp prev st).granted.find? (·.1==(a,b))).map Prod.snd).getD 0)=
      (distribute sp.ids.length sp.allowed st).granted[o*sp.ids.length+r]! :=
  mapped_lookup sp.ids hd _ a b o r ho hr
end ZkFormal.NearV3.Candidates.ProcNativeGrantLookup
