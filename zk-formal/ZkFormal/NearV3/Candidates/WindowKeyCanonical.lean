import ZkFormal.NearV3.Candidates.PhysicalWindowBalance
import ZkFormal.NearV3.Candidates.NativePostBytes

namespace ZkFormal.NearV3.Candidates.WindowKeyCanonical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

private theorem getD_small (xs : List Nat) (h : ∀x∈xs,x<P) (p : Nat) : xs.getD p 0<P := by
  cases he : xs[p]? with
  | none => simp [List.getD_eq_getElem?_getD,he];decide
  | some x => simpa [List.getD_eq_getElem?_getD,he] using h x (List.mem_of_getElem? he)

private theorem mem_le_sum {x : Nat} {xs : List Nat} (h : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · have := ih h; simp only [List.sum_cons];omega

/-- The full natural provider key is canonical. The byte hypothesis is supplied
by the actual native serialization, not by an assumption of hash injectivity. -/
theorem small {vs : List NodeS3} (hw : NodeWf3 vs) {s : NodeS3} {n p : Nat}
    (hs : vs[n]?=some s) (hp : p<(s.v.ser false).length)
    (hb : ∀x∈s.v.ser true,x<256) : ∀x∈windowKey n p s,x<P := by
  have hm:=List.mem_of_getElem? hs
  have hn:= (List.getElem?_eq_some_iff.mp hs).1
  have hlen : (s.v.ser false).length≤(vs.map (fun s=> (s.v.ser false).length)).sum :=
    mem_le_sum (List.mem_map.mpr ⟨s,hm,rfl⟩)
  have hc:=hw.count
  have hr:=hw.rows
  have hd:=(hw.small s hm).2.1
  have hu:=getD_small s.ucid (hw.upbSmall s hm).1 p
  have hb': (s.v.ser true).getD p 0<P := getD_small _ (fun x hx=>by have:=hb x hx;unfold P;omega) p
  have hi : msgId K_NPOST n<P := by unfold msgId K_NPOST P;omega
  have hp' : p<P := by unfold P;omega
  have hl' : (s.v.ser false).length<P := by unfold P;omega
  intro x hx
  simp only [windowKey,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hi
  · exact hp'
  · exact hb'
  · exact hl'
  · exact hd
  · exact hu

/-- Actual initialized, updated native forest bytes discharge the key-byte
premise, retaining original provider metadata and global occurrence indices. -/
theorem native_small (ts : List NearSpec.PTrie) (ht : ∀t∈ts,t.wf=true)
    (cs : List StoreDuplicateChain.Entry) (u : Inputs) (q : UseRequests)
    (hw : NodeWf3 (assignList q 0 (records u (ChainMetadata.assign cs 0
      (initializeList 0 (Assembly.forestNodes 0 0 0 ts))))))
    {s : NodeS3} {n p : Nat}
    (hs : (assignList q 0 (records u (ChainMetadata.assign cs 0
      (initializeList 0 (Assembly.forestNodes 0 0 0 ts)))))[n]?=some s)
    (hp : p<(s.v.ser false).length) : ∀x∈windowKey n p s,x<P :=
  small hw hs hp (NativePostBytes.updated_bytes ts ht cs u q s (List.mem_of_getElem? hs) true)

/-- Equality of the physical key fields identifies the original natural key,
without field-wrap ambiguity. -/
theorem physical_eq {vs : List NodeS3} (hw : NodeWf3 vs) {s : NodeS3} {n p : Nat}
    (hs : vs[n]?=some s) (hp : p<(s.v.ser false).length)
    (hb : ∀x∈s.v.ser true,x<256) (tr : Trace Fp) (t r : Nat)
    (he : windowFieldKey tr t r=(windowKey n p s).map Fp.ofNat) :
    physicalWindowKey tr t r=windowKey n p s := by
  rw [physicalWindowKey,he,List.map_map]
  conv => rhs; rw [←List.map_id (windowKey n p s)]
  apply List.map_congr_left
  intro x hx
  simpa only [Function.comp_def,id_eq,Fp.toNat_ofNat] using Nat.mod_eq_of_lt (small hw hs hp hb x hx)

end ZkFormal.NearV3.Candidates.WindowKeyCanonical
