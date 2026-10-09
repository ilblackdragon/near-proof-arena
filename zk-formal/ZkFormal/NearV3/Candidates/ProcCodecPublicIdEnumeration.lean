import ZkFormal.NearV3.Candidates.ProcCodecPublicIdPhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecPublicIdEnumeration

theorem flat_congr {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  simp only [List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left h)

theorem blocks {α : Type} (s w k : Nat) (f : Nat→List α) :
    (List.range' s (w*k)).flatMap f=
      (List.range k).flatMap (fun j=>(List.range' (s+w*j) w).flatMap f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,←List.range'_append_1,List.flatMap_append,ih,List.range_succ,List.flatMap_append]
    simp

theorem sampled {α : Type} (n : Nat) (hn : 0<n) (msg : Nat→α) :
    (List.range (n*n)).flatMap (fun k=>if k%n=0 then [msg (k/n)] else [])=
      (List.range n).map msg := by
  rw [List.range_eq_range',blocks]
  have he : ∀s∈List.range n,
      (List.range' (0+n*s) n).flatMap (fun k=>if k%n=0 then [msg (k/n)] else [])=[msg s] := by
    intro s hs
    rw [List.range'_eq_map_range,List.flatMap_map]
    have hh : (List.range n).flatMap (fun x=>if (0+n*s+x)%n=0 then [msg ((0+n*s+x)/n)] else [])=
        (List.range n).flatMap (fun x=>if x=0 then [msg s] else []) := by
      apply flat_congr
      intro x hx
      have hxn:=List.mem_range.mp hx
      simp only [Nat.zero_add,Nat.mul_add_mod,Nat.mod_eq_of_lt hxn,Nat.mul_add_div hn,Nat.div_eq_of_lt hxn,Nat.add_zero]
    rw [hh]
    exact ProcRawPresencePhysical.singleton_range n hn (msg s)
  rw [flat_congr _ _ _ he]
  have hm : ∀xs : List Nat,xs.flatMap (fun s=>[msg s])=xs.map msg := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact hm _

/-- A record has24 physical bytes; exactly its first row may emit. -/
theorem one_record {α : Type} (base : Nat) (G : Nat→List α) (a : List α)
    (h : ∀j<24,G (base+j)=if j=0 then a else []) :
    (List.range' base 24).flatMap G=a := by
  rw [List.range'_succ,List.flatMap_cons]
  have h0:=h 0 (by decide)
  simp only [Nat.add_zero,ite_true] at h0
  rw [h0]
  have hz : (List.range' (base+1) 23).flatMap G=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hh:=List.mem_range'.mp hr
    have he:r=base+(r-base) := by omega
    rw [he,h (r-base) (by omega),ite_eq_right (by omega)]
  rw [hz,List.append_nil]
end ZkFormal.NearV3.Candidates.ProcCodecPublicIdEnumeration
