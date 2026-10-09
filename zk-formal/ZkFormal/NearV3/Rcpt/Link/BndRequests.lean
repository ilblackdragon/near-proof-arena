import ZkFormal.NearV3.Rcpt.Link.BndProvider
import ZkFormal.NearV3.Rcpt.Link.NativeEncoding

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

def boundaryRequests (ls : RcptV3Vs) : List (Msg × Nat) :=
  (flatR ls).flatMap fun x => x.rlk.map fun (p,l,h,hn,u) => ([65*x.q+p,l,h,hn],u)

theorem view_route_bounds {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    {x : RcptE} (hx : x∈flatR ls) : RouteOk x ∧ x.v.length≤64 := by
  obtain ⟨toks,_,_,hw,_⟩ := h.toks
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hh := hw i hi
  rw [he] at hh
  have hl := (valid_length hh.ids.2.1).2
  exact ⟨hh.route,by simpa only [toBytes_length] using hl⟩

private theorem flatMap_length_bound {α β : Type} (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x∈xs,(f x).length≤n) : (xs.flatMap f).length≤n*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- All receipt routing requests together are too few to form a provider-free
BabyBear cycle, from the actual extracted receipt-count bound. -/
theorem boundaryRequests_bound {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hn : (flatR ls).length≤2^22) : (boundaryRequests ls).length<P := by
  have hh := flatMap_length_bound (flatR ls)
    (fun x => x.rlk.map fun (p,l,h,hn,u) => ([65*x.q+p,l,h,hn],u)) 65 (by
      intro x hx
      have hb := view_route_bounds h hx
      simp only [List.length_map]
      have hl := hb.1.len.2
      omega)
  change (boundaryRequests ls).length≤65*(flatR ls).length at hh
  unfold P
  omega

/-- Canonical BND request keys from extracted receipt facts and the repaired
seven-bit interval-index property. No such property is assumed of the old table. -/
theorem boundaryRequests_canonical {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hq : ∀ x∈flatR ls,x.q<128) :
    ∀ r∈boundaryRequests ls,r.1.length=4 ∧ Canon r.1 ∧ r.2<P := by
  intro r hr
  obtain ⟨x,hx,he⟩ := List.mem_flatMap.mp hr
  obtain ⟨e,hem,rfl⟩ := List.mem_map.mp he
  rcases e with ⟨pos,lo,hi,hn,u⟩
  have hb := view_route_bounds h hx
  have hp : pos∈List.range x.rlk.length := by
    rw [←hb.1.pos]
    exact List.mem_map.mpr ⟨(pos,lo,hi,hn,u),hem,rfl⟩
  have hpl := List.mem_range.mp hp
  have hll := hb.1.len.2
  have hq' := hq x hx
  have hc : ∀ a∈[pos,lo,hi,hn,u],a<P := by
    intro a ha
    apply h.canon.2 x hx a
    apply List.mem_append.mpr
    right
    exact List.mem_flatMap.mpr ⟨(pos,lo,hi,hn,u),hem,ha⟩
  refine ⟨rfl,?_,hc u (by simp)⟩
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  · unfold P
    omega
  · exact hc a (by simp)
  · exact hc a (by simp)
  · exact hc a (by simp)

end ZkFormal.NearV3.RcptLink
