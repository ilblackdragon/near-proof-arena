import ZkFormal.NearV3.Rcpt.Link.PreparedOwner

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- Every emitted byte retains its full natural message ID. -/
theorem emitAt_head_eq {id off a : Nat} {xs : List Nat} {m : Msg}
    (hm : m∈emitAt id off xs) (ha : m.head?=some a) : a=id := by
  simp only [emitAt,List.mem_map,List.mem_range] at hm
  obtain ⟨j,hj,rfl⟩ := hm
  simpa only [List.head?_cons,Option.some.injEq] using ha.symm

/-- Of the receipt byte streams, only the RC stream has the RC message kind. -/
theorem receipt_sends_rc {pub : List Fp} {xs : List RcptE} {j r off a : Nat} {x : RcptE} {m : Msg}
    (hm : m∈rSends pub xs j r off x B_BYTES) (ha : m.head?=some a) (hk : a%16=K_RC) :
    m∈emitAt (msgId K_RC j) off x.enc := by
  simp only [rSends,ite_true,List.mem_append] at hm
  rcases hm with (((hm|hm)|hm)|hm)|hm
  · exact hm
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [K_RF,K_RC] at hk
    · simp at hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId,K_PEO,K_RC,Nat.add_mod] at hk
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId,K_LEAF,K_RC,Nat.add_mod] at hk
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [msgId,K_RID,K_RC,Nat.add_mod] at hk
    · simp at hm

def listEncoding (pub : List Fp) (L : ListV3) : List Nat :=
  hdrBytes pub L++L.rs.flatMap (fun x => x.enc)

theorem list_header_length (pub : List Fp) (L : ListV3) : (hdrBytes pub L).length=12 := by
  simp [hdrBytes,pubBytes]

theorem list_offset_flat (xs : List RcptE) (k : Nat) :
    lOffs xs k=12+((xs.take k).flatMap (fun x => x.enc)).length := by
  unfold lOffs
  congr 1
  induction xs.take k with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,ih]

/-- A positioned receipt byte is a byte at that same offset in its complete RC preimage. -/
theorem list_receipt_byte {pub : List Fp} {L : ListV3} {k i : Nat} (hk : k<L.rs.length)
    (hi : i<L.rs[k].enc.length) :
    lOffs L.rs k+i<(listEncoding pub L).length ∧
      (listEncoding pub L).getD (lOffs L.rs k+i) 0=L.rs[k].enc.getD i 0 := by
  obtain ⟨hpos,hval⟩ := getD_flatMap_at (fun x : RcptE => x.enc) L.rs k hk i hi
  rw [list_offset_flat]
  unfold listEncoding
  constructor
  · simp only [List.length_append,list_header_length]; omega
  · rw [Nat.add_assoc,←list_header_length pub L,getD_append_right',hval]

/-- Natural RC IDs isolate exactly one complete list preimage across all receipt
streams, including every list header and positioned receipt segment. -/
theorem list_bytes_isolate {pub : List Fp} {ls : RcptV3Vs} {i : Nat} {m : Msg}
    (hm : m∈rcptSends3 pub ls B_BYTES) (ha : m.head?=some (msgId K_RC i)) :
    ∃ hi : i<ls.length, ∃ k,k<(listEncoding pub ls[i]).length ∧
      m=[msgId K_RC i,k,(listEncoding pub ls[i]).getD k 0] := by
  simp only [rcptSends3,ite_true,show B_BYTES≠B_RCL by decide,ite_false,List.append_nil] at hm
  obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm|hm
  · have hid := emitAt_head_eq hm ha
    have hji : j=i := by unfold msgId at hid; omega
    subst j
    refine ⟨hj,?_⟩
    rw [getD_eq_getElem' ls default hj] at hm
    simp only [emitAt,List.mem_map,List.mem_range] at hm
    obtain ⟨k,hk,rfl⟩ := hm
    refine ⟨k,?_,?_⟩
    · unfold listEncoding; simp only [List.length_append]; omega
    · simp only [Nat.zero_add,listEncoding]
      rw [getD_append_left' hk]
  · obtain ⟨⟨r,off,x⟩,hpos,hm⟩ := List.mem_flatMap.mp hm
    have hm := receipt_sends_rc hm ha (by simp [msgId,K_RC,Nat.add_mod])
    have hid := emitAt_head_eq hm ha
    have hji : j=i := by unfold msgId at hid; omega
    subst j
    refine ⟨hj,?_⟩
    simp only [located,getD_eq_getElem' ls default hj,List.mem_map,List.mem_range] at hpos
    obtain ⟨k,hk,hpos⟩ := hpos
    cases hpos
    rw [getD_eq_getElem' ls[i].rs default hk] at hm
    simp only [emitAt,List.mem_map,List.mem_range] at hm
    obtain ⟨p,hp,rfl⟩ := hm
    obtain ⟨hbound,hval⟩ := list_receipt_byte (pub:=pub) hk hp
    exact ⟨lOffs ls[i].rs k+p,hbound,by rw [hval]⟩

end ZkFormal.NearV3.RcptLink
