import ZkFormal.NearV3.Public.PreparedFit
import ZkFormal.NearV3.Sched.Pub.Prep

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Sched

private theorem flat_count {α β : Type} (xs : List α) (f : α→List β) (cap : Nat)
    (h : ∀x∈xs,(f x).length≤cap) : (xs.flatMap f).length≤cap*xs.length := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

private theorem dl_length (tau : Nat) (ids : List Nat) :
    (dlRecs tau ids).length≤16*(ids.length*ids.length) := by
  have h:=flat_count (List.range (ids.length*ids.length)) (fun k=>(List.range 16).map (fun o=>[tau]++b2 k++[o,idByte ids k o])) 16 (by intro x hx;simp)
  simpa only [dlRecs,List.length_range] using h

theorem scheduler_record_counts (Ps : List InstPub) (fwd : List (Nat×Nat))
    (hlen : Ps.length≤33) (hn : ∀P∈Ps,P.n≤64) (hr : ∀P∈Ps,P.raw.length≤65536) :
    (render Ps fwd).pubb.length≤5680 ∧ (render Ps fwd).par.length≤2302146 ∧
      (render Ps fwd).dlSend.length≤65536 ∧ (render Ps fwd).dlRecv.length≤65536 := by
  let inst:=fun i=>Ps.getD i ⟨[],⟨0,0,0,0,0⟩,#[],[],[],[]⟩
  have hg : ∀i,(inst i).n≤64 ∧ (inst i).raw.length≤65536 := by
    intro i
    by_cases hi : i<Ps.length
    · have he : inst i=Ps[i]:=by simp [inst,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      rw [he];exact ⟨hn _ (List.getElem_mem hi),hr _ (List.getElem_mem hi)⟩
    · simp [inst,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : Ps.length≤i),InstPub.n]
  have hs : ∀i,(inst i).n*(inst i).n≤4096:=by
    intro i;exact Nat.mul_le_mul (hg i).1 (hg i).1
  have hpub:=flat_count (List.range Ps.length)
    (fun i=>keyRecs i (inst i).seed++ashRecs i (inst i).ash) 48 (by
      intro i hi;simp [keyRecs,ashRecs])
  have hpar:=flat_count (List.range Ps.length)
    (fun i=>[parCodec i (inst i)]++(if (inst i).raw.isEmpty then [] else [parScan i (inst i)])++
      rawRecs i (inst i)++shardRecs i (inst i)++linkRecs i (inst i)) 69762 (by
        intro i hi
        have hh:=hg i;have hm:=hs i
        simp only [List.length_append,List.length_cons,List.length_nil,rawRecs,List.length_map,
          List.length_zip,List.length_range,Nat.min_self,shardRecs,List.flatMap_cons,List.flatMap_nil,
          linkRecs]
        split <;> simp only [List.length_nil,List.length_cons] <;> omega)
  have hd:=dl_length 0 (inst 0).ids
  have he:=dl_length Ps.length (inst 0).ids
  have h0:=hs 0
  change (render Ps fwd).pubb.length≤_ ∧ _
  simp only [render,List.length_append,fwdRecs,List.length_map,List.length_range]
  simp only [List.length_range] at hpub hpar
  change (inst 0).ids.length*(inst 0).ids.length≤4096 at h0
  change _≤5680 ∧ _≤2302146 ∧ _≤65536 ∧ _≤65536
  dsimp only [inst] at hpub hpar hd he h0
  simp only [InstPub.n] at *
  omega

theorem prepared_scheduler_counts {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) :
    (Public.schedulerRecords p).pubb.length≤5680 ∧
      (Public.schedulerRecords p).par.length≤2302146 ∧
      (Public.schedulerRecords p).dlSend.length≤65536 ∧
      (Public.schedulerRecords p).dlRecv.length≤65536 := by
  apply scheduler_record_counts
  · simpa only [List.length_map] using prepD0_len hp
  · intro P hP
    obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hP
    exact (prepD0_sched hp sp hsp).n64
  · intro P hP
    obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hP
    exact (prepD0_rawOk hp sp hsp).len16

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
