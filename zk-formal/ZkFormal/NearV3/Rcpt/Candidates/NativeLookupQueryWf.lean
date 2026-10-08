import ZkFormal.NearV3.Rcpt.Candidates.NativeAccessKeyRows
import ZkFormal.NearV3.Rcpt.Candidates.Walk22Compat

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen Assembly

private theorem sum_member_le (xs : List Nat) (x : Nat) (h : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil=>simp at h
  | cons a xs ih=>
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · have hh:=ih h;simp only [List.sum_cons];omega

theorem nativeQueryWalk_wf (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery)
    (w : WalkR) (h : nativeQueryWalk pairs q=some w)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true) (hb : preBytes (pairs.map Prod.fst)≤2000000)
    (hts : pairs.length≤P) (hwid : q.wid<P) (hk : ∀a∈q.key,a<16)
    (hlen : q.key.length+2≤2^23) : WalkWf3 [w] := by
  cases hp : pairs[q.tau]? with
  | none=>simp [nativeQueryWalk,hp] at h
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    have hi : q.tau<pairs.length := (List.getElem?_eq_some_iff.mp hp).1
    have hsplit : pairs=pairs.take q.tau++(tree,post)::pairs.drop (q.tau+1) := by
      have hd:=List.drop_eq_getElem_cons hi
      rw [(List.getElem?_eq_some_iff.mp hp).2] at hd
      simpa only [hd] using (List.take_append_drop q.tau pairs).symm
    have htree : tree.wf=true := hw tree (List.mem_map.mpr ⟨(tree,post),List.mem_of_getElem? hp,rfl⟩)
    have hforest : pairs.map Prod.fst=(pairs.take q.tau).map Prod.fst++
        tree::(pairs.drop (q.tau+1)).map Prod.fst := by
      simpa only [List.map_append,List.map_cons] using congrArg (List.map Prod.fst) hsplit
    dsimp only [nativeQueryWalk] at h
    rw [hp] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases hs : nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
    | none=>rw [hs] at h;cases h
    | some steps=>
      rw [hs] at h
      have h := Option.some.inj h
      subst w
      have hb' := hb
      rw [hforest] at hb'
      have ht' : ((pairs.take q.tau).map Prod.fst++tree::(pairs.drop (q.tau+1)).map Prod.fst).length≤P := by
        rw [←hforest,List.length_map];exact hts
      have hh:=native_forest_lookup_wf ((pairs.take q.tau).map Prod.fst)
        ((pairs.drop (q.tau+1)).map Prod.fst) tree q.wid q.key steps htree hb' ht' hwid hk hlen hs
      simpa only [List.length_map,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)] using hh

/-- Per-query native validity combines with the exact aggregate row budget. -/
theorem nativeQueryWalks_wf (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery)
    (ws : List WalkR) (h : nativeQueryWalks pairs qs=some ws)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true) (hb : preBytes (pairs.map Prod.fst)≤2000000)
    (hts : pairs.length≤P) (hwid : ∀q∈qs,q.wid<P) (hk : ∀q∈qs,∀a∈q.key,a<16)
    (hr : (qs.map (fun q=>q.key.length+2)).sum≤2^23) : WalkWf3 ws := by
  have hm : ∀w∈ws,WalkWf3 [w] := by
    intro w hwmem
    have hh : some w∈ws.map some := List.mem_map.mpr ⟨w,hwmem,rfl⟩
    rw [nativeQueryWalks_exact pairs qs ws h] at hh
    obtain ⟨q,hq,hqw⟩:=List.mem_map.mp hh
    have hlen : q.key.length+2≤2^23 := by
      have hl : q.key.length+2∈qs.map (fun q=>q.key.length+2) := List.mem_map.mpr ⟨q,hq,rfl⟩
      have hh:=sum_member_le _ _ hl
      omega
    exact nativeQueryWalk_wf pairs q w hqw hw hb hts (hwid q hq) (hk q hq) hlen
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w hw;exact (hm w hw).len w (by simp)
  · intro w hw;exact (hm w hw).canon w (by simp)
  · intro w hw;exact (hm w hw).rows w (by simp)
  · intro w hw;exact (hm w hw).start w (by simp)
  · intro w hw;exact (hm w hw).chain w (by simp)
  · rw [nativeQueryWalks_rows pairs qs ws h];exact hr

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
