import ZkFormal.NearV3.Candidates.ProcPreparedRequestGood
namespace ZkFormal.NearV3.Candidates.ProcRoundGuards
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcZeroPending ProcZeroTransition

def Below (K k : Nat) : Prop := k<K ∨ K=0 ∧ k=0

def Tags (last : Option (Nat×Nat)) (ps : List Push) : Prop :=
  Pending (nextZero last) ps ∧
  (∀p∈ps,p.key≠0 → p.z=0) ∧
  (∀p∈ps,match last with | none=>True | some (K,_)=>Below K p.key)

theorem initial (reqs : List Req) (st : PState) : Tags none (ProcModelStep.initial reqs st).1 := by
  refine ⟨ProcZeroPending.initial reqs st,?_,by simp⟩
  intro p hp hk
  obtain ⟨i,hi,hp⟩ := List.mem_filterMap.mp hp
  dsimp only at hp
  split at hp
  · contradiction
  · cases hp
    exact if_neg hk

theorem head_mem (ps : List Push) (hn : ps≠[]) :
    let K := ProcMaxBucket.maxKey ps
    (sortTs (ps.filter (fun p=>p.key==K))).headD default∈ps ∧
    ((sortTs (ps.filter (fun p=>p.key==K))).headD default).key=K := by
  dsimp only
  obtain ⟨p,hp,hk⟩ := ProcMaxBucket.max_mem ps hn
  have hm : p∈sortTs (ps.filter (fun p=>p.key==ProcMaxBucket.maxKey ps)) :=
    (ProcPushPerm.sort_perm _).mem_iff.mpr (List.mem_filter.mpr ⟨hp,by simpa using hk⟩)
  cases he : sortTs (ps.filter (fun p=>p.key==ProcMaxBucket.maxKey ps)) with
  | nil => rw [he] at hm; contradiction
  | cons q qs =>
    have hq : q∈sortTs (ps.filter (fun p=>p.key==ProcMaxBucket.maxKey ps)) := by rw [he]; simp
    have hh := List.mem_filter.mp ((ProcPushPerm.sort_perm _).mem_iff.mp hq)
    simpa [he] using And.intro hh.1 (show q.key=ProcMaxBucket.maxKey ps by simpa using hh.2)

theorem guards (last : Option (Nat×Nat)) (ps : List Push) (hn : ps≠[]) (hs : Tags last ps) :
    let K := ProcMaxBucket.maxKey ps
    let bucket := sortTs (ps.filter (fun p=>p.key==K))
    let z := (bucket.headD default).z
    bucket.all (fun p=>p.z==z)=true ∧ ProcModelValid.Valid K z ∧ Ordered last K z := by
  dsimp only
  let K := ProcMaxBucket.maxKey ps
  let b := sortTs (ps.filter (fun p=>p.key==K))
  let q := b.headD default
  have hq := head_mem ps hn
  change q∈ps ∧ q.key=K at hq
  have htag : q.z=if K=0 then nextZero last else 0 := by
    by_cases hk : K=0
    · rw [if_pos hk]; exact hs.1 q hq.1 (hq.2.trans hk)
    · rw [if_neg hk]; exact hs.2.1 q hq.1 (by omega)
  have hzpos : 0<nextZero last := by cases last with | none=>decide | some p=> rcases p with ⟨a,z⟩; simp [nextZero]; split <;> omega
  refine ⟨?_,?_,?_⟩
  · apply List.all_eq_true.mpr
    intro p hp
    have hm := List.mem_filter.mp ((ProcPushPerm.sort_perm _).mem_iff.mp hp)
    have hk : p.key=K := by simpa using hm.2
    have he : p.z=q.z := by
      rw [htag]
      by_cases hK : K=0
      · rw [if_pos hK]; exact hs.1 p hm.1 (hk.trans hK)
      · rw [if_neg hK]; exact hs.2.1 p hm.1 (by omega)
    exact beq_iff_eq.mpr he
  · change ProcModelValid.Valid K q.z
    unfold ProcModelValid.Valid
    split <;> simp_all only [ite_true,ite_false]
  · change Ordered last K q.z
    cases last with
    | none => trivial
    | some pair =>
      rcases pair with ⟨prev,z⟩
      have hb := hs.2.2 q hq.1
      change Below prev q.key at hb
      unfold Ordered
      rw [hq.2] at hb
      rcases hb with hb|⟨hprev,hK⟩
      · exact Or.inl hb
      · right
        refine ⟨hK,hprev,?_⟩
        simpa [hK,hprev,nextZero] using htag
end ZkFormal.NearV3.Candidates.ProcRoundGuards
