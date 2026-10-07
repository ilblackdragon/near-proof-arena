import ZkFormal.NearV3.Sched.Spec.Granted
import ZkFormal.NearV3.Sched.Pub.Prep

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 NearSpecV3.Scheduler Sched

def NativeGrantInv (n bound : Nat) (st : St) : Prop := GInv n bound st ∧ SzOk n st

theorem processBucket_grant_inv {n bound : Nat} (hb : bound ≤ u64Max) (allowed : Array Bool) :
    ∀ (qs : List Req) (st : St) (bk : List (Nat × List Req)), NativeGrantInv n bound st →
      NativeGrantInv n bound (processBucket n allowed qs (st,bk)).1
  | [], st, bk, h => h
  | q :: qs, st, bk, h => by
    cases hi : q.incs with
    | nil => simpa only [processBucket,hi] using processBucket_grant_inv hb allowed qs st bk h
    | cons inc rest =>
      have hg := (tryGrant_granted hb allowed h.1 q.link inc).1
      have hs := tryGrant_szOk allowed q.link inc h.2
      cases he : tryGrant n allowed st q.link inc with
      | mk ok next =>
        rw [he] at hg hs
        simpa only [processBucket,hi,he] using processBucket_grant_inv hb allowed qs next
          (if ok ∧ rest ≠ [] then bucketPush next.allowance[q.link]! ⟨q.link,rest⟩ bk else bk) ⟨hg,hs⟩

theorem processLoop_grant_inv {n bound : Nat} (hb : bound ≤ u64Max) (allowed : Array Bool) :
    ∀ fuel st bk out, NativeGrantInv n bound st →
      processLoop n allowed fuel st bk = some out → NativeGrantInv n bound out := by
  intro fuel
  induction fuel with
  | zero =>
    intro st bk out h he
    cases bk with
    | nil => cases he; exact h
    | cons a rest => cases he
  | succ fuel ih =>
    intro st bk out h he
    cases bk with
    | nil => cases he; exact h
    | cons a rest =>
      simp only [processLoop] at he
      split at he
      · cases he
      · rename_i qs rng hshuffle
        have h' : NativeGrantInv n bound {st with rng := rng} := h
        have hi := processBucket_grant_inv hb allowed qs {st with rng := rng} (a::rest).dropLast h'
        exact ih _ _ _ hi he

theorem processRequests_grant_inv {n bound : Nat} (hb : bound ≤ u64Max) (allowed : Array Bool)
    {st out : St} {reqs : List Req} (h : NativeGrantInv n bound st)
    (he : processRequests n allowed st reqs = some out) : NativeGrantInv n bound out :=
  processLoop_grant_inv hb allowed _ _ _ _ h he

theorem base_grant_inv {n bound : Nat} (hb : bound ≤ u64Max) (allowed : Array Bool) (bw : Nat) :
    ∀ (links : List Nat) (st : St), NativeGrantInv n bound st →
      NativeGrantInv n bound (links.foldl (fun st l => (tryGrant n allowed st l bw).2) st)
  | [], st, h => h
  | l :: ls, st, h => by
    simp only [List.foldl_cons]
    exact base_grant_inv hb allowed bw ls _
      ⟨(tryGrant_granted hb allowed h.1 l bw).1,tryGrant_szOk allowed l bw h.2⟩

theorem initial_grant_inv (n bound : Nat) (allowance : Array Nat) (rng : Rng) :
    NativeGrantInv n bound ⟨Array.replicate n bound,Array.replicate n bound,allowance,
      Array.replicate (n*n) 0,rng⟩ := by
  constructor
  · intro l
    have hg := getElem!_replicate_le (n*n) 0 l
    have hs := getElem!_replicate_le n bound (l/n)
    dsimp only at hg hs ⊢
    omega
  · simp [SzOk]

theorem distribute_grant_bound {n bound : Nat} (hb : bound ≤ u64Max)
    (allowed : Array Bool) (ha : allowed.size = n*n) (st : St)
    (h : NativeGrantInv n bound st) (l : Nat) (hl : l < n*n) :
    (distribute n allowed st).granted[l]! ≤ bound := by
  rw [distribute_eq_grid n allowed st h.2.1 h.2.2.1 ha]
  exact (final_granted hb allowed st h.1 h.2.2.2 _ _
    (fun x hx => (mem_sortByKey_range _ n x).1 hx) l hl).2

theorem scheduler_run_grant_bound {cc : CongestionConfig} {ids : List Nat} {prev : Option Bytes}
    {congestion : List (Nat × CongestionInfo × Nat)}
    {rawRequests : List (Nat × List BandwidthRequest)} {seed : Bytes} {out : Output}
    (h : run Config.pv86 cc ids prev congestion rawRequests seed = some out) :
    ∀ entry ∈ out.granted, entry.2 ≤ 4500000 := by
  unfold run at h
  split at h
  all_goals
    obtain ⟨prior,hprior,h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨p,hp,h⟩ := Option.bind_eq_some_iff.mp h
      try dsimp only at h
      obtain ⟨st,hst,h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hM := pv86_maxShard hp
      have hb : (4500000 : Nat) ≤ u64Max := by decide
      have hf : NativeGrantInv ids.length 4500000 st := by
        apply processRequests_grant_inv hb _ ?_ hst
        apply base_grant_inv hb
        rw [← hM]
        exact initial_grant_inv _ _ _ _
      intro entry he
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp he
      have hl := List.mem_range.mp hl
      exact distribute_grant_bound hb _ (by simp) st hf l hl

theorem prims_sched_grant_bound {input : SchedIn} {out : SchedOut}
    (h : prims.sched input = some out) : ∀ a b, out.grant a b ≤ 4500000 := by
  unfold prims at h
  obtain ⟨o,ho,rfl⟩ := Option.map_eq_some_iff.mp h
  intro a b
  dsimp only
  cases hf : o.granted.find? (·.1 == (a,b)) with
  | none => simp
  | some e => exact scheduler_run_grant_bound ho e (List.mem_of_find?_eq_some hf)

theorem schedStep_grant_bound {ctx : ApplyCtx} {t post : PTrie} {so : SchedOut}
    (h : schedStep prims ctx t = .ok (post,so)) : ∀ a b, so.grant a b ≤ 4500000 := by
  unfold schedStep at h
  obtain ⟨prev,_,h⟩ := bind_ok h
  split at h
  · rename_i o he
    simp only [pure,Except.pure,bind,Except.bind] at h
    split at h
    · cases h
      exact prims_sched_grant_bound he
    · cases h
  · cases h

end ZkFormal.NearV3.Assembly
