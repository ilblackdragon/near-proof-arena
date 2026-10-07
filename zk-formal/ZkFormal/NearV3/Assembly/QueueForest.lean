import ZkFormal.NearV3.Assembly.QueueModes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

def queueForestProviders : Nat → Nat → List (PTrie × List ReadRequest) → List QueueProvider
  | _, _, [] => []
  | tau, base, (pre,rs)::rest => queueProviders pre rs tau base ++
      queueForestProviders (tau+1) (base+(NearSpecV3.valsOf pre).length) rest

def queueForestValueCount (xs : List (PTrie × List ReadRequest)) : Nat :=
  (xs.map (fun x => (NearSpecV3.valsOf x.1).length)).sum

theorem queueForestProviders_bytes (xs : List (PTrie × List ReadRequest)) (tau base : Nat) :
    ((queueForestProviders tau base xs).map (fun p => p.bytes.length)).sum ≤
      preValueBytes (xs.map Prod.fst) := by
  induction xs generalizing tau base with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    have h := queueProviders_bytes pre rs tau base
    have ht := ih (tau+1) (base+(NearSpecV3.valsOf pre).length)
    simp only [queueForestProviders,List.map_append,List.sum_append,preValueBytes,List.map_cons,List.sum_cons] at *
    omega

theorem queueForestProviders_bounds (xs : List (PTrie × List ReadRequest)) (tau base : Nat)
    {p : QueueProvider} (hp : p ∈ queueForestProviders tau base xs) :
    tau ≤ p.tau ∧ p.tau < tau+xs.length ∧ base ≤ p.vid ∧ p.vid < base+queueForestValueCount xs := by
  induction xs generalizing tau base with
  | nil => simp [queueForestProviders] at hp
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    simp only [queueForestProviders,List.mem_append] at hp
    have hcnt : queueForestValueCount ((pre,rs)::xs) =
        (NearSpecV3.valsOf pre).length + queueForestValueCount xs := rfl
    rw [hcnt]
    simp only [List.length_cons]
    rcases hp with hp | hp
    · obtain ⟨ht,hl,hu,_,_⟩ := queueProviders_owner hp
      omega
    · have h := ih (tau+1) (base+(NearSpecV3.valsOf pre).length) hp
      omega

theorem queueForestProviders_ids_nodup (xs : List (PTrie × List ReadRequest)) (tau base : Nat) :
    ((queueForestProviders tau base xs).map QueueProvider.vid).Nodup := by
  induction xs generalizing tau base with
  | nil => simp [queueForestProviders]
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    simp only [queueForestProviders,List.map_append,List.nodup_append]
    refine ⟨queueProviders_ids_nodup pre rs tau base,ih _ _,?_⟩
    intro i hi j hj hsame
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hj
    have hp' := queueProviders_owner hp
    have hq' := queueForestProviders_bounds xs (tau+1) (base+(NearSpecV3.valsOf pre).length) hq
    omega

def queueInputs (pre : PTrie) (v : MainValues) (pres : List PTrie) : List (PTrie × List ReadRequest) :=
  (pre,mainRequests pre v) :: pres.map (fun t => (t,[missingRequest t]))

theorem queueInputs_pre (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    (queueInputs pre v pres).map Prod.fst = pre::pres := by simp [queueInputs,List.map_map,Function.comp_def]

theorem checkD0a_queue_provider_bytes {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) :
    ((queueForestProviders 0 0 (queueInputs m.pre v (steps.map ImplicitStepV3.pre))).map
      (fun p => p.bytes.length)).sum ≤ B := by
  have hb := queueForestProviders_bytes (queueInputs m.pre v (steps.map ImplicitStepV3.pre)) 0 0
  rw [queueInputs_pre] at hb
  exact Nat.le_trans hb (checkD0a_preValueBytes hk hw h hm hv)

theorem queueForestProviders_accepts (xs : List (PTrie × List ReadRequest)) (tau base : Nat)
    (hh : ∀ x ∈ xs, ∀ r ∈ x.2, r.Holds x.1) :
    ∀ p ∈ queueForestProviders tau base xs, p.mode.Accepts (some p.bytes) := by
  induction xs generalizing tau base with
  | nil => simp [queueForestProviders]
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    intro p hp
    simp only [queueForestProviders,List.mem_append] at hp
    rcases hp with hp | hp
    · exact queueProviders_accepts (hh (pre,rs) (by simp)) hp
    · exact ih (tau+1) (base+(NearSpecV3.valsOf pre).length)
        (fun x hx => hh x (by simp [hx])) p hp

theorem ImplicitTraceValid.missing_requests {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) :
    ∀ s ∈ steps, (missingRequest s.pre).Holds s.pre := by
  induction hv with
  | nil => simp
  | cons root b t rest steps post last run checked tail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact applyMissingChunk_request run
    · exact ih s hs

theorem native_queueInputs {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃ v : MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      (∀ x ∈ queueInputs m.pre v (steps.map ImplicitStepV3.pre), ∀ r ∈ x.2, r.Holds x.1) ∧
      (∀ x ∈ queueInputs m.pre v (steps.map ImplicitStepV3.pre), QueueModesByKey x.2) := by
  have hw : m.pre.wf = true := by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  obtain ⟨v,hvalid,hreads⟩ := applyNewChunk_pre_queue_reads hw hm.run
  refine ⟨v,hvalid,hreads,?_,?_⟩
  · intro x hx r hr
    simp only [queueInputs,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl | ⟨pre,⟨s,hs,rfl⟩,rfl⟩
    · exact mainRequests_hold m.pre v hvalid hreads r hr
    · have he : r=missingRequest s.pre := by simpa using hr
      subst r
      exact hv.missing_requests s hs
  · intro x hx
    simp only [queueInputs,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl | ⟨pre,⟨s,hs,rfl⟩,rfl⟩
    · exact mainRequests_modes m.pre v
    · exact missingRequest_modes s.pre

theorem queueForestProviders_length (xs : List (PTrie × List ReadRequest)) (tau base : Nat) :
    (queueForestProviders tau base xs).length ≤ (xs.map (fun x => x.2.length)).sum := by
  induction xs generalizing tau base with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    obtain ⟨pre,rs⟩ := x
    have hh := queueProviders_length pre rs tau base
    have ht := ih (tau+1) (base+(NearSpecV3.valsOf pre).length)
    simp only [queueForestProviders,List.length_append,List.map_cons,List.sum_cons]
    omega

theorem queueInputs_request_count (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    ((queueInputs pre v pres).map (fun x => x.2.length)).sum = 3+v.shards.length+pres.length := by
  simp only [queueInputs,List.map_cons,List.map_map,List.sum_cons,mainRequests_length,Function.comp_def,List.length_singleton]
  have he : (pres.map (fun _ => 1)).sum = pres.length := by
    induction pres with | nil => rfl | cons p ps ih => simp [ih,Nat.add_comm]
  simpa only [Function.comp_def] using congrArg (fun n => 3+v.shards.length+n) he

/-- Resolver consumed by the queue walk generator; offsets follow the value forest. -/
def queueForestResolve : List (PTrie × List ReadRequest) → Nat → Nat → Nat → Nat × Nat
  | [], _, _, _ => (0,0)
  | (pre,rs)::_, base, 0, slot => queueResolve pre rs base slot
  | (pre,_)::xs, base, tau+1, slot =>
    queueForestResolve xs (base+(NearSpecV3.valsOf pre).length) tau slot

theorem queueForestResolve_present (xs : List (PTrie × List ReadRequest)) (start base : Nat)
    {tau slot : Nat} {pre : PTrie} {rs : List ReadRequest} {r : ReadRequest} {b : Bytes}
    (ht : xs[tau]? = some (pre,rs)) (hr : rs[slot]? = some r)
    (hb : pre.find r.key = some (some b)) :
    ∃ p ∈ queueForestProviders start base xs, p.tau=start+tau ∧ p.bytes=b ∧
      queueForestResolve xs base tau slot = (p.vid,p.users) := by
  induction xs generalizing start base tau with
  | nil => simp at ht
  | cons x xs ih =>
    obtain ⟨first,requests⟩ := x
    cases tau with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at ht
      obtain ⟨rfl,rfl⟩ := ht
      obtain ⟨i,hi,hresolve,hp⟩ := queueResolve_present hr hb start base
      refine ⟨_,List.mem_append.mpr (Or.inl hp),?_,rfl,hresolve⟩
      simp
    | succ tau =>
      simp only [List.getElem?_cons_succ] at ht
      obtain ⟨p,hp,hpt,hpb,hresolve⟩ := ih (start+1) (base+(NearSpecV3.valsOf first).length) ht
      exact ⟨p,List.mem_append.mpr (Or.inr hp),by omega,hpb,hresolve⟩

end ZkFormal.NearV3.Assembly
