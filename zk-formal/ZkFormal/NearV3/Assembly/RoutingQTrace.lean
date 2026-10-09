import ZkFormal.NearV3.Assembly.RoutingQPatch

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof

def startsReceiver (tr : Trace Fp) (t r : Nat) : Prop :=
  tr.cell t r sV=1 ∧ tr.cell t r fs=1
instance (tr : Trace Fp) (t r : Nat) : Decidable (startsReceiver tr t r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Fill only the seven first-receiver scratch cells; all table heights and all
other cells, including original q and every bus-visible column, are preserved. -/
def patchTrace (tr : Trace Fp) (t : Nat) : Trace Fp where
  log := tr.log
  cell := fun tt r k =>
    if tt=t ∧ startsReceiver tr t r ∧ xb 12≤k ∧ k≤xb 18 then
      filledCell (cv tr t r q) k
    else tr.cell tt r k

theorem patch_height (tr : Trace Fp) (t tt : Nat) :
    (patchTrace tr t).height tt=tr.height tt := rfl

theorem patch_other (tr : Trace Fp) (t r k : Nat)
    (hk : ¬(xb 12≤k ∧ k≤xb 18)) :
    (patchTrace tr t).cell t r k=tr.cell t r k := by
  simp only [patchTrace]; split <;> grind

theorem patch_unmarked (tr : Trace Fp) (t r k : Nat)
    (hr : ¬startsReceiver tr t r) :
    (patchTrace tr t).cell t r k=tr.cell t r k := by
  simp [patchTrace,hr]

theorem patch_states (tr : Trace Fp) (t r k : Nat) (hk : k≤26) :
    (patchTrace tr t).cell t r k=tr.cell t r k :=
  patch_other tr t r k (by unfold xb;omega)

theorem patch_env_other (tr : Trace Fp) (t r k : Nat) (pub : List Fp) (nx : Bool)
    (hk : ¬(xb 12≤k ∧ k≤xb 18)) :
    (rowEnv (patchTrace tr t) t r pub).col k nx=(rowEnv tr t r pub).col k nx := by
  change (patchTrace tr t).cell t _ k=tr.cell t _ k
  rw [patch_height]
  exact patch_other tr t _ k hk

theorem state_specialization {tr : Trace Fp} {t r state : Nat} {pub : List Fp}
    (hL : TableLocal RcptV3.table tr t pub) (hr : r<tr.height t)
    (hst : state∈states) (hs : tr.cell t r state=1) :
    ∀k,4≤k → k≤26 → tr.cell t r k=if k=state then 1 else 0 := by
  intro k hk hk'
  by_cases he : k=state
  · simpa [he] using hs
  · simp only [if_neg he]
    exact (oneHot hL hr hst hs).2 k (by change k∈[4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]; simp; omega) he

theorem patch_boolean {tr : Trace Fp} {t r : Nat}
    (hs : startsReceiver tr t r) (hq : cv tr t r q<128) :
    ∀i,i<7 → (patchTrace tr t).cell t r (xb (12+i))=0 ∨
      (patchTrace tr t).cell t r (xb (12+i))=1 := by
  intro i hi
  have hx : xb 12≤xb (12+i) ∧ xb (12+i)≤xb 18 := by unfold xb;omega
  simp only [patchTrace,hs,hx.1,hx.2, and_self,if_true]
  exact (honest_filling _ hq).2 i hi

/-- Full preservation of old local constraints. The predecessor condition is
an ordinary trace-layout fact, not a new arithmetic or native-domain bound. -/
theorem patch_old_constraints {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal RcptV3.table tr t pub)
    (hQ : ∀r,r<tr.height t → startsReceiver tr t r → cv tr t r q<128)
    (hprev : ∀r,r<tr.height t → startsReceiver tr t ((r+1)%tr.height t) → tr.cell t r sVL=1) :
    ∀r,r<tr.height t → ∀e∈RcptV3.constraints,e.eval (patchTrace tr t) t r pub=0 := by
  intro r hr
  by_cases hs : startsReceiver tr t r
  · apply receiver_constraints_patch (patch_height tr t t)
    · exact state_specialization hL hr (by simp [states]) hs.1
    · intro k hk hk'; rw [patch_states _ _ _ _ hk']
      exact state_specialization hL hr (by simp [states]) hs.1 k hk hk'
    · exact fun k nx hk=>patch_env_other tr t r k pub nx hk
    · exact patch_boolean hs (hQ r hr hs)
    · exact hL.constr r hr
  · by_cases hn : startsReceiver tr t ((r+1)%tr.height t)
    · apply predecessor_constraints_patch (patch_height tr t t)
      · exact state_specialization hL hr (by simp [states]) (hprev r hr hn)
      · intro k hk hk'; rw [patch_states _ _ _ _ hk']
        exact state_specialization hL hr (by simp [states]) (hprev r hr hn) k hk hk'
      · intro k nx hk
        rcases hk with hk|hk
        · subst nx; exact patch_unmarked tr t r k hs
        · exact patch_env_other tr t r k pub nx hk
      · exact hL.constr r hr
    · intro e he
      rw [eval_scratch_agree (patch_height tr t t) e (by
        intro k nx _
        cases nx with
        | false => exact patch_unmarked tr t r k hs
        | true => exact patch_unmarked tr t _ k hn)]
      exact hL.constr r hr e he

theorem patch_qBound_start {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hs : startsReceiver tr t r) (hq : cv tr t r q<128) :
    qBound.eval (patchTrace tr t) t r pub=0 := by
  have hf := (honest_filling _ hq).1
  have hqeq := cell_eq_cast tr t r q
  have hb : ∀i,i<7 → (patchTrace tr t).cell t r (xb (12+i))=
      (filledTrace (cv tr t r q)).cell 0 0 (xb (12+i)) := by
    intro i hi
    have hx : xb 12≤xb (12+i) ∧ xb (12+i)≤xb 18 := by unfold xb;omega
    simp [patchTrace,hs,hx.1,hx.2,filledTrace]
  have hsV : (patchTrace tr t).cell t r sV=1 := by
    rw [patch_states _ _ _ _ (by decide)]; exact hs.1
  have hfs : (patchTrace tr t).cell t r fs=1 := by
    rw [patch_other _ _ _ _ (by decide)]; exact hs.2
  have hqq : (patchTrace tr t).cell t r q=Fp.ofNat (cv tr t r q) := by
    rw [patch_other _ _ _ _ (by decide)]; exact hqeq
  simp only [qBound,eval_mul3,eval_sub,eval_c,hsV,hfs,hqq]
  simp only [qBound,eval_mul3,eval_sub,eval_c] at hf
  have hbits : (bitsX 12 7).eval (patchTrace tr t) t r pub=
      (bitsX 12 7).eval (filledTrace (cv tr t r q)) 0 0 [] := by
    simp only [bitsX,bits,List.range_succ,List.range_zero,List.map_append,List.map_cons,
      List.map_nil,eval_sum_append,eval_sum_cons,eval_sum_nil,eval_smul,eval_c]
    simp only [hb 0 (by decide),hb 1 (by decide),hb 2 (by decide),hb 3 (by decide),
      hb 4 (by decide),hb 5 (by decide),hb 6 (by decide)]
  rw [hbits]
  simpa [filledTrace,filledCell,q,sV,fs,xb] using hf

theorem patch_interaction_expr {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    {i : Interaction} (hi : i∈RcptV3.interactions) {e : Expr} (he : e∈i.msg++i.mult) :
    e.eval (patchTrace tr t) t r pub=e.eval tr t r pub := by
  have hm : e∈RcptV3.interactions.flatMap (fun i=>i.msg++i.mult) :=
    List.mem_flatMap.mpr ⟨i,hi,he⟩
  have hf := List.all_eq_true.mp interaction_scratch_free _ hm
  have hf0 : readsScratch false e=false := by simp_all
  have hf1 : readsScratch true e=false := by simp_all
  apply eval_scratch_agree (patch_height tr t t)
  intro k nx hk
  apply patch_env_other
  rcases hk with hk|hk
  · exact hk
  · cases nx <;> simp_all

theorem patch_qBound {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL : TableLocal RcptV3.table tr t pub) (hr : r<tr.height t)
    (hQ : startsReceiver tr t r → cv tr t r q<128) :
    qBound.eval (patchTrace tr t) t r pub=0 := by
  by_cases hs : startsReceiver tr t r
  · exact patch_qBound_start hs (hQ hs)
  · have hv := states_bool hL hr sV (by simp [states])
    have hf := isBool hL hr (show fs∈boolCols by simp [boolCols])
    simp only [startsReceiver] at hs
    have hz : tr.cell t r sV=0 ∨ tr.cell t r fs=0 := by grind
    simp only [qBound,eval_mul3,eval_sub,eval_c,
      patch_other tr t r sV (by decide),patch_other tr t r fs (by decide)]
    rcases hz with hz|hz <;> rw [hz] <;> grind

/-- Executable full trace conversion. The only non-local inputs are honest q
range and the first-receiver predecessor shape. Public inputs are unchanged. -/
theorem patch_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal RcptV3.table tr t pub)
    (hQ : ∀r,r<tr.height t → startsReceiver tr t r → cv tr t r q<128)
    (hprev : ∀r,r<tr.height t → startsReceiver tr t ((r+1)%tr.height t) → tr.cell t r sVL=1) :
    TableLocal candidateTable (patchTrace tr t) t pub := by
  refine ⟨hL.log_ge,hL.log_le,?_,?_⟩
  · intro r hr e he
    change e∈RcptV3.constraints++[qBound] at he
    rcases List.mem_append.mp he with he|he
    · exact patch_old_constraints hL hQ hprev r hr e he
    · have he' : e=qBound := by simpa using he
      subst e; exact patch_qBound hL hr (hQ r hr)
  · intro r hr i hi e he
    rw [patch_interaction_expr hi (List.mem_append_right _ he)]
    exact hL.bits r hr i hi e he

theorem patch_msgVal {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    {i : Interaction} (hi : i∈RcptV3.interactions) :
    i.msgVal (patchTrace tr t) t r pub=i.msgVal tr t r pub := by
  apply List.map_congr_left
  intro e he
  exact patch_interaction_expr hi (List.mem_append_left _ he)

theorem patch_multNat {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    {i : Interaction} (hi : i∈RcptV3.interactions) :
    i.multNat (patchTrace tr t) t r pub=i.multNat tr t r pub := by
  unfold Interaction.multNat
  have go : ∀es, (∀e∈es,e∈i.mult) → ∀k,
      Interaction.multNat.go (patchTrace tr t) t r pub es k=
      Interaction.multNat.go tr t r pub es k := by
    intro es
    induction es with
    | nil => intros; rfl
    | cons e es ih =>
      intro hm k
      simp only [Interaction.multNat.go]
      rw [patch_interaction_expr hi (List.mem_append_right _ (hm _ (by simp))),
        ih (by intro e he; exact hm e (by simp [he]))]
  exact go i.mult (fun _ he=>he) 0

/- All messages and their natural multiplicities are preserved exactly on every
bus and both directions. This theorem needs no q bound or layout assumptions. -/
set_option maxHeartbeats 4000000 in
theorem patch_busCount (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount candidateTable.interactions (patchTrace tr t) t pub bus sd msg=
      tableBusCount RcptV3.interactions tr t pub bus sd msg := by
  change tableBusCount RcptV3.interactions _ _ _ _ _ _=_
  unfold tableBusCount
  rw [patch_height]
  have rows : ∀rs : List Nat, ∀acc,
    rs.foldr (fun r acc=>RcptV3.interactions.foldr (fun i acc'=>
      (if i.bus=bus ∧ i.send=sd ∧ i.msgVal (patchTrace tr t) t r pub=msg
       then i.multNat (patchTrace tr t) t r pub else 0)+acc') acc) acc=
    rs.foldr (fun r acc=>RcptV3.interactions.foldr (fun i acc'=>
      (if i.bus=bus ∧ i.send=sd ∧ i.msgVal tr t r pub=msg
       then i.multNat tr t r pub else 0)+acc') acc) acc := by
    intro rs
    induction rs with
    | nil => intros; rfl
    | cons r rs ih =>
      intro acc
      simp only [List.foldr_cons]
      rw [ih]
      have ints : ∀is : List Interaction,(∀i∈is,i∈RcptV3.interactions) → ∀a,
        is.foldr (fun i acc'=>
          (if i.bus=bus ∧ i.send=sd ∧ i.msgVal (patchTrace tr t) t r pub=msg
           then i.multNat (patchTrace tr t) t r pub else 0)+acc') a=
        is.foldr (fun i acc'=>
          (if i.bus=bus ∧ i.send=sd ∧ i.msgVal tr t r pub=msg
           then i.multNat tr t r pub else 0)+acc') a := by
        intro is
        induction is with
        | nil => intros; rfl
        | cons i is ih =>
          intro hm a
          simp only [List.foldr_cons]
          rw [patch_msgVal (hm i (by simp)),patch_multNat (hm i (by simp)),
            ih (by intro i hi; exact hm i (by simp [hi]))]
      exact ints _ (fun _ hi=>hi) _
  exact rows _ 0

theorem patch_traffic {tr : Trace Fp} {t : Nat} {pub : List Fp} {tf : Traffic}
    (h : TableTraffic RcptV3.interactions tr t pub tf) :
    TableTraffic candidateTable.interactions (patchTrace tr t) t pub tf := by
  intro bus msg
  rw [patch_busCount,patch_busCount]
  exact h bus msg

end ZkFormal.NearV3.Assembly.RoutingQCandidate
