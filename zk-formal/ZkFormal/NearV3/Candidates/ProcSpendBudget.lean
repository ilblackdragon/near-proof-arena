import ZkFormal.NearV3.Candidates.ProcSenderPotential
import ZkFormal.NearV3.Candidates.ProcReplayAllowance
import ZkFormal.NearV3.Candidates.ExceptArrayCount
namespace ZkFormal.NearV3.Candidates.ProcSpendBudget
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcReplayChain ProcReplayShape ProcSenderPotential

private theorem array_eta {α : Type} (a : Array α) : (⟨a.toList⟩ : Array α)=a := rfl

def EntryInv (m n B i : Nat) (s : EntryAcc) : Prop :=
  s.1.size=n ∧ phi m n s.1+s.2.2.2.2.2.2.2.1.size≤B ∧ s.2.2.2.2.2.2.2.2.2.2.size=i

def Inv (m n B : Nat) (s : ReplayAcc) : Prop :=
  s.1.size=n ∧ phi m n s.1+s.2.2.2.2.2.2.2.1.size≤B ∧
  s.2.2.2.2.2.2.2.2.1.size=(s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList.map (fun rd=>rd.entries.length)).sum

theorem sortPush_length (ps : List (Nat×Nat×Nat×Nat)) : (sortPush ps).length=ps.length := by
  unfold sortPush
  simp only [Array.length_toList]
  unfold Array.qsort
  split <;> simp

theorem sort_check_length (a b : Array (Nat×Nat×Nat×Nat))
    (h : check (sortPush a.toList==sortPush b.toList) "push log ≠ buckets"=.ok ()) : a.size=b.size := by
  have hh := check_true _ _ h
  simp only [beq_iff_eq] at hh
  have hl := congrArg List.length hh
  simpa only [sortPush_length,Array.length_toList] using hl

set_option maxHeartbeats 1600000 in
/-- The actual replay pays one sender-potential unit per re-push. Its checked
push log then bounds all processing entries by C+43*n under PV86. -/
theorem run_steps_le (I : Input) (tau : Nat) (R : Run)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h : Gen.run I tau=.ok R) :
    (R.rounds.map (fun rd=>rd.entries.length)).sum≤R.conv.length+43*I.ids.length := by
  let B := R.conv.length+43*I.ids.length
  have hconv := ProcConvertedFacts.run_facts I tau R h
  have hm : 0<(I.p.maxSingleGrant-I.p.base)/40 := by have := (pv86_kappa hp).1; omega
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    have hall : Inv ((I.p.maxSingleGrant-I.p.base)/40) I.ids.length B ?out := by
      refine ExceptLoop.invariant (α := Round) (ε := String) ?xs ?f
        (Inv ((I.p.maxSingleGrant-I.p.base)/40) I.ids.length B) ?step ?b _ ?init ?loop
      case loop => assumption
      case init =>
        refine ⟨by simp [linkPass],?_,rfl⟩
        have hb := initial_pv86 I hp
        simp only [B,Array.length_toList,Array.size_map]
        omega
      case step =>
        intro rd hrd s hs out ho
        repeat first | cases ho | split at ho
        all_goals
          rename_i entryOut hentry
          have hi : EntryInv ((I.p.maxSingleGrant-I.p.base)/40) I.ids.length B rd.bucket.length entryOut := by
            refine ExceptRange.range_invariant (ε := String) ?ef
              (EntryInv ((I.p.maxSingleGrant-I.p.base)/40) I.ids.length B) _ ?estep ?eb _ ?einit ?eloop
            case eloop => exact hentry
            case einit => exact ⟨hs.1,hs.2.1,rfl⟩
            case estep =>
              intro i hil st hst eo heo
              repeat first | cases heo | split at heo
              all_goals repeat first | cases heo | split at heo
              all_goals
                have hf := ProcConvertedFacts.entry_facts I _ hconv _ _
                  (ProcReplayDecisions.check_lt _ _ "entry cid" (by assumption))
                  (ProcReplayDecisions.check_lt _ _ "entry j" (by assumption))
                refine ⟨_,rfl,by simpa only [Array.size_set!] using hst.1,?_,?_⟩
                · apply Nat.le_trans ?_ hst.2.1
                  refine count_phi _ _ _ hst.1 _ _ hf.1 hm hf.2 _ ?_ _ _ ?_
                  · intro hok
                    simp only [Bool.and_eq_true,decide_eq_true_eq] at hok
                    exact hok.1.1
                  · simp only [Array.size_push]
                    split <;> simp_all only [array_eta,Bool.and_eq_true,decide_eq_true_eq,Bool.false_eq_true,false_and] <;> omega
                · simpa only [Array.size_push,hst.2.2]
          refine ⟨hi.1,hi.2.1,?_⟩
          refine Eq.trans (b := s.2.2.2.2.2.2.2.2.1.size+rd.bucket.length) ?hcount ?hsum
          case hcount =>
            refine ExceptArrayCount.count (β := Nat×Nat×Nat×Nat) (ε := String)
              rd.bucket ?cf ?cstep ?cb _ ?cloop
            case cloop => assumption
            case cstep =>
              intro p hp b out ho
              repeat first | cases ho | split at ho
              all_goals exact ⟨_,rfl,Array.size_push _⟩
          case hsum =>
            simp only [Array.toList_push,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,Array.length_toList]
            rw [←hs.2.2,hi.2.2]
    have hbalance := sort_check_length _ _ (by assumption)
    rcases hall with ⟨hsize,hphi,hcount⟩
    simp only [B,Array.length_toList,Array.size_map] at *
    omega
end ZkFormal.NearV3.Candidates.ProcSpendBudget
