import ZkFormal.NearV3.Candidates.ProcGrantAgreement
import ZkFormal.NearV3.Candidates.ProcCoreReplay
namespace ZkFormal.NearV3.Candidates.ProcNativeGrant
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

def native (st : PState) : St := ⟨st.sb,st.rb,st.al,st.g,st.rng⟩
def Inv (n M : Nat) (st : PState) : Prop := GInv n M (native st)

/-- The actual native saturating grant agrees with the event model under the
ordinary shard-budget invariant; no arithmetic-overflow premise is supplied. -/
theorem grant_native (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool)
    (st : PState) (hs : Inv n M st) (l inc : Nat) :
    tryGrant n allowed (native st) l inc =
      (allowed[l]! && decide (inc≤st.sb[l/n]!) && decide (inc≤st.rb[l%n]!),
        native (ProcGrantAgreement.modelGrant n allowed l inc st)) := by
  have hb := hs l
  change st.g[l]!+st.sb[l/n]!≤M at hb
  unfold tryGrant grantMore ProcGrantAgreement.modelGrant native
  cases ha : allowed[l]! <;>
    by_cases hS : inc≤st.sb[l/n]! <;> by_cases hR : inc≤st.rb[l%n]!
  all_goals
    have hsat : inc≤st.sb[l/n]! → st.g[l]!+inc≤u64Max := by omega
    simp_all only [Bool.not_false,Bool.not_true,
      Bool.and_false,Bool.and_true,Bool.false_eq_true,decide_true,decide_false,
      ite_true,ite_false]
  all_goals split <;> (first | omega | rfl)

theorem grant_inv (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool)
    (st : PState) (hs : Inv n M st) (l inc : Nat) :
    Inv n M (ProcGrantAgreement.modelGrant n allowed l inc st) := by
  have hh := (tryGrant_granted hM allowed hs l inc).1
  rw [grant_native n M hM allowed st hs l inc] at hh
  exact hh

theorem initial_inv (I : Input) (hn : 1≤I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ha : I.allowed.size=I.ids.length*I.ids.length) :
    Inv I.ids.length I.p.maxShardBandwidth (ProcCoreReplay.initial I) :=
  lpState_ginv I.ids hn I.p hp I.allowed ha
    (fun k=>(a0Canon I.ids.length I.prev)[k]!) I.seed

theorem entry_inv (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool)
    (reqs : List Req) (K z v : Nat) (s : ProcModelStep.EntryAcc)
    (hs : Inv n M s.2.1) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>Inv n M out.2.1) out := by
  have hh := ProcGrantAgreement.entry_grant n allowed reqs K z v s out h
  cases out <;> simp only [ExceptLoop.StepInv] at hh ⊢ <;> rw [hh] <;>
    exact grant_inv n M hM allowed s.2.1 hs _ _
end ZkFormal.NearV3.Candidates.ProcNativeGrant
