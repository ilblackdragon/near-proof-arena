import NearSpecV3.Logged.Lockstep

/-!
# `D2/Queues.lean` mirror = original (lockstep)
-/

namespace NearSpecV3.D2

@[reducible] def Env.ws (e : Env) (st : HStore) : Env := { e with store := st }

end NearSpecV3.D2

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

section
variable {s : HStore} {root : Bytes}

theorem R_groupsPopBack (rs : RS) (sh : Nat) (m : Meta) :
    R s root (groupsPopBackL rs sh m) (groupsPopBack (rs.wt (preT s root)) sh m)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold groupsPopBack groupsPopBackL; lk

theorem R_groupsPushBack (rs : RS) (sh : Nat) (m : Meta) (size gas : Nat) :
    R s root (groupsPushBackL rs sh m size gas) (groupsPushBack (rs.wt (preT s root)) sh m size gas)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold groupsPushBack groupsPushBackL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_groupsPopBack)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_groupsPushBack)

section
variable {s : HStore} {root : Bytes}

theorem R_metaPushed (rs : RS) (sh size gas : Nat) :
    R s root (metaPushedL rs sh size gas) (metaPushed (rs.wt (preT s root)) sh size gas) (·.wt (preT s root)) := by
  unfold metaPushed metaPushedL; lk

theorem R_metaPopped (rs : RS) (sh size gas : Nat) :
    R s root (metaPoppedL rs sh size gas) (metaPopped (rs.wt (preT s root)) sh size gas) (·.wt (preT s root)) := by
  unfold metaPopped metaPoppedL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_metaPushed)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_metaPopped)

section
variable {s : HStore} {root : Bytes}

theorem R_bufferReceipt (rs : RS) (r : Rcpt) (size gas shard : Nat) :
    R s root (bufferReceiptL rs r size gas shard) (bufferReceipt (rs.wt (preT s root)) r size gas shard)
      (·.wt (preT s root)) := by
  unfold bufferReceipt bufferReceiptL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_bufferReceipt)

section
variable {s : HStore} {root : Bytes}

theorem R_forwardOrBuffer (env : Env) (es : HStore) (rs : RS) (r : Rcpt) :
    R s root (forwardOrBufferL env rs r) (forwardOrBuffer (env.ws es) (rs.wt (preT s root)) r)
      (·.wt (preT s root)) := by
  unfold forwardOrBuffer forwardOrBufferL; lk

theorem R_readBufferedFromTrie (o : Ovl) (sh i : Nat) (ho : o.trie = preT s root) :
    R s root (readBufferedFromTrieL sh i) (readBufferedFromTrie o sh i) id := by
  unfold readBufferedFromTrie readBufferedFromTrieL
  rw [ho]
  apply R_bind_ok (ev_trieFindL (kBuf sh i))
  dsimp only
  cases (preT s root).find (nibbles (kBuf sh i)) <;> lk

end

end NearSpecV3.Logged

namespace NearSpecV3.Logged
open NearSpec NearSpecV3 NearSpecV3.D2

macro_rules | `(tactic| lk_call) => `(tactic| apply R_forwardOrBuffer)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_readBufferedFromTrie)

section
variable {s : HStore} {root : Bytes}

theorem R_fwdLoop (env : Env) (es : HStore) (sh : Nat) : ∀ (fuel i : Nat) (acc : RS × Nat × List (Nat × Nat)),
    R s root (fwdLoopL env sh fuel i acc) (fwdLoop (env.ws es) sh fuel i (acc.1.wt (preT s root), acc.2))
      (fun p => (p.1.wt (preT s root), p.2))
  | 0, i, acc => by unfold fwdLoop fwdLoopL; exact R_pure rfl
  | fuel + 1, i, (rs, k, pops) => by
    have ih := R_fwdLoop env es sh fuel
    unfold fwdLoop fwdLoopL
    lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_fwdLoop)

section
variable {s : HStore} {root : Bytes}

theorem R_forwardFromBufferToShard (env : Env) (es : HStore) (rs : RS) (sh : Nat) :
    R s root (forwardFromBufferToShardL env rs sh) (forwardFromBufferToShard (env.ws es) (rs.wt (preT s root)) sh)
      (·.wt (preT s root)) := by
  unfold forwardFromBufferToShard forwardFromBufferToShardL
  have hf : ∀ (sh f : Nat) (l : List Nat) (x : RS),
      l.foldl (fun rs j => { rs with o := rs.o.remove (kBuf sh (f + j)) }) (x.wt (preT s root)) =
        (l.foldl (fun rs j => { rs with o := rs.o.remove (kBuf sh (f + j)) }) x).wt (preT s root) := by
    intro sh f l x
    exact List.foldl_hom (fun (r : RS) => r.wt (preT s root)) (fun _ _ => rfl)
  dsimp only
  apply R_bind (R_fwdLoop env es sh _ _ (rs, 0, []))
  intro b
  dsimp only
  rw [hf]
  lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_forwardFromBufferToShard)

section
variable {s : HStore} {root : Bytes}

theorem R_forwardFromBuffer (env : Env) (es : HStore) (rs : RS) :
    R s root (forwardFromBufferL env rs) (forwardFromBuffer (env.ws es) (rs.wt (preT s root))) (·.wt (preT s root)) := by
  unfold forwardFromBuffer forwardFromBufferL; lk

theorem R_groupSizes (o : Ovl) (sh : Nat) : ∀ (fuel i : Nat),
    R s root (groupSizesL o sh fuel i) (groupSizes (o.wt (preT s root)) sh fuel i) id
  | 0, i => by unfold groupSizes groupSizesL; lk
  | fuel + 1, i => by
    have ih := R_groupSizes o sh fuel
    unfold groupSizes groupSizesL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_groupSizes)

section
variable {s : HStore} {root : Bytes}

theorem R_bandwidthRequests (env : Env) (es : HStore) (rs : RS) :
    R s root (bandwidthRequestsL env rs) (bandwidthRequests (env.ws es) (rs.wt (preT s root))) id := by
  unfold bandwidthRequests bandwidthRequestsL; lk

theorem R_delayPush (rs : RS) (r : Rcpt) :
    R s root (delayPushL rs r) (delayPush (rs.wt (preT s root)) r) (·.wt (preT s root)) := by
  unfold delayPush delayPushL; lk

theorem R_delayPop (env : Env) (es : HStore) : ∀ (fuel : Nat) (rs : RS),
    R s root (delayPopL env fuel rs) (delayPop (env.ws es) fuel (rs.wt (preT s root)))
      (fun p => (p.1.wt (preT s root), p.2))
  | 0, rs => by unfold delayPop delayPopL; lk
  | fuel + 1, rs => by
    have ih := R_delayPop env es fuel
    unfold delayPop delayPopL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_forwardFromBuffer)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_bandwidthRequests)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_delayPush)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_delayPop)

end NearSpecV3.Logged
