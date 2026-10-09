import ZkFormal.NearV3.Candidates.ProcDistQuietRows
namespace ZkFormal.NearV3.Candidates.ProcDistShardRow
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor
open Dist
open NearSpecV3.Scheduler
set_option maxRecDepth 32768

def average (count left:Nat) := if count=0 then 0 else left/count
def remainder (count left:Nat) := if count=0 then 0 else left%count

def core (tv n sd i x count left budget kpV:Nat) : List (Nat×Nat) :=
  [(act,1),(kSh,1),(tau,tv),(nn,n),(side,sd),(a,i),(r,x),(N2,count),(L2,left),
    (by0,budget%256),(by1,budget/256%256),(by2,budget/65536%256),
    (q2,average count left),(r2,remainder count left),(icnt,finv count),
    (zc,if count=0 then 1 else 0),(kp,kpV),(da,if sd=0 then i else 0),
    (db,if sd=0 then 255 else i),(cx,average count left*64+x),(cy,kpV),(cb,1),(cg,1),
    (dlsg,1),(sL,left),(e1,if i+1=n then 1 else 0),(shd,x),(lnk,count),(llo,n),
    (adr,4096*(sd+1)+x),(bv,budget),(ig1,finv (fsub i (n-1)))]

def row (tv n sd i x count left budget kpV:Nat) : Array Nat :=
  setAll width (core tv n sd i x count left budget kpV ++
    (if count=0 then [] else bitsOf bt2 (count-1-remainder count left)) ++
    bitsN qb2 23 (average count left) ++bitsN rb2 6 (remainder count left))

def nativeX (I:Input)(R:Run)(sd i:Nat) : Nat :=
  (if sd=0 then sortByKey (fun x=>average (cntS R.n I.allowed x) R.fin.sb[x]!) (List.range R.n)
    else sortByKey (fun x=>average (cntR R.n I.allowed x) R.fin.rb[x]!) (List.range R.n))[i]!
def nativeCount (I:Input)(R:Run)(sd x:Nat) := if sd=0 then cntS R.n I.allowed x else cntR R.n I.allowed x
def nativeLeft (R:Run)(sd x:Nat) := if sd=0 then R.fin.sb[x]! else R.fin.rb[x]!

theorem emitted (I:Input)(R:Run)(sd i:Nat)(s out:ShardAcc)
    (h:shardStep I R sd i s=.ok (.yield out)) :
    out.1=s.1.push (row R.tau R.n sd i (nativeX I R sd i)
      (nativeCount I R sd (nativeX I R sd i)) (nativeLeft R sd (nativeX I R sd i))
      (budget0 ⟨I.ids,I.p,I.allowed,I.raw,I.seed,I.ash⟩ sd (nativeX I R sd i)) s.2.2) := by
  unfold shardStep at h
  simp only [bind,Except.bind] at h
  split at h
  · cases h
  · simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    rfl
end ZkFormal.NearV3.Candidates.ProcDistShardRow
