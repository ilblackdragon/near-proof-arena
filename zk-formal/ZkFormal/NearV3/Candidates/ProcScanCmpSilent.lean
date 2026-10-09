import ZkFormal.NearV3.Candidates.ProcDistCmpTraffic
import ZkFormal.NearV3.Sched.Complete.Rows
namespace ZkFormal.NearV3.Candidates.ProcScanCmpSilent
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Good (rows:Array (Array Nat)) := ∀row∈rows.toList,row[Dist.cg]! = 0
private theorem set_ne (xs:Array Nat)(i j x:Nat)(h:i≠j) :
    (xs.setIfInBounds i x)[j]! = xs[j]! := Array.getElem!_set!_ne xs i j x h
private theorem loop {α β:Type}(xs:List α)(f:α→β→Id (ForInStep β))(P:β→Prop)
    (hf:∀x∈xs,∀s,P s→∃t,f x s=.yield t ∧ P t)(s:β)(hs:P s) :
    P (Id.run (forIn xs s f)) := by
  induction xs generalizing s with
  | nil=>exact hs
  | cons x xs ih=>
    obtain ⟨t,ht,hp⟩:=hf x (by simp) s hs
    rw [List.forIn_cons]
    simp only [ht]
    exact ih (fun y hy=>hf y (by simp [hy])) t hp
private theorem push (rs:Array (Array Nat))(r:Array Nat)(hs:Good rs)(hr:r[Dist.cg]! = 0) : Good (rs.push r) := by
  intro row hm
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm|rfl
  · exact hs row hm
  · exact hr

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem request (R:Run)(c:CReq) : Good (Scan.reqRows R c) := by
  unfold Scan.reqRows
  change Good (Id.run (forIn (List.range 20) ((#[]:Array (Array Nat)),(0:Nat),R.base) _)).1
  refine loop (β:=Array (Array Nat)×Nat×Nat) (List.range 20) _
    (fun s=>Good s.1) ?_ (#[],0,R.base) (by intro r h;cases h)
  intro rho hr s hs
  refine ⟨_,rfl,push s.1 _ hs ?_⟩
  simp only [List.forIn_pure_yield_eq_foldl,pure_bind,Id.run]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append,
    List.foldl_map]
  simp [pure,set_ne,Array.getElem!_set!_ne,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.cg,Scan.cur,Scan.cm,Scan.j,Scan.m,Scan.key,Scan.ikey,Scan.zk0,
    Scan.us0,Scan.us1,Scan.qb0,Scan.qb1,Scan.rb0,Scan.rb1,Dist.r1,Dist.r2,Scan.Q0,Scan.Q1,
    Scan.re,Scan.e4,Scan.iy,Scan.y,Scan.u0,Scan.u1,Scan.b0,Scan.b1,Scan.q,
    Scan.link,Scan.r,Scan.s,Scan.chi,Scan.clo,Scan.cid,Scan.dd,Scan.base,Scan.nn,Scan.tau,
    Scan.fQ,Scan.kS,Scan.act,zrow,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]

theorem param (R:Run) : (Scan.paramRow R)[Dist.cg]! = 0 := by
  simp [Scan.paramRow,Array.getElem!_set!_ne,Scan.act,Scan.kP,Scan.tau,Scan.nn,Scan.base,Scan.dd,
    Scan.q,Scan.clo,Scan.chi,zrow,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]

private theorem append (a b:Array (Array Nat))(ha:Good a)(hb:Good b) : Good (a++b) := by
  intro row hm
  simp only [Array.toList_append,List.mem_append] at hm
  exact hm.elim (ha row) (hb row)

attribute [local irreducible] Scan.reqRows

theorem rows (R:Run) : Good (Scan.rows R) := by
  unfold Scan.rows
  split
  · intro r h;cases h
  · have hf:∀cs:List CReq,∀a:Array (Array Nat),Good a→
        Good (cs.foldl (fun acc c=>acc++Scan.reqRows R c) a) := by
      intro cs
      induction cs with
      | nil=>intro a ha;exact ha
      | cons c cs ih=>intro a ha;exact ih (a++Scan.reqRows R c) (append a (Scan.reqRows R c) ha (request R c))
    refine hf R.conv #[Scan.paramRow R] ?_
    intro row hm
    simp only [Array.toList_push,Array.toList_empty,List.nil_append,List.mem_singleton] at hm
    subst row
    exact param R

theorem traffic (R:Run) :
    (Scan.rows R).toList.flatMap (fun row=>ProcDistCmpTraffic.messages
      (fun c=>ZkFormal.Algebra.Fp.ofNat row[c]!))=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro row hm
  have hz:=rows R row hm
  simp only [ProcDistCmpTraffic.messages,hz,
    show ZkFormal.Algebra.Fp.ofNat 0 ≠ 1 from by decide +kernel,if_false,List.replicate_zero]
end ZkFormal.NearV3.Candidates.ProcScanCmpSilent
