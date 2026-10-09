import ZkFormal.NearV3.Candidates.ProcRecordConcatGeometry
import ZkFormal.NearV3.Candidates.ProcRecordBlockLocal
namespace ZkFormal.NearV3.Candidates.ProcRecordConcatActive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcRecordConcatTraffic ProcRecordConcatCells ProcRecordConcatGeometry ProcPriorCells

theorem start_pos (ids : NativeBlock→List Nat) (pre : List NativeBlock) (h:pre≠[]) :
    0<start ids pre := by
  cases pre with
  | nil=>contradiction
  | cons b bs=>simp [start,rows,List.flatMap_cons,ProcRecordConcatTraffic.block_length]; omega

theorem native_links (b : NativeBlock) (hb:b.Valid) : ∀r∈b.old.links,LinkOk r := by
  have hd:=hb.2.2.2.1
  cases hp:b.prior with
  | none =>
    rw [hp] at hd
    have he:b.old=NearSpec.Bandwidth.State.initial:=(Option.some.inj hd).symm
    simp [he,NearSpec.Bandwidth.State.initial]
  | some raw =>
    rw [hp] at hd
    exact (ProcPriorDecode.decode_exact raw b.old hd).2.1

theorem active (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hb:∀b∈bs,b.Valid)
    (hfirst:∀b rest,bs=b::rest→b.run.tau=0)
    (hnext:∀pre b c rest,bs=pre++b::c::rest→c.run.tau=b.run.tau+1)
    (r : Nat) (hr:r<(rows ids bs).length) (e : Expr)
    (he:e∈ProcPriorRecordTable.constraints) :
    e.evalWith (env (cell ids bs r) (cell ids bs (r+1))
      (if r=0 then 1 else 0) 0 1)=0 := by
  obtain ⟨pre,b,post,i,hbs,hi,hr⟩:=active_cases ids bs r hr
  have hf:(if start ids pre+i=0 then (1:Fp) else 0)=0 ∨ b.run.tau=0 := by
    by_cases hz:start ids pre+i=0
    · right
      have hp:pre=[] := by
        by_cases hh:pre=[]
        · exact hh
        · have:=start_pos ids pre hh; omega
      exact hfirst b post (by simpa [hp] using hbs)
    · left; exact ite_eq_right hz
  have hn:cell ids bs (start ids pre+i+1)=
      ProcRecordBlockLocal.after (ids b) b.run.tau b.old.links (post.head?.map ids) (i+1) := by
    by_cases hin:i+1<blockLength b
    · rw [show start ids pre+i+1=start ids pre+(i+1) by omega,
        block_lookup ids bs pre post b hbs (i+1) hin]
      exact (ite_eq_left hin).symm
    · have hiend:i+1=blockLength b:=by omega
      change ¬i+1<1+9*b.old.links.length at hin
      rw [show start ids pre+i+1=start ids pre+blockLength b by omega,
        after_block ids bs pre post b hbs,ProcRecordBlockLocal.after,ite_eq_right hin]
      cases post with
      | nil=>rfl
      | cons c rest=>
        simp only [List.head?_cons,Option.map_some,ProcRecordBlockLocal.finish]
        unfold blockCell
        rw [ProcPriorRecordTrace.header,hnext pre b c rest hbs]
  rw [hr,block_lookup ids bs pre post b hbs i hi,hn]
  have hf':(if i=0 then (if start ids pre+i=0 then (1:Fp) else 0) else 0)=
      (if start ids pre+i=0 then 1 else 0) := by
    by_cases hi0:i=0
    · simp [hi0]
    · have hn:start ids pre+i≠0:=by omega
      simp [hi0,hn]
  have hh:=ProcRecordBlockLocal.constraints (ids b) b.run.tau b.old.links
    (native_links b (hb b (by simp [hbs]))) i hi
    (if start ids pre+i=0 then 1 else 0) hf (post.head?.map ids) e he
  rw [hf'] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcRecordConcatActive
