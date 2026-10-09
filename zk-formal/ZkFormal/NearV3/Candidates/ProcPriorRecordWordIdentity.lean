import ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordWordIdentity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem within (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (ht:cv tr t r topLimb=0) :
    cv tr t (r+1) tau=cv tr t r tau ∧ cv tr t (r+1) record=cv tr t r record := by
  obtain ⟨hn,hsn,han,hfields⟩:=ProcPriorRecordWordTraversal.within hL hr hs hw ht
  have ha:cv tr t r act=1:=by
    have h:=ProcPriorRecordGeometry.words_bound hL hr hs
    have hb:=ProcPriorRecordSound.flag hL hr hs act (by simp)
    omega
  have hwi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1:=by omega
  have hwn:(cv tr t (r+1) sender:Int)+(cv tr t (r+1) receiver:Int)+(cv tr t (r+1) amount:Int)=1:=by
    rw [hfields sender (by simp),hfields receiver (by simp),hfields amount (by simp)]
    exact hwi
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int):=rfl
  have nex (x:Nat):zev (tenv tr t r pub) (.col x true)=(cv tr t (r+1) x:Int):=by
    change zev (tenv tr t r pub) (n x)=_
    simp only [zev_n,Codec.nx hn]
  constructor
  · obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs
      (.mul (.mul adjacent (words true)) (sub (n tau) (c tau))) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul (.mul adjacent (words true)) (sub (n tau) (c tau)))=2013265921*q at hq
    zs hq [adjacent,words,cur,nex,ha,han,Codec.nx hn]
    rw [hwn] at hq
    have h0:=Codec.lt (tr:=tr) (t:=t) r tau
    have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) tau
    omega
  · obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs
      (.mul sameRecord (sub (n record) (c record))) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul sameRecord (sub (n record) (c record)))=2013265921*q at hq
    zs hq [sameRecord,words,notE,cur,ht,Codec.nx hn]
    rw [hwi] at hq
    have h0:=Codec.lt (tr:=tr) (t:=t) r record
    have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) record
    omega
theorem limb_identity (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (j:Nat) (hj:j<3) :
    cv tr t (r+j) tau=cv tr t r tau ∧ cv tr t (r+j) record=cv tr t r record := by
  obtain ⟨hr1,hs1,_,hm1,_⟩:=ProcPriorRecordWordTraversal.limb_next hL hr hs firstLimb midLimb (by simp) hf
  have facts (q g:Nat) (hq:q<tr.height t) (hsq:cv tr t q (ProcPriorVertical4Linear.stage 3)=1)
      (hg:g=firstLimb ∨ g=midLimb) (hflag:cv tr t q g=1) :
      cv tr t q sender+cv tr t q receiver+cv tr t q amount=1 ∧ cv tr t q topLimb=0 := by
    have he:=ProcPriorRecordGeometry.limbs_eq hL hq hsq
    have hb:=ProcPriorRecordGeometry.words_bound hL hq hsq
    have ha:=ProcPriorRecordSound.flag hL hq hsq act (by simp)
    rcases hg with rfl|rfl <;> constructor <;> omega
  have f0:=facts r firstLimb hr hs (by simp) hf
  have f1:=facts (r+1) midLimb hr1 hs1 (by simp) hm1
  have h0:=within hL hr hs f0.1 f0.2
  have h1:=within hL hr1 hs1 f1.1 f1.2
  simp only [Nat.add_assoc,Nat.reduceAdd] at h1
  have casesj:j=0 ∨ j=1 ∨ j=2:=by omega
  rcases casesj with rfl|rfl|rfl
  · exact ⟨rfl,rfl⟩
  · exact h0
  · exact ⟨h1.1.trans h0.1,h1.2.trans h0.2⟩

end ZkFormal.NearV3.Candidates.ProcPriorRecordWordIdentity
