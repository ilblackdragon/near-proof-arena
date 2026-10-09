import ZkFormal.NearV3.Candidates.ProcPriorRecordPacked
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
theorem active_not_last (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1) :cv tr t r ProcPriorVertical4Linear.last=0 ∧ r+1<tr.height t := by
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs (.mul .isLast (c act)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c ProcPriorVertical4Linear.last) (c act))=2013265921*q at hq
  zs hq [ha]
  have hb:=Codec.lt (tr:=tr) (t:=t) r ProcPriorVertical4Linear.last
  have hz:cv tr t r ProcPriorVertical4Linear.last=0:=by omega
  refine ⟨hz,?_⟩
  apply Classical.byContradiction
  intro hh
  have heq:r+1=tr.height t:=by omega
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
    (.mul .isLast (sub (c ProcPriorVertical4Linear.last) (k 1)))
    (by simp [ProcPriorVertical4Linear.windows]))
  have hl:(tenv tr t r pub).last=1 := by simp [tenv,heq]
  simp only [zev_mul,zev_sub,zev_c,zev_k,cur_cv,hz] at hq
  change (tenv tr t r pub).last*(↑(0:Nat)-↑(1:Nat))=2013265921*q at hq
  rw [hl] at hq
  omega

theorem stage_next (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1) :cv tr t (r+1) (ProcPriorVertical4Linear.stage 3)=1 := by
  obtain ⟨hl,hn⟩:=active_not_last hL hr hs ha
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (sub (k 1) (c ProcPriorVertical4Linear.last)))
      (sub (n (ProcPriorVertical4Linear.stage 3)) (c (ProcPriorVertical4Linear.stage 3))))
    (List.mem_append_right _ (List.mem_map.mpr ⟨3,by decide,rfl⟩)))
  simp only [zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hn,hs,hl] at hq
  simp only [zev,Mem.tenv_last_zero hn] at hq
  have hb:=hL.bool hn (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 3)) (by simp [ProcPriorVertical4Linear.windows]))
  omega

theorem within (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (ht:cv tr t r topLimb=0) :
    r+1<tr.height t ∧ cv tr t (r+1) (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv tr t (r+1) act=1 ∧
      (∀x∈[sender,receiver,amount,lo,mid,hi],cv tr t (r+1) x=cv tr t r x) := by
  have ha:cv tr t r act=1:=by
    have h:=ProcPriorRecordGeometry.words_bound hL hr hs
    have hb:=ProcPriorRecordSound.flag hL hr hs act (by simp)
    omega
  have hn:=(active_not_last hL hr hs ha).2
  have hsn:=stage_next hL hr hs ha
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int):=rfl
  have hwi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1:=by omega
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs (.mul sameRecord (notE (n act))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul sameRecord (notE (n act)))=2013265921*q at hq
  zs hq [sameRecord,words,cur,notE,ht,Codec.nx hn]
  rw [hwi] at hq
  have hba:=ProcPriorRecordSound.flag hL hn hsn act (by simp)
  refine ⟨hn,hsn,by omega,?_⟩
  intro x hx
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs (.mul sameWord (sub (n x) (c x)))
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩)))
  change zev (tenv tr t r pub) (.mul sameWord (sub (n x) (c x)))=2013265921*q at hq
  zs hq [sameWord,words,cur,notE,ht,Codec.nx hn]
  rw [hwi] at hq
  have h0:=Codec.lt (tr:=tr) (t:=t) r x
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  omega

theorem limb_next (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (g g':Nat) (hgg:(g=firstLimb ∧ g'=midLimb) ∨ (g=midLimb ∧ g'=topLimb))
    (hg:cv tr t r g=1) :
    r+1<tr.height t ∧ cv tr t (r+1) (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv tr t (r+1) act=1 ∧ cv tr t (r+1) g'=1 ∧
      (∀x∈[sender,receiver,amount,lo,mid,hi],cv tr t (r+1) x=cv tr t r x) := by
  have hb:=ProcPriorRecordGeometry.words_bound hL hr hs
  have hl:=ProcPriorRecordGeometry.limbs_eq hL hr hs
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  have hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1:=by
    rcases hgg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  have ht:cv tr t r topLimb=0:=by
    rcases hgg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  obtain ⟨hn,hsn,han,hfields⟩:=within hL hr hs hw ht
  have hm:(.mul (c g) (sub (n g') (k 1)))∈constraints:=by
    rcases hgg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [constraints]
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs _ hm
  change zev (tenv tr t r pub) (.mul (c g) (sub (n g') (k 1)))=2013265921*q at hq
  zs hq [hg,Codec.nx hn]
  have hbg:=Codec.lt (tr:=tr) (t:=t) (r+1) g'
  exact ⟨hn,hsn,han,by omega,hfields⟩
/-- A first-limb row represents a bounded natural u64 once its authenticated
bytes are supplied. All three limb values refer to this same first row. -/
theorem word_bounds (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1)
    (hb:∀j,j<3→∀x∈[byte0,byte1,byte2],cv tr t (r+j) x<256) :
    r+2<tr.height t ∧ cv tr t r lo<16777216 ∧ cv tr t r mid<16777216 ∧
      cv tr t r hi<65536 ∧
      cv tr t r lo+16777216*cv tr t r mid+281474976710656*cv tr t r hi<18446744073709551616 := by
  obtain ⟨hr1,hs1,_,hm1,hf1⟩:=limb_next hL hr hs firstLimb midLimb (by simp) hf
  obtain ⟨hr2,hs2,_,ht2,hf2⟩:=limb_next hL hr1 hs1 midLimb topLimb (by simp) hm1
  simp only [Nat.add_assoc,Nat.reduceAdd] at hr2 hs2 ht2 hf2
  have hlo:=(ProcPriorRecordPacked.limb hL hr hs firstLimb lo (by simp) hf
    (hb 0 (by decide) byte0 (by simp)) (hb 0 (by decide) byte1 (by simp))
    (hb 0 (by decide) byte2 (by simp))).2
  have hmid:=(ProcPriorRecordPacked.limb hL hr1 hs1 midLimb mid (by simp) hm1
    (hb 1 (by decide) byte0 (by simp)) (hb 1 (by decide) byte1 (by simp))
    (hb 1 (by decide) byte2 (by simp))).2
  have hhi:=(ProcPriorRecordPacked.top hL hr2 hs2 ht2
    (hb 2 (by decide) byte0 (by simp)) (hb 2 (by decide) byte1 (by simp))).2
  have hmid0:=hf1 mid (by simp)
  have hhi0:=(hf2 hi (by simp)).trans (hf1 hi (by simp))
  exact ⟨hr2,hlo,by omega,by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
