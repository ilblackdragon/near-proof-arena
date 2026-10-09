import ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable ProcPriorRecordOrdinal
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem first_words (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r ProcPriorVertical4Linear.first=1) :
    cv tr t r sender+cv tr t r receiver+cv tr t r amount=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul .isFirst (sub (c act) (header false))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c ProcPriorVertical4Linear.first) (sub (c act) (header false)))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  zs hq [header,words,cur,hf]
  have hw:=ProcPriorRecordGeometry.words_bound hL hr hs
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  omega

theorem constant_next (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1) (hna:cv tr t (r+1) act=1)
    (hw:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1)
    (x:Nat) (hx:x∈[tau,shards]) :cv tr t (r+1) x=cv tr t r x := by
  have hm:.mul (.mul adjacent (words true)) (sub (n x) (c x))∈constraints := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
    rcases hx with rfl|rfl <;> simp [constraints]
  obtain ⟨q,hq⟩:=zdvd hL (show r<tr.height t by omega) hs _ hm
  change zev (tenv tr t r pub) (.mul (.mul adjacent (words true)) (sub (n x) (c x)))=2013265921*q at hq
  have nxt (x:Nat):zev (tenv tr t r pub) (.col x true)=(cv tr t (r+1) x:Int) := by
    change zev (tenv tr t r pub) (n x)=_
    rw [zev_n,Codec.nx hr]
  zs hq [adjacent,words,ha,hna,nxt,Codec.nx hr]
  have wi:(cv tr t (r+1) sender:Int)+(cv tr t (r+1) receiver:Int)+(cv tr t (r+1) amount:Int)=1 := by omega
  rw [wi] at hq
  have l0:=Codec.lt (tr:=tr) (t:=t) r x
  have l1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  omega

/-- Every active stage3 Record row has an earlier active header with the
same timestamp and shard count. No generated Record geometry is assumed. -/
theorem header_origin (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) :
    ∀r,r<tr.height t→cv tr t r (ProcPriorVertical4Linear.stage 3)=1→cv tr t r act=1→
    ∃f,f≤r ∧ cv tr t f (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t f act=1 ∧
      cv tr t f sender+cv tr t f receiver+cv tr t f amount=0 ∧
      cv tr t f tau=cv tr t r tau ∧ cv tr t f shards=cv tr t r shards := by
  intro r
  induction r with
  | zero=>
    intro hr hs ha
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1))) (by simp [ProcPriorVertical4Linear.windows]))
    have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
    zs hq [zev_isFirst,hf]
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC ProcPriorVertical4Linear.first) (by simp [ProcPriorVertical4Linear.windows]))
    exact ⟨0,Nat.le_refl _,hs,ha,first_words hL hr hs (by omega),rfl,rfl⟩
  | succ r ih=>
    intro hr hs ha
    by_cases hw:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=0
    · exact ⟨r+1,Nat.le_refl _,hs,ha,hw,rfl,rfl⟩
    have hwbound:=ProcPriorRecordGeometry.words_bound hL hr hs
    have hw1:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1 := by omega
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC ProcPriorVertical4Linear.first) (by simp [ProcPriorVertical4Linear.windows]))
    have hf:cv tr t (r+1) ProcPriorVertical4Linear.first=0 := by
      by_cases hh:cv tr t (r+1) ProcPriorVertical4Linear.first=1
      · exact (hw (first_words hL hr hs hh)).elim
      · omega
    obtain ⟨hps,hpl⟩:=previous_stage hL hr hs hf
    have hpa:=previous_active hL hr hps hpl ha
    obtain ⟨f,hfr,hfs,hfa,hfw,hft,hfn⟩:=ih (by omega) hps hpa
    have ht:=constant_next hL hr hps hpa ha hw1 tau (by simp)
    have hn:=constant_next hL hr hps hpa ha hw1 shards (by simp)
    exact ⟨f,by omega,hfs,hfa,hfw,hft.trans ht.symm,hfn.trans hn.symm⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordOrigin
