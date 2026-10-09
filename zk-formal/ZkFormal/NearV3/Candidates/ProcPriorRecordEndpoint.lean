import ZkFormal.NearV3.Candidates.ProcPriorRecordOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordEndpoint
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable ProcPriorRecordOrdinal
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

/-- A receiver/amount row must have a preceding active Record row, and cannot
follow a completed amount or a header. -/
theorem previous_record (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t (r+1) (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t (r+1) act=1)
    (hw:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1)
    (hns:cv tr t (r+1) sender=0) :
    cv tr t r (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t r act=1 ∧
    cv tr t r sender+cv tr t r receiver+cv tr t r amount=1 ∧
    cv tr t r amount*cv tr t r topLimb=0 := by
  have hf:cv tr t (r+1) ProcPriorVertical4Linear.first=0 := by
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC ProcPriorVertical4Linear.first) (by simp [ProcPriorVertical4Linear.windows]))
    by_cases he:cv tr t (r+1) ProcPriorVertical4Linear.first=1
    · have hz:=ProcPriorRecordOrigin.first_words hL hr hs he;omega
    · omega
  obtain ⟨hps,hpl⟩:=previous_stage hL hr hs hf
  have hpa:=previous_active hL hr hps hpl ha
  have hr0:r<tr.height t := by omega
  have w0:=ProcPriorRecordGeometry.words_bound hL hr0 hps
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  have nxt (x:Nat):zev (tenv tr t r pub) (.col x true)=(cv tr t (r+1) x:Int) := by
    change zev (tenv tr t r pub) (n x)=_
    rw [zev_n,Codec.nx hr]
  have wi:(cv tr t (r+1) sender:Int)+(cv tr t (r+1) receiver:Int)+(cv tr t (r+1) amount:Int)=1 := by omega
  rw [hns] at wi
  obtain ⟨q,hq⟩:=zdvd hL hr0 hps
    (.mul (.mul (header false) (n act)) (sub (words true) (n sender))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (.mul (header false) (n act)) (sub (words true) (n sender)))=2013265921*q at hq
  zs hq [header,words,cur,nxt,hpa,ha,hns,Codec.nx hr]
  rw [wi] at hq
  have wp:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1 := by omega
  obtain ⟨q,he⟩:=zdvd hL hr0 hps
    (.mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n sender) (k 1))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n sender) (k 1)))=2013265921*q at he
  zs he [words,cur,nxt,hns,Codec.nx hr]
  rw [wi] at he
  have ba:=ProcPriorRecordSound.flag hL hr0 hps amount (by simp)
  have bt:=ProcPriorRecordSound.flag hL hr0 hps topLimb (by simp)
  refine ⟨hps,hpa,wp,?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ba with hz|hz <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bt with ht|ht <;>
    simp only [hz,ht,Int.natCast_zero,Int.natCast_one] at he ⊢ <;> omega

theorem carried (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (hend:cv tr t r amount*cv tr t r topLimb=0)
    (x:Nat) (hx:x∈[record,senderFound,senderIndex,receiverFound,receiverIndex]) :
    cv tr t (r+1) x=cv tr t r x := by
  obtain ⟨q,hq⟩:=zdvd hL (show r<tr.height t by omega) hs
    (.mul sameRecord (sub (n x) (c x))) (List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
  change zev (tenv tr t r pub) (.mul sameRecord (sub (n x) (c x)))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  zs hq [sameRecord,words,notE,cur,Codec.nx hr]
  have wi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1 := by omega
  have wend:(cv tr t r amount:Int)*(cv tr t r topLimb:Int)=0 := by rw [←Int.natCast_mul,hend];rfl
  rw [wi,wend] at hq
  have l0:=Codec.lt (tr:=tr) (t:=t) r x
  have l1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  omega

theorem leaves_word (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (x:Nat) (hx:x∈[sender,receiver,amount]) (hp:cv tr t r x=1) (hn:cv tr t (r+1) x=0) :
    cv tr t r topLimb=1 := by
  have hm:.mul sameWord (sub (n x) (c x))∈constraints := by
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨x,by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx ⊢;grind only,rfl⟩
  obtain ⟨q,hq⟩:=zdvd hL (show r<tr.height t by omega) hs _ hm
  change zev (tenv tr t r pub) (.mul sameWord (sub (n x) (c x)))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  zs hq [sameWord,words,notE,cur,Codec.nx hr,hp,hn]
  have wi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1 := by omega
  rw [wi] at hq
  have bt:=ProcPriorRecordSound.flag hL (show r<tr.height t by omega) hs topLimb (by simp)
  omega
theorem sender_origin (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) :
    ∀r,r<tr.height t→cv tr t r (ProcPriorVertical4Linear.stage 3)=1→cv tr t r act=1→
    cv tr t r sender+cv tr t r receiver+cv tr t r amount=1→cv tr t r sender=0→
    ∃q,q<r ∧ cv tr t q (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t q sender=1 ∧
      cv tr t q topLimb=1 ∧ cv tr t q senderFound=cv tr t r senderFound ∧
      cv tr t q senderIndex=cv tr t r senderIndex := by
  intro r
  induction r with
  | zero=>
    intro hr hs ha hw hn
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1))) (by simp [ProcPriorVertical4Linear.windows]))
    have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
    zs hq [zev_isFirst,hf]
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC ProcPriorVertical4Linear.first) (by simp [ProcPriorVertical4Linear.windows]))
    have hz:=ProcPriorRecordOrigin.first_words hL hr hs (by omega)
    omega
  | succ r ih=>
    intro hr hs ha hw hn
    obtain ⟨hps,hpa,hpw,hend⟩:=previous_record hL hr hs ha hw hn
    have hc1:=carried hL hr hps hpw hend senderFound (by simp)
    have hc2:=carried hL hr hps hpw hend senderIndex (by simp)
    by_cases hp:cv tr t r sender=1
    · have htop:=leaves_word hL hr hps hpw sender (by simp) hp hn
      exact ⟨r,by omega,hps,hp,htop,hc1.symm,hc2.symm⟩
    · have hbp:=ProcPriorRecordSound.flag hL (show r<tr.height t by omega) hps sender (by simp)
      have hp0:cv tr t r sender=0 := by omega
      obtain ⟨q,hqr,hqs,hqsend,hqtop,hqf,hqi⟩:=ih (by omega) hps hpa hpw hp0
      exact ⟨q,by omega,hqs,hqsend,hqtop,hqf.trans hc1.symm,hqi.trans hc2.symm⟩

theorem receiver_origin (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) :
    ∀r,r<tr.height t→cv tr t r (ProcPriorVertical4Linear.stage 3)=1→cv tr t r act=1→cv tr t r amount=1→
    ∃q,q<r ∧ cv tr t q (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t q receiver=1 ∧
      cv tr t q topLimb=1 ∧ cv tr t q receiverFound=cv tr t r receiverFound ∧
      cv tr t q receiverIndex=cv tr t r receiverIndex := by
  intro r
  induction r with
  | zero=>
    intro hr hs ha hamt
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1))) (by simp [ProcPriorVertical4Linear.windows]))
    have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
    zs hq [zev_isFirst,hf]
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC ProcPriorVertical4Linear.first) (by simp [ProcPriorVertical4Linear.windows]))
    have hz:=ProcPriorRecordOrigin.first_words hL hr hs (by omega)
    omega
  | succ r ih=>
    intro hr hs ha hamt
    have hwb:=ProcPriorRecordGeometry.words_bound hL hr hs
    have hw:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1 := by omega
    have hn:cv tr t (r+1) sender=0 := by omega
    have hnrecv:cv tr t (r+1) receiver=0 := by omega
    obtain ⟨hps,hpa,hpw,hend⟩:=previous_record hL hr hs ha hw hn
    have hc1:=carried hL hr hps hpw hend receiverFound (by simp)
    have hc2:=carried hL hr hps hpw hend receiverIndex (by simp)
    by_cases hp:cv tr t r receiver=1
    · have htop:=leaves_word hL hr hps hpw receiver (by simp) hp hnrecv
      exact ⟨r,by omega,hps,hp,htop,hc1.symm,hc2.symm⟩
    · have hsend:cv tr t r sender=0 := by
        have hb:=ProcPriorRecordSound.flag hL (show r<tr.height t by omega) hps sender (by simp)
        by_cases hs1:cv tr t r sender=1
        · have htop:=leaves_word hL hr hps hpw sender (by simp) hs1 hn
          obtain ⟨q,hq⟩:=zdvd hL (show r<tr.height t by omega) hps
            (.mul (.mul (c sender) (c topLimb)) (sub (n receiver) (k 1))) (by simp [constraints])
          change zev (tenv tr t r pub) (.mul (.mul (c sender) (c topLimb)) (sub (n receiver) (k 1)))=2013265921*q at hq
          zs hq [hs1,htop,Codec.nx hr,hnrecv]
          omega
        · omega
      have hbr:=ProcPriorRecordSound.flag hL (show r<tr.height t by omega) hps receiver (by simp)
      have hpre:cv tr t r amount=1 := by omega
      obtain ⟨q,hqr,hqs,hqrecv,hqtop,hqf,hqi⟩:=ih (by omega) hps hpa hpre
      exact ⟨q,by omega,hqs,hqrecv,hqtop,hqf.trans hc1.symm,hqi.trans hc2.symm⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordEndpoint
