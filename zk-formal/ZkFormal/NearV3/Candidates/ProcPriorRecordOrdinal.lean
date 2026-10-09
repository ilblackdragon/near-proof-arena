import ZkFormal.NearV3.Candidates.ProcPriorRecordGeometry
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem zdvd (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (e:Expr) (he:e∈constraints) :
    ∃q:Int,zev (tenv tr t r pub) (ProcPriorVertical4Linear.expression e)=2013265921*q := by
  have hh:=ProcPriorRecordSound.component_value hL hr hs e he
  rw [eval_eq] at hh
  have hd:=(Lean.Grind.IsCharP.intCast_eq_zero_iff (α:=Fp) P _).mp hh
  rw [P_val] at hd
  exact ⟨zev (tenv tr t r pub) (ProcPriorVertical4Linear.expression e)/2013265921,by omega⟩

theorem previous_stage (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t (r+1) (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t (r+1) ProcPriorVertical4Linear.first=0) :
    cv tr t r (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t r ProcPriorVertical4Linear.last=0 := by
  have hr0:r<tr.height t := by omega
  have hb:=hL.bool hr0 (ProcPriorVerticalMemorySound.window_member
    (Table.boolC ProcPriorVertical4Linear.last) (by simp [ProcPriorVertical4Linear.windows]))
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul .isTransition (sub (n ProcPriorVertical4Linear.first) (c ProcPriorVertical4Linear.last)))
    (by simp [ProcPriorVertical4Linear.windows]))
  zs hq [Codec.nx hr,hf]
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have hl:cv tr t r ProcPriorVertical4Linear.last=0 := by omega
  obtain ⟨q,he⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (sub (k 1) (c ProcPriorVertical4Linear.last)))
      (sub (n (ProcPriorVertical4Linear.stage 3)) (c (ProcPriorVertical4Linear.stage 3)))) (by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨3,by simp,rfl⟩))
  zs he [Codec.nx hr,hl,hs]
  simp only [zev,Mem.tenv_last_zero hr] at he
  have hb3:=hL.bool hr0 (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 3)) (by simp [ProcPriorVertical4Linear.windows]))
  exact ⟨by omega,hl⟩

theorem header_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1) (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=0) :
    cv tr t r record=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (header false) (c record)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (header false) (c record))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  zs hq [header,words,cur,ha]
  have hi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=0 := by omega
  rw [hi] at hq
  have hh:=Codec.lt (tr:=tr) (t:=t) r record
  omega

/-- The virtual first row of Record contains no word, so an active first row
starts with ordinal zero. -/
theorem first_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1) (hf:cv tr t r ProcPriorVertical4Linear.first=1) :
    cv tr t r record=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul .isFirst (sub (c act) (header false))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c ProcPriorVertical4Linear.first) (sub (c act) (header false)))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  zs hq [header,words,cur,hf]
  have hw:=ProcPriorRecordGeometry.words_bound hL hr hs
  apply header_zero hL hr hs ha
  omega
theorem previous_active (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hl:cv tr t r ProcPriorVertical4Linear.last=0) (ha:cv tr t (r+1) act=1) :
    cv tr t r act=1 := by
  obtain ⟨q,hq⟩:=zdvd hL (show r<tr.height t by omega) hs
    (.mul (.mul .isTransition (notE (c act))) (n act)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (.mul (notE (c ProcPriorVertical4Linear.last)) (notE (c act))) (n act))=2013265921*q at hq
  zs hq [notE,hl,Codec.nx hr,ha]
  have hb:=ProcPriorRecordSound.flag hL (show r<tr.height t by omega) hs act (by simp)
  omega

theorem next_bound (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hns:cv tr t (r+1) (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1) (hna:cv tr t (r+1) act=1) :
    cv tr t (r+1) record≤cv tr t r record+1 := by
  have hr0:r<tr.height t := by omega
  have w0:=ProcPriorRecordGeometry.words_bound hL hr0 hs
  have w1:=ProcPriorRecordGeometry.words_bound hL hr hns
  by_cases hw1:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=0
  · have hz:=header_zero hL hr hns hna hw1
    omega
  have hw1':cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1 := by omega
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int) := rfl
  have nxt (x:Nat):zev (tenv tr t r pub) (.col x true)=(cv tr t (r+1) x:Int) := by
    change zev (tenv tr t r pub) (n x)=_
    rw [zev_n,Codec.nx hr]
  have wi1:(cv tr t (r+1) sender:Int)+(cv tr t (r+1) receiver:Int)+(cv tr t (r+1) amount:Int)=1 := by omega
  have l1:=Codec.lt (tr:=tr) (t:=t) (r+1) record
  have l0:=Codec.lt (tr:=tr) (t:=t) r record
  by_cases hw0:cv tr t r sender+cv tr t r receiver+cv tr t r amount=0
  · obtain ⟨q,hq⟩:=zdvd hL hr0 hs
      (.mul (.mul (header false) (words true)) (n record)) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul (.mul (header false) (words true)) (n record))=2013265921*q at hq
    have wi0:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=0 := by omega
    zs hq [header,words,cur,nxt,ha,Codec.nx hr]
    rw [wi0,wi1] at hq
    omega
  have wi0:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1 := by omega
  have ba:=ProcPriorRecordSound.flag hL hr0 hs amount (by simp)
  have bt:=ProcPriorRecordSound.flag hL hr0 hs topLimb (by simp)
  obtain ⟨qc,hc⟩:=zdvd hL hr0 hs (.mul sameRecord (sub (n record) (c record))) (by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨record,by simp,rfl⟩)
  change zev (tenv tr t r pub) (.mul sameRecord (sub (n record) (c record)))=2013265921*qc at hc
  obtain ⟨qi,hi⟩:=zdvd hL hr0 hs
    (.mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n record) (.add (c record) (k 1)))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n record) (.add (c record) (k 1))))=2013265921*qi at hi
  zs hc [sameRecord,words,notE,cur,nxt,Codec.nx hr]
  zs hi [words,cur,nxt,Codec.nx hr]
  rw [wi0] at hc
  rw [wi1] at hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ba with ha0|ha0 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bt with ht0|ht0 <;>
    rw [ha0,ht0] at hc hi <;> simp only [Int.natCast_zero,Int.natCast_one] at hc hi <;> omega

/-- An active original-record ordinal never exceeds its physical row index.
This includes entry into the actual vertical Record window. -/
theorem ordinal_le_row (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) :
    ∀r,r<tr.height t→cv tr t r (ProcPriorVertical4Linear.stage 3)=1→cv tr t r act=1→cv tr t r record≤r := by
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
    have hh:=first_zero hL hr hs ha (by omega)
    omega
  | succ r ih=>
    intro hr hs ha
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC ProcPriorVertical4Linear.first) (by simp [ProcPriorVertical4Linear.windows]))
    by_cases hf:cv tr t (r+1) ProcPriorVertical4Linear.first=1
    · have hh:=first_zero hL hr hs ha hf
      omega
    · have hf0:cv tr t (r+1) ProcPriorVertical4Linear.first=0 := by omega
      obtain ⟨hps,hpl⟩:=previous_stage hL hr hs hf0
      have hpa:=previous_active hL hr hps hpl ha
      have hp:=ih (by omega) hps hpa
      have hn:=next_bound hL hr hps hs hpa ha
      omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
