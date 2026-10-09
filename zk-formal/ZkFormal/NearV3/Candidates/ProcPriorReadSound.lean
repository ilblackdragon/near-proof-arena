import ZkFormal.NearV3.Candidates.ProcPriorMemorySound
namespace ZkFormal.NearV3.Candidates.ProcPriorReadSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched

/-- Exclusive ownership of actual priorRead sends. It does not assert any
semantic value, generated row shape, or authenticity of the write inventory. -/
structure Own (AP : AirP) (tm : Nat) : Prop where
  lt : tm<AP.tables.length
  tab : AP.tables[tm]! =ProcPriorMemoryGated.table 67 68 69
  only : ∀t,t<AP.tables.length→t≠tm→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠68

theorem sender_eq {i : Interaction}
    (hi:i∈(ProcPriorMemoryGated.table 67 68 69).interactions)
    (hb:i.bus=68) (hs:i.send=true) : i=(ProcPriorMemoryTable.interactions 67 68 69)[1]! := by
  have hf:(ProcPriorMemoryGated.table 67 68 69).interactions.filter (fun i=>i.bus==68 && i.send)=
      [(ProcPriorMemoryTable.interactions 67 68 69)[1]!] := rfl
  have hm:i∈(ProcPriorMemoryGated.table 67 68 69).interactions.filter (fun i=>i.bus==68 && i.send) :=
    List.mem_filter.mpr ⟨hi,by simp [hb,hs]⟩
  rw [hf] at hm
  exact List.mem_singleton.mp hm

theorem sender_flags {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL:ProcPriorMemorySound.LocalM tr t pub) (hr:r<tr.height t)
    (hm:((ProcPriorMemoryTable.interactions 67 68 69)[1]!).multNat tr t r pub≠0) :
    cv tr t r ProcPriorMemoryTable.act=1 ∧ cv tr t r ProcPriorMemoryTable.query=1 := by
  have ha:=ProcPriorMemorySound.flag hL hr (x:=ProcPriorMemoryTable.act) (by simp)
  have hq:=ProcPriorMemorySound.flag hL hr (x:=ProcPriorMemoryTable.query) (by simp)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha|ha
  · have hz:((ProcPriorMemoryTable.interactions 67 68 69)[1]!).multNat tr t r pub=0 :=
      Codec.mult_zero rfl (by simp only [zev_mul,zev_c,cur_cv,ha,Int.natCast_zero,Int.zero_mul])
    exact (hm hz).elim
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with hq|hq
    · have hz:((ProcPriorMemoryTable.interactions 67 68 69)[1]!).multNat tr t r pub=0 :=
        Codec.mult_zero rfl (by simp only [zev_mul,zev_c,cur_cv,hq,Int.natCast_zero,Int.mul_zero])
      exact (hm hz).elim
    · exact ⟨ha,hq⟩

theorem message_fields (tr : Trace Fp) (tm q tc r : Nat) (pub : List Fp)
    (he:((ProcPriorMemoryTable.interactions 67 68 69)[1]!).msgVal tr tm q pub=
      ProcPriorCodecActual.priorRead.msgVal tr tc r pub) :
    cv tr tm q ProcPriorMemoryTable.tau=cv tr tc r Codec.tau ∧
    cv tr tm q ProcPriorMemoryTable.link=cv tr tc r Codec.kidx ∧
    cv tr tm q ProcPriorMemoryTable.lo=cv tr tc r Codec.apR ∧
    cv tr tm q ProcPriorMemoryTable.hi=cv tr tc r Codec.bigR := by
  simp only [ProcPriorMemoryTable.interactions,ProcPriorCodecActual.priorRead,
    List.getElem!_cons_succ,List.getElem!_cons_zero,Interaction.msgVal,List.map_cons,List.map_nil,
    Codec.ev_c,List.cons.injEq] at he
  exact ⟨ProcPriorCodecSoundPublicId.nat_eq _ _ (cv_lt _ _) (cv_lt _ _) he.1,
    ProcPriorCodecSoundPublicId.nat_eq _ _ (cv_lt _ _) (cv_lt _ _) he.2.1,
    ProcPriorCodecSoundPublicId.nat_eq _ _ (cv_lt _ _) (cv_lt _ _) he.2.2.1,
    ProcPriorCodecSoundPublicId.nat_eq _ _ (cv_lt _ _) (cv_lt _ _) he.2.2.2.1⟩

/-- Genuine global bus balance selects an actual memory query, whose local
read value is zero or the preceding write. This does not yet identify that
write with the greatest decoded-original ordinal; ordering and authenticated
RawFrame/ID/record write provenance remain separate obligations. -/
theorem query_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (tm : Nat) (own:Own AP tm)
    (hpub:∀msg,pubCount AP pub 68 true msg=0)
    (r : Nat) (hr:r<tr.height tc)
    (hm:ProcPriorCodecActual.priorRead.multNat tr tc r pub≠0) :
    ∃q,q<tr.height tm ∧ cv tr tm q ProcPriorMemoryTable.act=1 ∧
      cv tr tm q ProcPriorMemoryTable.query=1 ∧
      ((ProcPriorMemoryTable.interactions 67 68 69)[1]!).msgVal tr tm q pub=
        ProcPriorCodecActual.priorRead.msgVal tr tc r pub ∧
      ((cv tr tm q ProcPriorMemoryTable.lo=0 ∧ cv tr tm q ProcPriorMemoryTable.hi=0) ∨
       ∃v,q=v+1 ∧ cv tr tm v ProcPriorMemoryTable.act=1 ∧ cv tr tm v ProcPriorMemoryTable.query=0 ∧
         ProcPriorMemoryTable.addr.eval tr tm v pub=ProcPriorMemoryTable.addr.eval tr tm q pub ∧
         cv tr tm v ProcPriorMemoryTable.lo=cv tr tm q ProcPriorMemoryTable.lo ∧
         cv tr tm v ProcPriorMemoryTable.hi=cv tr tm q ProcPriorMemoryTable.hi) := by
  have hi:ProcPriorCodecActual.priorRead∈AP.tables[tc]!.interactions := by
    rw [htab]
    have hh:ProcPriorCodecActual.table.interactions[14]! =ProcPriorCodecActual.priorRead := rfl
    rw [←hh,getElem!_pos _ _ (by decide)]
    exact List.getElem_mem (by decide)
  rcases recv_src hH ht hr hi (by rfl : ProcPriorCodecActual.priorRead.bus=68)
    (by rfl : ProcPriorCodecActual.priorRead.send=false) hm with hp|hs
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,i,hi,hb,hs,hmsg,hm'⟩:=hs
    have he:t'=tm := Classical.byContradiction (fun hn=>own.only t' ht' hn i hi hs hb)
    subst t'
    rw [own.tab] at hi
    have hei:=sender_eq hi hb hs
    subst i
    have hLG:=local_of_holdsP hH own.lt
    rw [own.tab] at hLG
    have hL:ProcPriorMemorySound.LocalM tr tm pub := by
      intro rr hrr e he
      exact hLG rr hrr e (List.mem_append_left _ he)
    obtain ⟨ha,hqq⟩:=sender_flags hL hq hm'
    exact ⟨q,hq,ha,hqq,hmsg,ProcPriorMemorySound.query_origin hL hq ha hqq⟩
end ZkFormal.NearV3.Candidates.ProcPriorReadSound
