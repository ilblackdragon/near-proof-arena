import ZkFormal.NearV3.Candidates.ProcPriorIdSoundBound
namespace ZkFormal.NearV3.Candidates.ProcPriorIdSoundResult
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundBound

structure Own (AP : AirP) (ti cmp : Nat) : Prop where
  lt : ti<AP.tables.length
  tab : AP.tables[ti]! = table 70 71 72 cmp
  only : ∀t,t<AP.tables.length→t≠ti→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠72

theorem sender_eq (cmp : Nat) (hcmp:cmp≠72) {i : Interaction}
    (hi:i∈(table 70 71 72 cmp).interactions) (hb:i.bus=72) (hs:i.send=true) :
    i=(interactions 70 71 72 cmp)[2]! := by
  simp only [table,interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | rfl | simp_all

theorem sender_active {tr : Trace Fp} {ti r cmp : Nat} {pub : List Fp}
    (hL:ProcPriorIdSoundRows.At tr ti r pub)
    (hm:((interactions 70 71 72 cmp)[2]!).multNat tr ti r pub≠0) : cv tr ti r act=1 := by
  have ha:=ProcPriorIdSoundRows.flag hL (x:=act) (by simp)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h0|h1
  · have hz:((interactions 70 71 72 cmp)[2]!).multNat tr ti r pub=0:=
      Codec.mult_zero rfl (by simp only [zev_mul,zev_sub,zev_c,zev_k,notE,cur_cv,h0,Int.natCast_zero,Int.zero_mul])
    exact (hm hz).elim
  · exact h1

/-- A live found-result receive obtains its bounded index from an actual ID
sender through global bus balance. The receiver can be a Record row or another
explicitly authorized result consumer; no generated inventory is substituted. -/
theorem result_bound {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hH:HoldsP AP pub tr) {ti cmp : Nat} (own:Own AP ti cmp) (hcmp:cmp≠72)
    (n : Nat) (hpub70:∀msg,pubCount AP pub 70 true msg=0)
    (hpublic:PublicSendBound AP tr pub n) (hpub72:∀msg,pubCount AP pub 72 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=72) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) (hf:(i.msgVal tr tc r pub)[2]! = Fp.ofNat 1) :
    ((i.msgVal tr tc r pub)[3]!).toNat<n := by
  rcases recv_src hH ht hr hi hb hs hm with hp|hsrc
  · exact (hp (hpub72 _)).elim
  · obtain ⟨ts,hts,q,hq,j,hj,hbus,hdir,hmsg,hmj⟩:=hsrc
    have he:ts=ti:=Classical.byContradiction (fun hn=>own.only ts hts hn j hj hdir hbus)
    subst ts
    rw [own.tab] at hj
    have he:=sender_eq cmp hcmp hj hbus hdir
    subst j
    have hL:=local_of_holdsP hH own.lt
    rw [own.tab] at hL
    have ha:=sender_active (hL q hq) hmj
    have hfield:((interactions 70 71 72 cmp)[2]!).msgVal tr ti q pub=
        [Fp.ofNat (cv tr ti q tau),Fp.ofNat (cv tr ti q ordinal),
         Fp.ofNat (cv tr ti q found),Fp.ofNat (cv tr ti q index)] := by
      simp [interactions,Interaction.msgVal,Codec.ev_c]
    have hfound:cv tr ti q found=1 := by
      rw [←hmsg,hfield] at hf
      simp only [List.getElem!_cons_succ,List.getElem!_cons_zero] at hf
      exact ProcPriorCodecSoundPublicId.nat_eq _ _ (cv_lt _ _) (by decide +kernel) hf
    have hbound:=found_bound hH own.lt own.tab n hpub70 hpublic hq ha hfound
    rw [←hmsg,hfield]
    simp only [List.getElem!_cons_succ,List.getElem!_cons_zero,Fp.toNat_ofNat]
    rwa [Nat.mod_eq_of_lt (show cv tr ti q index<P from cv_lt q index)]
end ZkFormal.NearV3.Candidates.ProcPriorIdSoundResult
