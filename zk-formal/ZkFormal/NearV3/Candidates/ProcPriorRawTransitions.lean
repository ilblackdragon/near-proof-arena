import ZkFormal.NearV3.Candidates.ProcPriorRawEndpoints
namespace ZkFormal.NearV3.Candidates.ProcPriorRawTransitions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem active_not_last (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) :cv tr t r ProcPriorVertical4Linear.last=0 ∧ r+1<tr.height t := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul .isLast (c act)) (by simp [constraints])
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
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) :cv tr t (r+1) (ProcPriorVertical4Linear.stage 2)=1 := by
  obtain ⟨hl,hn⟩:=active_not_last hL hr hs ha
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (sub (k 1) (c ProcPriorVertical4Linear.last)))
      (sub (n (ProcPriorVertical4Linear.stage 2)) (c (ProcPriorVertical4Linear.stage 2))))
    (List.mem_append_right _ (List.mem_map.mpr ⟨2,by decide,rfl⟩)))
  simp only [zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hn,hs,hl] at hq
  simp only [zev,Mem.tenv_last_zero hn] at hq
  have hb:=hL.bool hn (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 2)) (by simp [ProcPriorVertical4Linear.windows]))
  omega

/-- Inside a phase, a live frame cannot stop or change its instance/value
identity. This applies to arbitrary satisfying traces. -/
theorem interior (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (he:cv tr t r phaseEnd=0) :
    cv tr t (r+1) act=1 ∧
      ∀x∈[tau,vid,present,count,hdr,rec,hash],cv tr t (r+1) x=cv tr t r x := by
  have hn:=(active_not_last hL hr hs ha).2
  have hsn:=stage_next hL hr hs ha
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul nextWithin (notE (n act))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul nextWithin (notE (n act)))=2013265921*q at hq
  zs hq [nextWithin,done,notE,ha,he,Codec.nx hn]
  have hb:=flag hL hn hsn act (by simp)
  refine ⟨by omega,?_⟩
  intro x hx
  have hm:x∈[tau,vid,present,count] ∨ x∈[hdr,rec,hash] := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] using hx
  rcases hm with hm|hm
  · obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul nextWithin (sub (n x) (c x)))
      (by simp only [constraints,List.mem_append];left;left;left;left;left;exact Or.inr (List.mem_map.mpr ⟨x,hm,rfl⟩))
    change zev (tenv tr t r pub) (.mul nextWithin (sub (n x) (c x)))=2013265921*q at hq
    zs hq [nextWithin,done,ha,he,Codec.nx hn]
    have h0:=Codec.lt (tr:=tr) (t:=t) r x
    have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
    omega
  · obtain ⟨q,hq⟩:=zdvd hL hr hs (mul3 (c act) (notE (c phaseEnd)) (sub (n x) (c x)))
      (by simp only [constraints,List.mem_append];left;left;left;left;exact Or.inr (List.mem_map.mpr ⟨x,hm,rfl⟩))
    change zev (tenv tr t r pub) (mul3 (c act) (notE (c phaseEnd)) (sub (n x) (c x)))=2013265921*q at hq
    zs hq [mul3,notE,ha,he,Codec.nx hn]
    have h0:=Codec.lt (tr:=tr) (t:=t) r x
    have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
    omega

/-- Field increments are stated with their wrap case explicit. Later finite
framing bounds must exclude that case before using natural-number offsets. -/
theorem interior_increment (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (he:cv tr t r phaseEnd=0) (x:Nat) (hx:x=pos∨x=offset) :
    cv tr t (r+1) x=cv tr t r x+1 ∨
      (cv tr t r x=2013265920 ∧ cv tr t (r+1) x=0) := by
  have hn:=(active_not_last hL hr hs ha).2
  have h0:=Codec.lt (tr:=tr) (t:=t) r x
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  rcases hx with rfl|rfl
  · obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul nextWithin (sub (n pos) (.add (c pos) (k 1))))
      (by simp [constraints])
    change zev (tenv tr t r pub) (.mul nextWithin (sub (n pos) (.add (c pos) (k 1))))=2013265921*q at hq
    zs hq [nextWithin,done,ha,he,Codec.nx hn]
    omega
  · obtain ⟨q,hq⟩:=zdvd hL hr hs (mul3 (c act) (notE (c phaseEnd)) (sub (n offset) (.add (c offset) (k 1))))
      (by simp [constraints])
    change zev (tenv tr t r pub) (mul3 (c act) (notE (c phaseEnd)) (sub (n offset) (.add (c offset) (k 1))))=2013265921*q at hq
    zs hq [mul3,notE,ha,he,Codec.nx hn]
    omega
end ZkFormal.NearV3.Candidates.ProcPriorRawTransitions
