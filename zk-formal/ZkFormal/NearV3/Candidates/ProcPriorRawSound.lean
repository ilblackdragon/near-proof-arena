import ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyWrite
namespace ZkFormal.NearV3.Candidates.ProcPriorRawSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem component_value (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (e:Expr) (he:e∈constraints) :
    (ProcPriorVertical4Linear.expression e).eval tr t r pub=0 := by
  have hm:.mul (c (ProcPriorVertical4Linear.stage 2)) (ProcPriorVertical4Linear.expression e)∈
      ProcPriorVertical4Linear.table.constraints := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorRawFrame.table 59 73 B_VBYTES 74 75,2),by simp [ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have hh:=hL r hr _ hm
  have hc:tr.cell t r (ProcPriorVertical4Linear.stage 2)=(1:Fp) := by
    change tr.cell t r (ProcPriorVertical4Linear.stage 2)=Fp.ofNat 1
    rw [←hs];exact (Fp.ofNat_toNat _).symm
  change tr.cell t r (ProcPriorVertical4Linear.stage 2)*(ProcPriorVertical4Linear.expression e).eval tr t r pub=0 at hh
  rw [hc] at hh
  grind only

theorem flag (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (x:Nat) (hx:x∈[act,present,hdr,rec,hash,phaseEnd,recordEnd,empty,first,byteGate,lengthGate]) :cv tr t r x≤1 := by
  have hm:Table.boolC x∈constraints := by simp only [constraints,List.mem_append];left;left;left;left;left;left;left;exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hh:=component_value hL hr hs _ hm
  exact Codec.bool_of_eval (pub:=pub) hh

theorem zdvd (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (e:Expr) (he:e∈constraints) :
    ∃q:Int,zev (tenv tr t r pub) (ProcPriorVertical4Linear.expression e)=2013265921*q := by
  have hh:=component_value hL hr hs e he
  rw [eval_eq] at hh
  have hd:=(Lean.Grind.IsCharP.intCast_eq_zero_iff (α:=Fp) P _).mp hh
  rw [P_val] at hd
  exact ⟨zev (tenv tr t r pub) (ProcPriorVertical4Linear.expression e)/2013265921,by omega⟩

theorem kinds (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1) :
    cv tr t r act=cv tr t r hdr+cv tr t r rec+cv tr t r hash := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (sub (c act) (.add (c hdr) (.add (c rec) (c hash)))) (by simp [constraints])
  change zev (tenv tr t r pub) (sub (c act) (.add (c hdr) (.add (c rec) (c hash))))=2013265921*q at hq
  zs hq []
  have ha:=flag hL hr hs act (by simp)
  have hh:=flag hL hr hs hdr (by simp)
  have hr':=flag hL hr hs rec (by simp)
  have hh':=flag hL hr hs hash (by simp)
  omega

theorem byte_gate (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hp:cv tr t r present=1) :cv tr t r byteGate=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (sub (c byteGate) (.mul (c act) (c present))) (by simp [constraints])
  change zev (tenv tr t r pub) (sub (c byteGate) (.mul (c act) (c present)))=2013265921*q at hq
  zs hq [ha,hp]
  have hb:=flag hL hr hs byteGate (by simp)
  omega

theorem absent_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hp:cv tr t r present=0) :cv tr t r byte=0 ∧ cv tr t r count=0 := by
  have hzero (x:Nat) (hx:x=byte∨x=count):cv tr t r x=0 := by
    obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (notE (c present)) (c x)) (by rcases hx with rfl|rfl <;> simp [constraints])
    change zev (tenv tr t r pub) (.mul (notE (c present)) (c x))=2013265921*q at hq
    zs hq [notE,hp]
    have hh:=Codec.lt (tr:=tr) (t:=t) r x
    omega
  exact ⟨hzero byte (Or.inl rfl),hzero count (Or.inr rfl)⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawSound
