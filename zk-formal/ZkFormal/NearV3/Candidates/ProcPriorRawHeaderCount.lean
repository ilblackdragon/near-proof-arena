import ZkFormal.NearV3.Candidates.ProcPriorRawRecordBoundary
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHeaderCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem first_acc (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :cv tr t (r+1) acc=cv tr t r count := by
  obtain ⟨_,ha,_⟩:=ProcPriorRawPhase.first_header hL hr hs hf
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c first) (sub (n acc) (c count))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c first) (sub (n acc) (c count)))=2013265921*q at hq
  zs hq [hf,Codec.nx hn]
  have h0:=Codec.lt (tr:=tr) (t:=t) (r+1) acc
  have h1:=Codec.lt (tr:=tr) (t:=t) r count
  omega

theorem end_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hh:cv tr t r hdr=1) (he:cv tr t r phaseEnd=1) :
    cv tr t r acc=0 ∧ cv tr t r byte=0 := by
  have zero (x:Nat) (hx:x=acc∨x=byte):cv tr t r x=0 := by
    obtain ⟨q,hq⟩:=zdvd hL hr hs (mul3 (c hdr) (c phaseEnd) (c x))
      (by rcases hx with rfl|rfl <;> simp [constraints])
    change zev (tenv tr t r pub) (mul3 (c hdr) (c phaseEnd) (c x))=2013265921*q at hq
    zs hq [mul3,hh,he]
    have hx:=Codec.lt (tr:=tr) (t:=t) r x
    omega
  exact ⟨zero acc (Or.inl rfl),zero byte (Or.inr rfl)⟩

theorem digit_equation (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hh:cv tr t r hdr=1) (hf:cv tr t r first=0) (he:cv tr t r phaseEnd=0) :
    ∃q:Int,(cv tr t r acc:Int)-((cv tr t r byte:Int)+256*(cv tr t (r+1) acc:Int))=2013265921*q := by
  have hk:=kinds hL hr hs
  have hb:=flag hL hr hs act (by simp)
  have ha:cv tr t r act=1:=by omega
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (mul3 (c hdr) (notE (.add (c first) (c phaseEnd)))
      (sub (c acc) (.add (c byte) (.mul (k 256) (n acc))))) (by simp [constraints])
  change zev (tenv tr t r pub)
    (mul3 (c hdr) (notE (.add (c first) (c phaseEnd)))
      (sub (c acc) (.add (c byte) (.mul (k 256) (n acc)))))=2013265921*q at hq
  zs hq [mul3,notE,hh,hf,he,Codec.nx hn]
  exact ⟨q,by omega⟩

/-- A framed header's count is exactly its three little-endian bytes. Byte
bounds remain explicit until the authenticated Value/SHA view supplies them. -/
theorem count_bytes (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1)
    (hbytes:∀j,1≤j→j≤3→cv tr t (r+j) byte<256) :
    cv tr t r count=cv tr t (r+1) byte+256*cv tr t (r+2) byte+65536*cv tr t (r+3) byte ∧
      cv tr t r count<16777216 := by
  obtain ⟨hh,ha,ho⟩:=ProcPriorRawPhase.first_header hL hr hs hf
  have hk:=kinds hL hr hs
  have he:4=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash:=by omega
  have dig (j:Nat) (hlo:1≤j) (hhi:j≤3) :
      ∃q:Int,(cv tr t (r+j) acc:Int)-((cv tr t (r+j) byte:Int)+256*(cv tr t (r+j+1) acc:Int))=2013265921*q := by
    obtain ⟨hrj,hsj,haj,hoj,hfields⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho 4 he j (by omega)
    have hhj:cv tr t (r+j) hdr=1:=(hfields hdr (by simp)).trans hh
    have hp:=ProcPriorRawPhase.boundary_flag hL hr hs ha ho 4 he j (by omega)
    have hjne:j≠4:=by omega
    simp only [hjne,ite_false] at hp
    have hfj:=flag hL hrj hsj first (by simp)
    have hf0:cv tr t (r+j) first=0 := by
      by_cases hf1:cv tr t (r+j) first=1
      · have hz:=ProcPriorRawEndpoints.first_offset hL hrj hsj hhj hf1
        omega
      · omega
    exact digit_equation hL hrj hsj hhj hf0 hp
  obtain ⟨q1,h1⟩:=dig 1 (by decide) (by decide)
  obtain ⟨q2,h2⟩:=dig 2 (by decide) (by decide)
  obtain ⟨q3,h3⟩:=dig 3 (by decide) (by decide)
  obtain ⟨hr4,hs4,_,_,hfields4⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho 4 he 4 (by decide)
  have hp4:=ProcPriorRawPhase.boundary_flag hL hr hs ha ho 4 he 4 (by decide)
  simp only [ite_true] at hp4
  have hz:=(end_zero hL hr4 hs4 ((hfields4 hdr (by simp)).trans hh) hp4).1
  have hacc:=first_acc hL hr hs hf
  have hb1:=hbytes 1 (by decide) (by decide)
  have hb2:=hbytes 2 (by decide) (by decide)
  have hb3:=hbytes 3 (by decide) (by decide)
  simp only [Nat.add_assoc,Nat.reduceAdd] at h1 h2 h3
  have hcount:=Codec.lt (tr:=tr) (t:=t) r count
  have heq:(cv tr t r count:Int)-((cv tr t (r+1) byte:Int)+256*(cv tr t (r+2) byte:Int)+65536*(cv tr t (r+3) byte:Int))=
      2013265921*(q1+256*q2+65536*q3) := by omega
  have he_nat:cv tr t r count=cv tr t (r+1) byte+256*cv tr t (r+2) byte+65536*cv tr t (r+3) byte:=by omega
  exact ⟨he_nat,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawHeaderCount
