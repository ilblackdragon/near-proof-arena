import ZkFormal.NearV3.Candidates.ProcPriorRawHeaderCount
namespace ZkFormal.NearV3.Candidates.ProcPriorRawWithin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

/-- Header/record boundaries cannot change the frame's instance or value.
This includes boundary rows, not just phase interiors. -/
theorem fields (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hh:cv tr t r hash=0) :
    ∀x∈[tau,vid,present,count],cv tr t (r+1) x=cv tr t r x := by
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  intro x hx
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul nextWithin (sub (n x) (c x)))
    (by simp only [constraints,List.mem_append];left;left;left;left;left;exact Or.inr (List.mem_map.mpr ⟨x,hx,rfl⟩))
  change zev (tenv tr t r pub) (.mul nextWithin (sub (n x) (c x)))=2013265921*q at hq
  zs hq [nextWithin,done,ha,hh,Codec.nx hn]
  have h0:=Codec.lt (tr:=tr) (t:=t) r x
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  omega

/-- A phase's last row is fixed by its one-hot kind, so metadata is stable
from its zero-offset start through the first row of the following phase. -/
theorem phase_fields (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hh:cv tr t r hash=0) (ho:cv tr t r offset=0)
    (e:Nat) (he:e=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash) :
    ∀x∈[tau,vid,present,count],cv tr t (r+e+1) x=cv tr t r x := by
  obtain ⟨hrj,hsj,haj,_,hf⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho e he e (by omega)
  have hhj:cv tr t (r+e) hash=0:=(hf hash (by simp)).trans hh
  intro x hx
  exact (fields hL hrj hsj haj hhj x hx).trans (hf x (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with rfl|rfl|rfl|rfl <;> simp))
end ZkFormal.NearV3.Candidates.ProcPriorRawWithin
