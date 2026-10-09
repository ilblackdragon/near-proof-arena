import ZkFormal.NearV3.Candidates.ProcPriorVerticalMemorySound
import ZkFormal.NearV3.Candidates.ProcPriorReadSound
namespace ZkFormal.NearV3.Candidates.ProcPriorVerticalReadSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear

def read : Interaction :=interaction 0 ((ProcPriorMemoryTable.interactions 67 68 69)[1]!)

structure Own (AP : AirP) (tv : Nat) : Prop where
  lt : tv<AP.tables.length
  tab : AP.tables[tv]! =table
  only : ∀t,t<AP.tables.length→t≠tv→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠68

theorem sender_eq {i : Interaction} (hi:i∈table.interactions) (hb:i.bus=68) (hs:i.send=true) :i=read := by
  have hf:table.interactions.filter (fun i=>i.bus==68 && i.send)=[read] := rfl
  have hm:i∈table.interactions.filter (fun i=>i.bus==68 && i.send) := List.mem_filter.mpr ⟨hi,by simp [hb,hs]⟩
  rw [hf] at hm
  exact List.mem_singleton.mp hm

theorem flags {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:read.multNat tr t r pub≠0) :
    cv tr t r (stage 0)=1 ∧ cv tr t r ProcPriorMemoryTable.act=1 ∧ cv tr t r ProcPriorMemoryTable.query=1 := by
  have hg:(Expr.mul (c (stage 0)) (.mul (c ProcPriorMemoryTable.act) (c ProcPriorMemoryTable.query))).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c (stage 0)) (.mul (c ProcPriorMemoryTable.act) (c ProcPriorMemoryTable.query))).eval tr t r pub=1
    · exact he
    · have heq:read.mult=[Expr.mul (c (stage 0)) (.mul (c ProcPriorMemoryTable.act) (c ProcPriorMemoryTable.query))] := rfl
      simp only [Interaction.multNat,heq,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hsbit:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC (stage 0)) (by simp [windows]))
  have hzero (x : Nat) (hx:cv tr t r x=0) :tr.cell t r x=(0:Fp) := by
    change tr.cell t r x=Fp.ofNat 0
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  change tr.cell t r (stage 0)*(tr.cell t r ProcPriorMemoryTable.act*tr.cell t r ProcPriorMemoryTable.query)=1 at hg
  have hs:cv tr t r (stage 0)=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hz|hz
    · rw [hzero _ hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by grind only)).elim
    · exact hz
  have hb (x : Nat) (hx:x∈[ProcPriorMemoryTable.act,ProcPriorMemoryTable.query,ProcPriorMemoryTable.hi,ProcPriorMemoryTable.beforeHi,ProcPriorMemoryTable.same]) :cv tr t r x≤1 := by
    have hh:=ProcPriorVerticalMemorySound.component_value hL hr hs (Table.boolC x)
      (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
    change (Table.boolC x).eval tr t r pub=0 at hh
    exact Codec.bool_of_eval (pub:=pub) hh
  have ha:=hb ProcPriorMemoryTable.act (by simp)
  have hq:=hb ProcPriorMemoryTable.query (by simp)
  refine ⟨hs,?_,?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with hz|hz
    · rw [hzero _ hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by grind only)).elim
    · exact hz
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with hz|hz
    · rw [hzero _ hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by grind only)).elim
    · exact hz

theorem message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    read.msgVal tr t r pub=((ProcPriorMemoryTable.interactions 67 68 69)[1]!).msgVal tr t r pub := rfl

/-- The actual four-stage vertical table supplies every live priorRead query.
Window predecessor/selector facts are derived from arbitrary vertical Local;
no generated clock, standalone memory table, or chosen window is assumed. -/
theorem query_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (tv : Nat) (own:Own AP tv)
    (hpub:∀msg,pubCount AP pub 68 true msg=0)
    (r : Nat) (hr:r<tr.height tc)
    (hm:ProcPriorCodecActual.priorRead.multNat tr tc r pub≠0) :
    ∃q,q<tr.height tv ∧ cv tr tv q (stage 0)=1 ∧
      cv tr tv q ProcPriorMemoryTable.tau=cv tr tc r Codec.tau ∧
      cv tr tv q ProcPriorMemoryTable.link=cv tr tc r Codec.kidx ∧
      cv tr tv q ProcPriorMemoryTable.lo=cv tr tc r Codec.apR ∧
      cv tr tv q ProcPriorMemoryTable.hi=cv tr tc r Codec.bigR ∧
      ((cv tr tv q ProcPriorMemoryTable.lo=0 ∧ cv tr tv q ProcPriorMemoryTable.hi=0) ∨
       ∃v,q=v+1 ∧ cv tr tv v ProcPriorMemoryTable.act=1 ∧ cv tr tv v ProcPriorMemoryTable.query=0 ∧
         ProcPriorMemoryTable.addr.eval tr tv v pub=ProcPriorMemoryTable.addr.eval tr tv q pub ∧
         cv tr tv v ProcPriorMemoryTable.lo=cv tr tv q ProcPriorMemoryTable.lo ∧
         cv tr tv v ProcPriorMemoryTable.hi=cv tr tv q ProcPriorMemoryTable.hi) := by
  have hi:ProcPriorCodecActual.priorRead∈AP.tables[tc]!.interactions := by
    rw [htab]
    have hh:ProcPriorCodecActual.table.interactions[14]! =ProcPriorCodecActual.priorRead := rfl
    rw [←hh,getElem!_pos _ _ (by decide)]
    exact List.getElem_mem (by decide)
  rcases recv_src hH ht hr hi (by rfl : ProcPriorCodecActual.priorRead.bus=68)
    (by rfl : ProcPriorCodecActual.priorRead.send=false) hm with hp|hs
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,i,hi,hb,hs,hmsg,hm'⟩:=hs
    have he:t'=tv := Classical.byContradiction (fun hn=>own.only t' ht' hn i hi hs hb)
    subst t'
    rw [own.tab] at hi
    have hei:=sender_eq hi hb hs
    subst i
    have hL:=local_of_holdsP hH own.lt
    rw [own.tab] at hL
    obtain ⟨hstage,ha,hquery⟩:=flags hL hq hm'
    rw [message] at hmsg
    obtain ⟨htau,hlink,hlo,hhi⟩:=ProcPriorReadSound.message_fields tr tv q tc r pub hmsg
    exact ⟨q,hq,hstage,htau,hlink,hlo,hhi,ProcPriorVerticalMemorySound.query_origin hL hq hstage ha hquery⟩
end ZkFormal.NearV3.Candidates.ProcPriorVerticalReadSound
