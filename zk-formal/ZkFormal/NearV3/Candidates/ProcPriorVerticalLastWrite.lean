import ZkFormal.NearV3.Candidates.ProcPriorMemoryStampMax
import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead
namespace ZkFormal.NearV3.Candidates.ProcPriorVerticalLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder

def Live (tr : Trace Fp) (t r : Nat) :Prop :=
  cv tr t r (ProcPriorVertical4Linear.stage 0)=1 ∧ cv tr t r act=1

def Result (tr : Trace Fp) (t q : Nat) :Prop :=
  ((cv tr t q lo=0 ∧ cv tr t q hi=0) ∧
    ∀w,w<tr.height t→Live tr t w→cv tr t w query=0→address tr t w≠address tr t q) ∨
  ∃v,q=v+1 ∧ Live tr t v ∧ cv tr t v query=0 ∧
    address tr t v=address tr t q ∧ cv tr t v lo=cv tr t q lo ∧ cv tr t v hi=cv tr t q hi ∧
    ∀u,u<tr.height t→Live tr t u→cv tr t u query=0→address tr t u=address tr t q→
      u≤v ∧ cv tr t u stamp≤cv tr t v stamp

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem live_local (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) {r : Nat}
    (hr:r<tr.height t) (ha:Live tr t r) :ProcPriorMemorySoundRows.At tr t r pub := by
  obtain ⟨hl,hr1⟩:=ProcPriorVerticalMemorySound.active_not_last hL hr ha.1 ha.2
  exact ProcPriorVerticalMemorySound.row_local hL hr1 ha.1 hl

theorem live_prev (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) {r : Nat}
    (hr:r+1<tr.height t) (ha:Live tr t (r+1)) :Live tr t r := by
  obtain ⟨hs,hl⟩:=ProcPriorVerticalMemorySound.stage_prev hL hr ha.1
  have hm:=ProcPriorVerticalMemorySound.row_local hL hr hs hl
  exact ⟨hs,ProcPriorMemorySoundRows.active_prev hm hr ha.2⟩

theorem live_prefix (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (s : Nat) (hs:s<tr.height t) (ha:Live tr t s) (r : Nat) (hr:r≤s) :Live tr t r := by
  induction s generalizing r with
  | zero=>have :r=0 := by omega
          subst r;exact ha
  | succ s ih=>
    by_cases he:r=s+1
    · subst r;exact ha
    · exact ih (by omega) (live_prev hL hs ha) r (by omega)

/-- Full last-write and maximal-stamp extraction for actual stage0 rows.
The standalone LocalM hypothesis is eliminated. Comparator-derived order
and bounded-address obligations remain explicit and are not native witnesses. -/
theorem query_last_write (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (ho:∀s,s<tr.height t→Live tr t s→∀r,r≤s→address tr t r≤address tr t s)
    (hb:∀r,r<tr.height t→Live tr t r→address tr t r<P)
    (hst:∀r,r+1<tr.height t→Live tr t r→Live tr t (r+1)→address tr t r=address tr t (r+1)→
      cv tr t (r+1) query=0→cv tr t r stamp<cv tr t (r+1) stamp)
    {q : Nat} (hq:q<tr.height t) (hqa:Live tr t q) (hqq:cv tr t q query=1) :Result tr t q :=
  ProcPriorMemoryStampMax.query_max_stamp (Live tr t) (fun _ h=>h.2)
    (live_prefix hL) (fun _ hr ha=>live_local hL hr ha) ho hst hb hq hqa hqq

/-- Actual paired/triple-packed family validity supplies all local/prefix
hypotheses. Only natural comparator order and operand provenance remain. -/
theorem family_last_write {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorCodecActualFamily.tables)
    (ho:∀s,s<tr.height 0→Live (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 s→
      ∀r,r≤s→address (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 r≤
        address (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 s)
    (hb:∀r,r<tr.height 0→Live (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 r→
      address (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 r<P)
    (hst:∀r,r+1<tr.height 0→Live (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 r→
      Live (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 (r+1)→
      address (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 r=
        address (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 (r+1)→
      cv (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 (r+1) query=0→
      cv (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 r stamp<
        cv (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 (r+1) stamp)
    {q : Nat} (hq:q<tr.height 0)
    (hqa:Live (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 q)
    (hqq:cv (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 q query=1) :
    Result (HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr) 0 q := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht
  have he:AP.tables[0]! =ProcPriorCodecActualFamily.tables[0]! := by rw [htables]
  rw [he] at hL
  exact query_last_write (ProcPriorCodecFamilyRead.projected_local hL) ho hb hst hq hqa hqq
end ZkFormal.NearV3.Candidates.ProcPriorVerticalLastWrite
