import ZkFormal.NearV3.Candidates.ProcPriorVerticalLastWrite
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite

def memory (tr : Trace Fp) :Trace Fp :=HorizontalTrace.project ProcPriorCodecFamilyRead.offset tr

def Ordered (tr : Trace Fp) :Prop :=
  ∀s,s<tr.height 0→Live (memory tr) 0 s→∀r,r≤s→address (memory tr) 0 r≤address (memory tr) 0 s

def Bounded (tr : Trace Fp) :Prop :=
  ∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<P

def StampOrdered (tr : Trace Fp) :Prop :=
  ∀r,r+1<tr.height 0→Live (memory tr) 0 r→Live (memory tr) 0 (r+1)→
    address (memory tr) 0 r=address (memory tr) 0 (r+1)→cv (memory tr) 0 (r+1) query=0→
    cv (memory tr) 0 r stamp<cv (memory tr) 0 (r+1) stamp

/-- Every actual physical prior68 consumer reads initialized zero when no matching memory
write exists, or reads a matching write whose physical position and original
stamp dominate every matching write. Comparator order/range obligations are
explicit; decoded-original interpretation of those writes is not asserted. -/
theorem consumer {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorCodecActualFamily.tables)
    (hpub:∀msg,pubCount AP pub 68 true msg=0)
    (ho:Ordered tr) (hb:Bounded tr) (hst:StampOrdered tr)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorCodecActualFamily.tables[0]! := by rw [htables]
  rcases recv_src hH ht hr hi hib his him with hp|hs
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hs
    have he:t'=0 := Classical.byContradiction (fun hn=>ProcPriorCodecFamilyRead.other_tables htables t' ht' hn j hj hjs hjb)
    subst t'
    rw [htab] at hj
    have hej:=ProcPriorCodecFamilyRead.sender_eq hj hjb hjs
    subst j
    rw [ProcPriorCodecFamilyRead.projected_message] at hmsg
    rw [ProcPriorCodecFamilyRead.projected_mult] at hjm
    have hL:=local_of_holdsP hH ht0
    rw [htab] at hL
    have hp:=ProcPriorCodecFamilyRead.projected_local hL
    obtain ⟨hstage,ha,hquery⟩:=ProcPriorVerticalReadSound.flags hp hq hjm
    exact ⟨q,hq,⟨hstage,ha⟩,hquery,hmsg,
      ProcPriorVerticalLastWrite.query_last_write hp ho hb hst hq ⟨hstage,ha⟩ hquery⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyLastWrite
