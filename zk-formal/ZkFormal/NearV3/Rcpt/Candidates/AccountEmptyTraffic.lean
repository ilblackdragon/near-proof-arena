import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptySound

namespace ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}

theorem zero_gate_mult (ha : tr.cell tt r Acct.act=0) (hf : tr.cell tt r Acct.af=0)
    (hg : tr.cell tt r Acct.gS=0) (it : Interaction) (hit : it∈table.interactions) :
    it.multNat tr tt r pub=0 := by
  simp only [table,AcctV3.table,AcctV3.interactions,AcctV3.vpre,Acct.vbytes,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with ((rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl))|(rfl|rfl|rfl)
  all_goals simp only [send,recv,Interaction.multNat,Interaction.multNat.go,eval_c,ha,hf,hg]
  all_goals decide

theorem zero_gate_traffic (ha : tr.cell tt r Acct.act=0) (hf : tr.cell tt r Acct.af=0)
    (hg : tr.cell tt r Acct.gS=0) (b : Nat) (sd : Bool) :
    rowTraffic table.interactions tr tt r pub b sd=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro it hit
  have hm := zero_gate_mult (pub:=pub) ha hf hg it hit
  change (if it.bus=b ∧ it.send=sd then List.replicate (it.multNat tr tt r pub)
    (it.msgVal tr tt r pub) else [])=[]
  rw [hm]
  split <;> rfl

theorem empty_traffic (tt r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic table.interactions emptyTrace tt r pub b sd=[] :=
  zero_gate_traffic rfl rfl rfl b sd

/-- The candidate adds only a traffic-free empty case; all nonempty behavior
still satisfies the original table and can reuse its checked extraction. -/
theorem sound_cases {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) :
    TableLocal AcctV3.table tr tt pub ∨
      ∀r,tr.height tt>r → ∀b sd,rowTraffic table.interactions tr tt r pub b sd=[] := by
  rcases local_cases h with ho|he
  · exact Or.inl ho
  · right
    intro r hr b sd
    obtain ⟨ha,hf,hg⟩ := he r hr
    exact zero_gate_traffic ha hf hg b sd

end ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
