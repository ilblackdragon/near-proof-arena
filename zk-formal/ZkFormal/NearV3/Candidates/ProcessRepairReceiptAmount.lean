import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemoryOrder
import ZkFormal.Near.Link.Run
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptAmount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Link
open ProcessRepairReceiptMemoryOrder (mem_read)

def writeAmount (rs:RcptVs) (a:AcctV) (t:Nat):Nat:=
  if t=0 then leN' (a.pre.take 16) else leN' (rs.getD (t-1) default).aft

def amountAt (rs:RcptVs) (a:AcctV):Nat→Nat
  | 0=>leN' (a.pre.take 16)
  | r+1=>amountAt rs a r + if ksl rs r=a.k then leN' (rs.getD r default).dep else 0

variable {pub:List Fp} {rs:RcptVs} {as:List AcctV}
  (h:ProcessRepairReceiptMemoryOrder.Context pub rs as)
  (initial:∀a∈as,a.pre.length=72)
  (lens:∀r,(hr:r<rs.length)→rs[r].bef.length=16 ∧ rs[r].aft.length=16)
include h initial lens
theorem before {r : Nat} (hr : r < rs.length) {a : AcctV} (ha : a ∈ as) (hk : a.k = rs[r].kslot) :
    leN' rs[r].bef = writeAmount rs a (lastW (ksl rs) a.k r) := by
  have hnd := h.unique
  have l6 := (lens r hr).1
  have hl := initial a ha
  rw [hk]
  rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, -, -, e⟩
  · rw [e]; simp only [writeAmount, if_true]
    congr 1
    apply ext16 l6 (by simp [hl])
    intro i hi
    obtain ⟨b, hb, hbk, he⟩ := (mem_read h hr hi).1 e
    have : b = a := by
      have := (acctOf_eq hnd hb).symm.trans ((hbk.trans hk.symm) ▸ acctOf_eq hnd ha)
      simpa using this
    subst this
    simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [writeAmount, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨hr0, -, -, -⟩ := (mem_read h hr (i := 0) (by decide)).2 r0 e
    have l9 := (lens r0 hr0).2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr0, Option.getD_some]
    congr 1
    apply ext16 l6 l9
    intro i hi
    obtain ⟨_, -, -, he2⟩ := (mem_read h hr hi).2 r0 e
    simp only [rdMsg, wrMsg, List.cons.injEq] at he2
    exact he2.2.2.2.1


theorem invariant (adds:∀r,(hr:r<rs.length)→leN' rs[r].aft=leN' rs[r].bef+leN' rs[r].dep)
    {a:AcctV} (ha:a∈as):∀r,r≤rs.length→amountAt rs a r=writeAmount rs a (lastW (ksl rs) a.k r)
  | 0,_=>by simp only [amountAt,lastW,writeAmount,if_true]
  | r+1,hr=>by
    have ih:=invariant adds ha r (by omega)
    simp only [amountAt,lastW]
    rw [ih]
    split
    · next hk=>
      have hr':r<rs.length:=by omega
      rw [←before h initial lens hr' ha (by rw [←hk,ksl_eq hr'])]
      simp only [writeAmount,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,
        List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr',Option.getD_some]
      rw [adds r hr']
    · next hk=>simp [hk]

theorem current (adds:∀r,(hr:r<rs.length)→leN' rs[r].aft=leN' rs[r].bef+leN' rs[r].dep)
    {a:AcctV} (ha:a∈as) {r:Nat} (hr:r<rs.length) (hk:a.k=rs[r].kslot):
    amountAt rs a r=leN' rs[r].bef:=by
  rw [invariant h initial lens adds ha r (by omega),before h initial lens hr ha hk]
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptAmount
