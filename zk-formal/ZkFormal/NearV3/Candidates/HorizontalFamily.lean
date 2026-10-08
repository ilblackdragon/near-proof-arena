import ZkFormal.NearV3.Candidates.HorizontalProjection
import ZkFormal.NearV3.Candidates.HorizontalInventory

namespace ZkFormal.NearV3.Candidates.HorizontalFamily
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- Reindex a physical table without changing its clock or cells. -/
def focus (tr : Trace Fp) (t : Nat) : Trace Fp :=
  {log:=fun _=>tr.log t,cell:=fun _=>tr.cell t}

theorem focus_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (focus tr t) 0 r pub=e.eval tr t r pub := rfl

theorem focus_local {T : Air.Table} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal T tr t pub) : TableLocal T (focus tr t) 0 pub := by
  exact ⟨h.log_ge,h.log_le,h.constr,h.bits⟩

theorem focus_count (tr : Trace Fp) (t : Nat) (pub : List Fp) (is : List Interaction)
    (b : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount is (focus tr t) 0 pub b sd m=tableBusCount is tr t pub b sd m := by
  have hm : ∀r es k,Interaction.multNat.go (focus tr t) 0 r pub es k=
      Interaction.multNat.go tr t r pub es k := by
    intro r es k
    induction es generalizing k with
    | nil => rfl
    | cons e es ih => simp only [Interaction.multNat.go,focus_eval,ih]; rfl
  have hi : ∀i : Interaction,∀r,i.multNat (focus tr t) 0 r pub=i.multNat tr t r pub :=
    fun i r=>hm r i.mult 0
  have hv : ∀i : Interaction,∀r,i.msgVal (focus tr t) 0 r pub=i.msgVal tr t r pub := by
    intro i r
    apply List.map_congr_left
    intro e he
    rfl
  simp only [tableBusCount,hi,hv]
  rfl

/-- Separate physical tables, each reindexed at zero for component extractors. -/
def parts (tr : Trace Fp) : Nat→List Air.Table→List (Air.Table×Trace Fp)
  | _,[]=>[]
  | t,T::ts=>(T,focus tr t)::parts tr (t+1) ts

def count (xs : List (Air.Table×Trace Fp)) (pub : List Fp) (b : Nat) (sd : Bool) (m : List Fp) : Nat :=
  (xs.map (fun x=>tableBusCount x.1.interactions x.2 0 pub b sd m)).sum

theorem parts_tables (tr : Trace Fp) (t : Nat) (ts : List Air.Table) :
    (parts tr t ts).map Prod.fst=ts := by
  induction ts generalizing t with
  | nil => rfl
  | cons T ts ih => simp [parts,ih]

theorem parts_count (tr : Trace Fp) (t : Nat) (ts : List Air.Table)
    (pub : List Fp) (b : Nat) (sd : Bool) (m : List Fp) :
    count (parts tr t ts) pub b sd m=busCount.go tr pub b sd m ts t := by
  induction ts generalizing t with
  | nil => rfl
  | cons T ts ih => simp [count,parts,busCount.go,focus_count,←ih]

/-- Extract the fused block and retain all separately clocked tables. -/
def components (tr : Trace Fp) (ts rest : List Air.Table) : List (Air.Table×Trace Fp) :=
  HorizontalProjection.split (focus tr 0) 0 ts++parts tr 1 rest

theorem component_tables (tr : Trace Fp) (ts rest : List Air.Table) :
    (components tr ts rest).map Prod.fst=ts++rest := by
  simp [components,List.map_append,HorizontalProjection.split_tables,parts_tables]

/-- Exact global multiplicities survive extraction from the physical family. -/
theorem component_count (tr : Trace Fp) (ts rest : List Air.Table)
    (pub : List Fp) (b : Nat) (sd : Bool) (m : List Fp) (nb np : Nat) :
    count (components tr ts rest) pub b sd m=
      busCount (⟨HorizontalTables.fuse ts::rest,nb,np⟩ : Air) tr pub b sd m := by
  simp only [components,count,List.map_append,List.sum_append]
  rw [←HorizontalProjection.fused_count]
  rw [focus_count]
  have hp := parts_count tr 1 rest pub b sd m
  exact congrArg (fun n=>tableBusCount (HorizontalTables.fuse ts).interactions tr 0 pub b sd m+n) hp

/-- AIR balance transfers to the complete component inventory, without a
caller-supplied ownership or message-disjointness premise. -/
theorem component_balance {tr : Trace Fp} {ts rest : List Air.Table} {pub : List Fp}
    {nb np : Nat} (h : Holds (⟨HorizontalTables.fuse ts::rest,nb,np⟩ : Air) pub tr)
    (b : Nat) (m : List Fp) :
    count (components tr ts rest) pub b true m=count (components tr ts rest) pub b false m := by
  rw [component_count tr ts rest pub b true m nb np,component_count tr ts rest pub b false m nb np]
  exact h.balance b m

theorem parts_local (tr : Trace Fp) (t : Nat) (ts : List Air.Table) (pub : List Fp)
    (h : ∀i (hi : i<ts.length),TableLocal ts[i] tr (t+i) pub) :
    ∀x∈parts tr t ts,TableLocal x.1 x.2 0 pub := by
  induction ts generalizing t with
  | nil => simp [parts]
  | cons T ts ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · have hh := h 0 (by simp)
      change TableLocal T tr (t+0) pub at hh
      rw [Nat.add_zero] at hh
      exact focus_local hh
    · apply ih (t+1) _ x hx
      intro i hi
      have hh := h (i+1) (by simpa using hi)
      change TableLocal ts[i] tr (t+(i+1)) pub at hh
      simpa only [Nat.add_assoc,Nat.add_comm 1] using hh

/-- Local constraints of all original components follow from physical AIR
validity; separate-table clocks are retained without padding. -/
theorem component_local {tr : Trace Fp} {ts rest : List Air.Table} {pub : List Fp}
    {nb np : Nat} (hc : ∀T∈ts,T.maxLog=22)
    (h : Holds (⟨HorizontalTables.fuse ts::rest,nb,np⟩ : Air) pub tr) :
    ∀x∈components tr ts rest,TableLocal x.1 x.2 0 pub := by
  have hf : TableLocal (HorizontalTables.fuse ts) tr 0 pub :=
    ⟨(h.logBound 0 (by simp)).1,(h.logBound 0 (by simp)).2,
      h.constr 0 (by simp),h.bits 0 (by simp)⟩
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact HorizontalProjection.fused_local ts (focus tr 0) 0 pub hc (focus_local hf) x hx
  · apply parts_local tr 1 rest pub _ x hx
    intro i hi
    have hg : i+1<(HorizontalTables.fuse ts::rest).length := by simp; omega
    have ht : TableLocal ((HorizontalTables.fuse ts::rest)[i+1]) tr (i+1) pub :=
      ⟨(h.logBound (i+1) hg).1,(h.logBound (i+1) hg).2,
        h.constr (i+1) hg,h.bits (i+1) hg⟩
    simpa only [List.getElem_cons_succ,Nat.add_comm 1] using ht

/-- Complete local and global decomposition of the admitted physical candidate. -/
theorem candidate_components {tr : Trace Fp} {pub : List Fp}
    (h : Holds HorizontalAccounts.air pub tr) :
    let xs := components tr HorizontalTables.selected HorizontalAccounts.rest
    xs.map Prod.fst=HorizontalTables.selected++HorizontalAccounts.rest ∧
    (∀x∈xs,TableLocal x.1 x.2 0 pub) ∧
    (∀b m,count xs pub b true m=count xs pub b false m) := by
  refine ⟨component_tables _ _ _,component_local ?_ h,component_balance h⟩
  intro T hT
  exact of_decide_eq_true (List.mem_filter.mp hT).2

theorem candidate_inventory (tr : Trace Fp) :
    ((components tr HorizontalTables.selected HorizontalAccounts.rest).map Prod.fst).Perm
      HorizontalInventory.original := by
  rw [component_tables]
  exact HorizontalInventory.partition

end ZkFormal.NearV3.Candidates.HorizontalFamily
