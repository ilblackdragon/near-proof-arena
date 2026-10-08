import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTables
import ZkFormal.Near.Extract.BusCount

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- Exact traffic transformation: SIZE gains the authenticated count component;
all other buses and multiplicities are unchanged. -/
theorem rowTraffic_withCount {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]
    (is : List Interaction) (e : Expr) (tr : Trace F) (t r : Nat) (pub : List F)
    (b : Nat) (side : Bool) :
    rowTraffic (is.map (withCount e)) tr t r pub b side=
      (rowTraffic is tr t r pub b side).map
        (fun msg => if b=B_SIZE then msg++[e.eval tr t r pub] else msg) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,rowTraffic,List.flatMap_cons,List.map_append] at ih ⊢
    rw [ih]
    congr 1
    by_cases hb : i.bus=B_SIZE <;> by_cases hbi : i.bus=b <;>
      by_cases hs : i.send=side <;>
      simp [withCount,hb,hbi,hs,Interaction.multNat,Interaction.msgVal,List.map_append,
        List.map_replicate] <;> simp_all

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
