import ZkFormal.NearV3.Candidates.MerkleEmpty
import ZkFormal.NearV3.Candidates.MerkleLog19

namespace ZkFormal.NearV3.Candidates.MerkleEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

theorem count_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    countE.eval tr tt r pub=countE.eval tr tt 0 pub := rfl

theorem gate_zero {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (he : tr.cell tt r emptyCol=0) (e : Expr) :
    (gate e).eval tr tt r pub=e.eval tr tt r pub := by
  simp only [gate,active,eval_mul,eval_not,eval_c,he]
  grind

theorem mult_zero {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (he : tr.cell tt r emptyCol=0) (es : List Expr) (k : Nat) :
    Interaction.multNat.go tr tt r pub (es.map gate) k=
      Interaction.multNat.go tr tt r pub es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons,Interaction.multNat.go,gate_zero he,ih]

theorem row_nonempty {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (he : tr.cell tt r emptyCol=0) (b : Nat) (sd : Bool) :
    rowTraffic table.interactions tr tt r pub b sd=
      rowTraffic MerklePublic.table.interactions tr tt r pub b sd := by
  simp only [table,rowTraffic,List.flatMap_map]
  apply flatMap_congr'
  intro i hi
  have hm : (interaction i).multNat tr tt r pub=i.multNat tr tt r pub := mult_zero he i.mult 0
  simp only [hm]
  rfl

theorem count_nonempty {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (he : ∀ r<tr.height tt, tr.cell tt r emptyCol=0) (b : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount table.interactions tr tt pub b sd m=
      tableBusCount MerklePublic.table.interactions tr tt pub b sd m := by
  simp only [tableBusCount_eq]
  congr 1
  apply flatMap_congr'
  intro r hr
  exact row_nonempty (he r (List.mem_range.mp hr)) b sd

theorem gate_one {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (he : tr.cell tt r emptyCol=1) (e : Expr) :
    (gate e).eval tr tt r pub=0 := by
  simp only [gate,active,eval_mul,eval_not,eval_c,he]
  grind

theorem mult_one {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (he : tr.cell tt r emptyCol=1) (es : List Expr) (k : Nat) :
    Interaction.multNat.go tr tt r pub (es.map gate) k=0 := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,Interaction.multNat.go,gate_one he,ih]
    rfl

theorem row_empty {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (he : tr.cell tt r emptyCol=1) (b : Nat) (sd : Bool) :
    rowTraffic table.interactions tr tt r pub b sd=[] := by
  simp only [table,rowTraffic,List.flatMap_map]
  apply List.flatMap_eq_nil_iff.mpr
  intro i hi
  have hm : (interaction i).multNat tr tt r pub=0 := mult_one he i.mult 0
  simp only [hm,List.replicate_zero]
  split <;> rfl

/-- Arbitrary accepting zero-count traces have the native empty root and no
physical Merkle traffic, without an honest-witness premise. -/
theorem empty_view {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) (hc : countE.eval tr tt 0 pub=0) :
    (∀ i<32, pub.getD (PH_OUT+i) 0=0) ∧
    (∀ b sd m, tableBusCount table.interactions tr tt pub b sd m=0) := by
  have hp : 0<tr.height tt := Nat.two_pow_pos _
  refine ⟨zero_count_root h hp hc,?_⟩
  intro b sd m
  have he : ∀ r<tr.height tt, tr.cell tt r emptyCol=1 := by
    intro r hr
    apply zero_count_flag h hr
    rwa [count_row]
  rw [tableBusCount_eq]
  have hz : (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic table.interactions tr tt r pub b sd)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    exact row_empty (he r (List.mem_range.mp hr)) b sd
  rw [hz]
  rfl

/-- Full original Merkle view/traffic extraction at log19 under v3 public fields. -/
theorem remapped_view {tr : Trace Fp} {pub : List Fp}
    (h : TableLocal MerklePublic.table tr T_MRK pub) :
    ∃ v, MrkWf (MerklePublic.aliasPublic pub) v ∧
      TableTraffic MerklePublic.table.interactions tr T_MRK pub
        (mrkTraffic (MerklePublic.aliasPublic pub) v) := by
  obtain ⟨v,hw,ht⟩ := MerkleLog19.mrk_view tr _ (MerklePublic.local_alias.mp h)
  refine ⟨v,hw,?_⟩
  intro b m
  simpa only [MerklePublic.count_alias] using ht b m

/-- The nonempty extended candidate extracts the same semantic view and exact
physical traffic, with no supplied empty-flag or honest-trace premise. -/
theorem nonempty_view {tr : Trace Fp} {pub : List Fp}
    (h : TableLocal table tr T_MRK pub)
    (hc : countE.eval tr T_MRK 0 pub≠0) :
    ∃ v, MrkWf (MerklePublic.aliasPublic pub) v ∧
      TableTraffic table.interactions tr T_MRK pub
        (mrkTraffic (MerklePublic.aliasPublic pub) v) := by
  have he : ∀ r<tr.height T_MRK, tr.cell T_MRK r emptyCol=0 := by
    intro r hr
    apply nonzero_count_flag h hr
    rwa [count_row]
  obtain ⟨v,hw,ht⟩ := remapped_view (nonempty_local h he)
  refine ⟨v,hw,?_⟩
  intro b m
  simpa only [count_nonempty he] using ht b m

end ZkFormal.NearV3.Candidates.MerkleEmpty
