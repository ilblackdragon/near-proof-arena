import ZkFormal.NearV3.Assembly.SourceSchedulerShaOk
import ZkFormal.Sha.Complete.All
import ZkFormal.Near.Extract.Common

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Each table index renders its assigned messages independently inside one trace.
This is not proof composition; all tables share the same byte/digest buses. -/
def shaBinTrace (bins : List (List Sha.Gen.Msg)) : Trace Fp :=
  ⟨fun t => Sha.Gen.honestLog (bins.getD t []),
    fun t r c => Fp.ofNat (Sha.Gen.honestCell (bins.getD t []) r c)⟩

def shaBinTraffic (ms : List Sha.Gen.Msg) : Traffic :=
  ⟨fun b => if b=B_DIGEST then Sha.Gen.expectedDigests ms else [],
   fun b => if b=B_BYTES then Sha.Gen.expectedBytes ms else []⟩

theorem shaBin_local (bins : List (List Sha.Gen.Msg)) (t : Nat) (pub : List Fp)
    (hok : Sha.MsgsOk (bins.getD t [])) :
    TableLocal (Sha.Table.table B_BYTES B_DIGEST) (shaBinTrace bins) t pub := by
  obtain ⟨hL,hB,_⟩ := Sha.Complete.sha_complete_closed _ hok t pub
  refine ⟨hL.log_ge,hL.log_le,?_,?_⟩
  · intro r hr e he
    exact hL.constr r hr e he
  · intro r hr i hi b hb
    exact hB r hr B_BYTES B_DIGEST i hi b hb

private theorem sha_only_buses (i : Interaction)
    (hi : i∈Sha.Table.interactions B_BYTES B_DIGEST) : i.bus=B_BYTES ∨ i.bus=B_DIGEST := by
  simp only [Sha.Table.interactions,List.mem_append,List.mem_map,List.mem_range,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with ⟨q,_,rfl⟩|rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem off_bus (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (m : List Fp) (h : ∀i∈is,i.bus≠bus) :
    tableBusCount is tr t pub bus sd m=0 := by
  simp only [tableBusCount]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldr_cons,ih]
    clear ih
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [List.foldr_cons,ih (fun j hj=>h j (List.mem_cons_of_mem _ hj))]
      have hh := h i (List.mem_cons_self ..)
      simp [hh]

private theorem bin_eval (bins : List (List Sha.Gen.Msg)) (t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (shaBinTrace bins) t r pub=e.eval (Sha.honestTrace (bins.getD t [])) t r pub := by
  rfl

private theorem bin_mult (bins : List (List Sha.Gen.Msg)) (t r : Nat) (pub : List Fp)
    (i : Interaction) : i.multNat (shaBinTrace bins) t r pub=
      i.multNat (Sha.honestTrace (bins.getD t [])) t r pub := by
  unfold Interaction.multNat
  generalize 0=k
  induction i.mult generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [Interaction.multNat.go,bin_eval,ih]

private theorem bin_msg (bins : List (List Sha.Gen.Msg)) (t r : Nat) (pub : List Fp)
    (i : Interaction) : i.msgVal (shaBinTrace bins) t r pub=
      i.msgVal (Sha.honestTrace (bins.getD t [])) t r pub := by
  simp only [Interaction.msgVal,bin_eval]

private theorem bin_count (bins : List (List Sha.Gen.Msg)) (t : Nat) (pub : List Fp)
    (is : List Interaction) (b : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount is (shaBinTrace bins) t pub b sd m =
    tableBusCount is (Sha.honestTrace (bins.getD t [])) t pub b sd m := by
  simp only [tableBusCount,bin_mult,bin_msg]
  rfl

theorem shaBin_traffic (bins : List (List Sha.Gen.Msg)) (t : Nat) (pub : List Fp)
    (hok : Sha.MsgsOk (bins.getD t [])) :
    TableTraffic (Sha.Table.interactions B_BYTES B_DIGEST) (shaBinTrace bins) t pub
      (shaBinTraffic (bins.getD t [])) := by
  have hT := Sha.Complete.trafficStmt _ hok t pub B_BYTES B_DIGEST (by decide)
  intro b m
  rw [bin_count,bin_count]
  by_cases hb : b=B_BYTES
  · subst b
    obtain ⟨h1,h2,_,_⟩ := hT m
    exact ⟨h2,h1⟩
  · by_cases hd : b=B_DIGEST
    · subst b
      obtain ⟨_,_,h3,h4⟩ := hT m
      exact ⟨h3,h4⟩
    · have hoff : ∀i∈Sha.Table.interactions B_BYTES B_DIGEST,i.bus≠b := by
        intro i hi
        rcases sha_only_buses i hi with hh|hh <;> rw [hh] <;> omega
      simp only [shaBinTraffic,hb,hd,ite_false,List.map_nil,List.count_nil]
      exact ⟨off_bus _ _ _ _ _ _ _ hoff,off_bus _ _ _ _ _ _ _ hoff⟩

end ZkFormal.NearV3.Assembly
