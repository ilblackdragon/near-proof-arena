import ZkFormal.NearV3.Candidates.ShaPackingTrace
import ZkFormal.Near.Extract.Eval

namespace ZkFormal.NearV3.Candidates.ShaPackingEncode
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ShaPackingTrace
set_option maxRecDepth 32768

def carryCell (f : Nat → Fp) (i : Nat) : Fp :=
  if i<384 then f i
  else if i<432 then
    let j:=i-384
    if j%2=0 then f (384+3*(j/2))+2*f (385+3*(j/2))
    else f (386+3*(j/2))
  else f (i+24)

def kindCell (f : Nat → Fp) (i : Nat) : Fp :=
  if i<478 then f i
  else if i<486 then
    let j:=i-478
    f (478+2*j)+2*f (479+2*j)
  else f (i+8)

theorem carry_triplet (f : Nat → Fp) (j : Nat) (hj : j<24)
    (h0 : f (384+3*j)=0 ∨ f (384+3*j)=1)
    (h1 : f (385+3*j)=0 ∨ f (385+3*j)=1) :
    ShaPackingTrace.carryCell (carryCell f) (384+3*j)=f (384+3*j) ∧
    ShaPackingTrace.carryCell (carryCell f) (385+3*j)=f (385+3*j) ∧
    ShaPackingTrace.carryCell (carryCell f) (386+3*j)=f (386+3*j) := by
  have hd := ShaCarryPairs.pair_decode _ _ h0 h1
  have div0 : (384+3*j-384)/3=j := by omega
  have div1 : (385+3*j-384)/3=j := by omega
  have div2 : (386+3*j-384)/3=j := by omega
  have mod0 : (384+3*j-384)%3=0 := by omega
  have mod1 : (385+3*j-384)%3=1 := by omega
  have mod2 : (386+3*j-384)%3=2 := by omega
  have div3 : (384+2*j-384)/2=j := by omega
  have div4 : (385+2*j-384)/2=j := by omega
  have mod3 : (384+2*j-384)%2=0 := by omega
  have mod4 : (385+2*j-384)%2=1 := by omega
  have bounds : ¬384+3*j<384 ∧ ¬385+3*j<384 ∧ ¬386+3*j<384 ∧
      384+3*j<456 ∧ 385+3*j<456 ∧ 386+3*j<456 ∧
      ¬384+2*j<384 ∧ ¬385+2*j<384 ∧ 384+2*j<432 ∧ 385+2*j<432 := by omega
  rcases bounds with ⟨a,b,c,d,e,g,h,i,k,l⟩
  simp [ShaPackingTrace.carryCell,carryCell,div0,div1,div2,
    mod0,mod1,mod2,div3,div4,mod3,mod4,hd.1,hd.2,a,b,c,d,e,g,h,i,k,l]

theorem kind_pair (f : Nat → Fp) (j : Nat) (hj : j<8)
    (h0 : f (478+2*j)=0 ∨ f (478+2*j)=1)
    (h1 : f (479+2*j)=0 ∨ f (479+2*j)=1) :
    ShaPackingTrace.kindCell (kindCell f) (478+2*j)=f (478+2*j) ∧
    ShaPackingTrace.kindCell (kindCell f) (479+2*j)=f (479+2*j) := by
  have hd := ShaCarryPairs.pair_decode _ _ h0 h1
  have div0 : (478+2*j-478)/2=j := by omega
  have div1 : (479+2*j-478)/2=j := by omega
  have mod0 : (478+2*j-478)%2=0 := by omega
  have mod1 : (479+2*j-478)%2=1 := by omega
  have bounds : ¬478+2*j<478 ∧ ¬479+2*j<478 ∧ 478+2*j<494 ∧
      479+2*j<494 ∧ ¬478+j<478 ∧ 478+j<486 := by omega
  rcases bounds with ⟨a,b,c,d,e,g⟩
  simpa [ShaPackingTrace.kindCell,kindCell,div0,div1,mod0,mod1,a,b,c,d,e,g] using hd
theorem carry_roundtrip (f : Nat → Fp)
    (h : ∀j<24,(f (384+3*j)=0 ∨ f (384+3*j)=1) ∧
      (f (385+3*j)=0 ∨ f (385+3*j)=1)) (i : Nat) :
    ShaPackingTrace.carryCell (carryCell f) i=f i := by
  by_cases h0 : i<384
  · simp [ShaPackingTrace.carryCell,carryCell,h0]
  by_cases h1 : i<456
  · let j:=(i-384)/3
    have hj : j<24 := by dsimp [j]; omega
    have ht:=carry_triplet f j hj (h j hj).1 (h j hj).2
    have hi : i=384+3*j ∨ i=385+3*j ∨ i=386+3*j := by dsimp [j]; omega
    rcases hi with hi | hi | hi
    · simpa only [hi] using ht.1
    · simpa only [hi] using ht.2.1
    · simpa only [hi] using ht.2.2
  · have h2 : ¬i-24<384 := by omega
    have h3 : ¬i-24<432 := by omega
    simp [ShaPackingTrace.carryCell,carryCell,h0,h1,h2,h3,show i-24+24=i by omega]

theorem kind_roundtrip (f : Nat → Fp)
    (h : ∀j<8,(f (478+2*j)=0 ∨ f (478+2*j)=1) ∧
      (f (479+2*j)=0 ∨ f (479+2*j)=1)) (i : Nat) :
    ShaPackingTrace.kindCell (kindCell f) i=f i := by
  by_cases h0 : i<478
  · simp [ShaPackingTrace.kindCell,kindCell,h0]
  by_cases h1 : i<494
  · let j:=(i-478)/2
    have hj : j<8 := by dsimp [j]; omega
    have ht:=kind_pair f j hj (h j hj).1 (h j hj).2
    have hi : i=478+2*j ∨ i=479+2*j := by dsimp [j]; omega
    rcases hi with hi | hi
    · simpa only [hi] using ht.1
    · simpa only [hi] using ht.2
  · have h2 : ¬i-8<478 := by omega
    have h3 : ¬i-8<486 := by omega
    simp [ShaPackingTrace.kindCell,kindCell,h0,h1,h2,h3,show i-8+8=i by omega]

/-- Actual512-column encoder, preserving table heights and row positions. -/
def encodeTrace (tr : Trace Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r => kindCell (carryCell (tr.cell t r))}

theorem local_bool {tr : Trace Fp} {t bb bd r i : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub)
    (hr : r<tr.height t) (hi : i∈ZkFormal.Sha.Layout.boolCols) :
    tr.cell t r i=0 ∨ tr.cell t r i=1 := by
  have hm : ZkFormal.Sha.Table.boolC i ∈ ZkFormal.Sha.Table.constraints := by
    simp only [ZkFormal.Sha.Table.constraints,List.mem_append]
    left; left; left; left; left; left; left
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  have hc:=h.constr r hr _ hm
  change tr.cell t r i * (tr.cell t r i + -(1:Fp))=0 at hc
  apply bool_cases
  have eqn (x : Fp) : x*(x-1)=x*(x+ -1) := by grind
  rw [eqn]
  exact hc

theorem local_bool_range {tr : Trace Fp} {t bb bd r i : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub)
    (hr : r<tr.height t) (hi : i<456 ∨ (502≤i ∧ i<536)) :
    tr.cell t r i=0 ∨ tr.cell t r i=1 := by
  apply local_bool h hr
  simp only [ZkFormal.Sha.Layout.boolCols,List.mem_append,List.mem_range,List.mem_range'_1,
    List.mem_cons,List.mem_singleton]
  omega

/-- Every original cell on every physical row is recovered exactly. -/
theorem cell_roundtrip {tr : Trace Fp} {t bb bd r : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub)
    (hr : r<tr.height t) (i : Nat) :
    (decodeTrace (encodeTrace tr)).cell t r i=tr.cell t r i := by
  have hc : ∀j<24,(tr.cell t r (384+3*j)=0 ∨ tr.cell t r (384+3*j)=1) ∧
      (tr.cell t r (385+3*j)=0 ∨ tr.cell t r (385+3*j)=1) := by
    intro j hj
    exact ⟨local_bool_range h hr (by omega),local_bool_range h hr (by omega)⟩
  have hk : ∀j<8,(carryCell (tr.cell t r) (478+2*j)=0 ∨
      carryCell (tr.cell t r) (478+2*j)=1) ∧
      (carryCell (tr.cell t r) (479+2*j)=0 ∨ carryCell (tr.cell t r) (479+2*j)=1) := by
    intro j hj
    have h0:=local_bool_range h hr (i:=478+2*j+24) (by omega)
    have h1:=local_bool_range h hr (i:=479+2*j+24) (by omega)
    have b0 : ¬478+2*j<384 ∧ ¬478+2*j<432 ∧ ¬479+2*j<384 ∧ ¬479+2*j<432 := by omega
    simpa only [carryCell,if_neg b0.1,if_neg b0.2.1,if_neg b0.2.2.1,
      if_neg b0.2.2.2] using And.intro h0 h1
  have he : (fun j => ShaPackingTrace.kindCell
      (kindCell (carryCell (tr.cell t r))) j)=carryCell (tr.cell t r) :=
    funext (kind_roundtrip _ hk)
  change ShaPackingTrace.carryCell
    (fun j => ShaPackingTrace.kindCell (kindCell (carryCell (tr.cell t r))) j) i=tr.cell t r i
  rw [he]
  exact carry_roundtrip _ hc i

theorem eval_roundtrip {tr : Trace Fp} {t bb bd r : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub)
    (hr : r<tr.height t) (e : Expr) :
    e.eval (decodeTrace (encodeTrace tr)) t r pub=e.eval tr t r pub := by
  unfold Expr.eval rowEnv
  congr 1
  congr 1
  funext i nx
  apply cell_roundtrip h
  cases nx
  · exact hr
  · exact Nat.mod_lt _ (by change 0<tr.height t; omega)

/-- Every honest original physical SHA table packs at the same height. -/
theorem encode_local {tr : Trace Fp} {t bb bd : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub) :
    TableLocal (ShaCarryKinds.table bb bd) (encodeTrace tr) t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rcases List.mem_map.mp he with ⟨e0,he0,rfl⟩
    rcases List.mem_map.mp he0 with ⟨e1,he1,rfl⟩
    rw [ShaPackingTrace.original_eval,eval_roundtrip h hr]
    exact h.constr r hr e1 he1
  · intro r hr i hi b hb
    rcases List.mem_map.mp hi with ⟨i0,hi0,rfl⟩
    rcases List.mem_map.mp hi0 with ⟨i1,hi1,rfl⟩
    rcases List.mem_map.mp hb with ⟨b0,hb0,rfl⟩
    rcases List.mem_map.mp hb0 with ⟨b1,hb1,rfl⟩
    simpa only [ShaPackingTrace.original_eval,eval_roundtrip h hr] using h.bits r hr i1 hi1 b1 hb1

theorem mult_roundtrip {tr : Trace Fp} {t bb bd r : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub)
    (hr : r<tr.height t) (i : Interaction) :
    i.multNat (decodeTrace (encodeTrace tr)) t r pub=i.multNat tr t r pub := by
  unfold Interaction.multNat
  generalize 0=k
  induction i.mult generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [Interaction.multNat.go,eval_roundtrip h hr,ih]

theorem foldr_congr_mem {A B : Type} (xs : List A) (f g : A → B → B)
    (h : ∀x∈xs,∀a,f x a=g x a) (a : B) : xs.foldr f a=xs.foldr g a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons,List.foldr_cons,ih (by intro y hy; exact h y (by simp [hy])),
      h x (by simp)]

/-- Honest encoding preserves exact bus counts, not just local legality. -/
theorem encode_traffic {tr : Trace Fp} {t bb bd : Nat} {pub : List Fp}
    (h : TableLocal (ZkFormal.Sha.Table.table bb bd) tr t pub)
    (bus : Nat) (send : Bool) (m : List Fp) :
    tableBusCount (ShaCarryKinds.table bb bd).interactions
      (encodeTrace tr) t pub bus send m =
    tableBusCount (ZkFormal.Sha.Table.table bb bd).interactions tr t pub bus send m := by
  rw [ShaPackingTrace.table_traffic]
  unfold tableBusCount
  apply foldr_congr_mem
  intro r hr acc
  have hr' : r<tr.height t := List.mem_range.mp hr
  simp only [Interaction.msgVal,eval_roundtrip h hr',mult_roundtrip h hr']
  rfl

end ZkFormal.NearV3.Candidates.ShaPackingEncode
