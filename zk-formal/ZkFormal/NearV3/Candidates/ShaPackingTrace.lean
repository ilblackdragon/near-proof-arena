import ZkFormal.NearV3.Candidates.ShaCarryKinds
import ZkFormal.Near.Extract.Common

namespace ZkFormal.NearV3.Candidates.ShaPackingTrace
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 32768

def carryCell (f : Nat → Fp) (i : Nat) : Fp :=
  if i<384 then f i
  else if i<456 then
    let j:=i-384
    let x:=f (384+2*(j/3))
    if j%3=0 then ShaCarryPairs.decodeLow x
    else if j%3=1 then ShaCarryPairs.decodeHigh x
    else f (385+2*(j/3))
  else f (i-24)

def kindCell (f : Nat → Fp) (i : Nat) : Fp :=
  if i<478 then f i
  else if i<494 then
    let j:=i-478
    let x:=f (478+j/2)
    if j%2=0 then ShaCarryPairs.decodeLow x else ShaCarryPairs.decodeHigh x
  else f (i-8)

def carryTrace (tr : Trace Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r => carryCell (tr.cell t r)}
def kindTrace (tr : Trace Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r => kindCell (tr.cell t r)}
def decodeTrace (tr : Trace Fp) : Trace Fp := carryTrace (kindTrace tr)

theorem carry_column_eval (tr : Trace Fp) (t r i : Nat) (pub : List Fp) (nx : Bool) :
    (ShaCarryPairs.column i nx).eval tr t r pub =
      carryCell (tr.cell t (if nx then (r+1)%tr.height t else r)) i := by
  unfold ShaCarryPairs.column carryCell
  repeat' first
    | split
    | simp_all [Expr.eval,Expr.evalWith,rowEnv,ShaCarryPairs.low,
        ShaCarryPairs.high,ShaCarryPairs.decodeLow,ShaCarryPairs.decodeHigh,
        ShaCarryPairs.scalarEnv,ZkFormal.Sha.Table.E.smul,ZkFormal.Sha.Table.E.sub,
        ZkFormal.Sha.Table.E.k]

theorem kind_column_eval (tr : Trace Fp) (t r i : Nat) (pub : List Fp) (nx : Bool) :
    (ShaCarryKinds.column i nx).eval tr t r pub =
      kindCell (tr.cell t (if nx then (r+1)%tr.height t else r)) i := by
  unfold ShaCarryKinds.column kindCell
  repeat' first
    | split
    | simp_all [Expr.eval,Expr.evalWith,rowEnv,ShaCarryPairs.low,
        ShaCarryPairs.high,ShaCarryPairs.decodeLow,ShaCarryPairs.decodeHigh,
        ShaCarryPairs.scalarEnv,ZkFormal.Sha.Table.E.smul,ZkFormal.Sha.Table.E.sub,
        ZkFormal.Sha.Table.E.k]

theorem carry_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) :
    (ShaCarryPairs.expression e).eval tr t r pub = e.eval (carryTrace tr) t r pub := by
  unfold Expr.eval
  rw [ShaCarryPairs.expression_eval]
  congr 1
  congr 1
  funext i nx
  exact carry_column_eval tr t r i pub nx

theorem kind_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) :
    (ShaCarryKinds.expression e).eval tr t r pub = e.eval (kindTrace tr) t r pub := by
  unfold Expr.eval
  rw [ShaCarryKinds.expression_eval]
  congr 1
  congr 1
  funext i nx
  exact kind_column_eval tr t r i pub nx

theorem original_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) :
    (ShaCarryKinds.expression (ShaCarryPairs.expression e)).eval tr t r pub =
      e.eval (decodeTrace tr) t r pub := by
  rw [kind_eval,carry_eval]
  rfl

/-- Physical local soundness at unchanged height, including multiplicity bits. -/
theorem decode_local {tr : Trace Fp} {t bb bd : Nat} {pub : List Fp}
    (h : TableLocal (ShaCarryKinds.table bb bd) tr t pub) :
    TableLocal (ZkFormal.Sha.Table.table bb bd) (decodeTrace tr) t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rw [← original_eval]
    apply h.constr r hr
    exact List.mem_map.mpr ⟨ShaCarryPairs.expression e,
      List.mem_map.mpr ⟨e,he,rfl⟩,rfl⟩
  · intro r hr i hi b hb
    have hi' : ShaCarryKinds.interaction (ShaCarryPairs.interaction i) ∈
        (ShaCarryKinds.table bb bd).interactions :=
      List.mem_map.mpr ⟨ShaCarryPairs.interaction i,List.mem_map.mpr ⟨i,hi,rfl⟩,rfl⟩
    have hb' : ShaCarryKinds.expression (ShaCarryPairs.expression b) ∈
        (ShaCarryKinds.interaction (ShaCarryPairs.interaction i)).mult :=
      List.mem_map.mpr ⟨ShaCarryPairs.expression b,List.mem_map.mpr ⟨b,hb,rfl⟩,rfl⟩
    simpa only [original_eval] using h.bits r hr _ hi' _ hb'

theorem mult_go (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bs : List Expr) (k : Nat) :
    Interaction.multNat.go tr t r pub
      (bs.map (fun e => ShaCarryKinds.expression (ShaCarryPairs.expression e))) k =
    Interaction.multNat.go (decodeTrace tr) t r pub bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,Interaction.multNat.go,original_eval,ih]

theorem interaction_mult (tr : Trace Fp) (t r : Nat) (pub : List Fp) (i : Interaction) :
    (ShaCarryKinds.interaction (ShaCarryPairs.interaction i)).multNat tr t r pub =
    i.multNat (decodeTrace tr) t r pub := by
  simp only [Interaction.multNat,ShaCarryKinds.interaction,ShaCarryPairs.interaction,
    List.map_map,Function.comp_def,mult_go]

/-- Exact full physical bus traffic, including all padding and cyclic rows. -/
theorem table_traffic (tr : Trace Fp) (t bb bd bus : Nat) (pub m : List Fp) (send : Bool) :
    tableBusCount (ShaCarryKinds.table bb bd).interactions tr t pub bus send m =
    tableBusCount (ZkFormal.Sha.Table.table bb bd).interactions
      (decodeTrace tr) t pub bus send m := by
  simp only [ShaCarryKinds.table,ShaCarryPairs.table,ZkFormal.Sha.Table.table,
    tableBusCount,List.foldr_map,interaction_mult]
  simp only [Interaction.msgVal,ShaCarryKinds.interaction,ShaCarryPairs.interaction,
    List.map_map,Function.comp_def,original_eval]
  rfl

end ZkFormal.NearV3.Candidates.ShaPackingTrace
