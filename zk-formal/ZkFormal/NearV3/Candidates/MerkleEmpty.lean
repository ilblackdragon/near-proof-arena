import ZkFormal.NearV3.Candidates.MerkleTraffic
import NearSpec.Outcome

namespace ZkFormal.NearV3.Candidates.MerkleEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

def emptyCol : Nat := 58
def inverseCol : Nat := 59
def countE : Expr := MerklePublic.expression Mrk.nPubE
def active : Expr := Dsl.not (c emptyCol)
def gate (e : Expr) : Expr := .mul active e

def interaction (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map gate}

/-- Empty trees use no Merkle/SHA traffic. The inverse distinguishes nonzero
counts; the public byte range and count bound are supplied by the whole AIR. -/
def controls : List Expr :=
  [Dsl.bool (c emptyCol), sub (n emptyCol) (c emptyCol),
   .mul (c emptyCol) countE,
   .mul active (sub (.mul countE (c inverseCol)) (k 1))] ++
  (List.range 32).map (fun i => .mul (c emptyCol) (.pub (PH_OUT+i)))

def table : Air.Table :=
  { MerklePublic.table with
    width:=60
    constraints:=controls ++ MerklePublic.table.constraints.map gate
    interactions:=MerklePublic.table.interactions.map interaction }

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem table_wf : table.wf ⟨[table],67,202⟩ 8=true := by decide +kernel

/-- Honest empty witness, with the minimum two rows. -/
def emptyTrace : Trace Fp :=
  {log:=fun _ => 1, cell:=fun _ _ x => if x=emptyCol then 1 else 0}

theorem gate_empty (tt r : Nat) (pub : List Fp) (e : Expr) :
    (gate e).eval emptyTrace tt r pub=0 := by
  simp [gate,active,Dsl.not,sub,k,c,Expr.eval,Expr.evalWith,rowEnv,emptyTrace]
  <;> grind

theorem empty_local (tt : Nat) (pub : List Fp)
    (hc : ∀ r, countE.eval emptyTrace tt r pub=0)
    (ho : ∀ i<32, pub.getD (PH_OUT+i) 0=0) :
    TableLocal table emptyTrace tt pub := by
  refine ⟨by change 1≤1; omega,by change 1≤19; omega,?_,?_⟩
  · intro r hr e he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · simp [Dsl.bool,c,sub,k,Expr.eval,Expr.evalWith,rowEnv,emptyTrace]
          <;> grind
        · simp [sub,n,c,Expr.eval,Expr.evalWith,rowEnv,emptyTrace]
          <;> grind
        · change (c emptyCol).eval emptyTrace tt r pub * countE.eval emptyTrace tt r pub=0
          rw [hc r]; grind
        · exact gate_empty tt r pub _
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
        have h := ho i (List.mem_range.mp hi)
        change (1 : Fp) * pub.getD (PH_OUT+i) 0=0
        rw [h]; grind
    · obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
      exact gate_empty tt r pub e
  · intro r hr i hi e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hi
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
    exact Or.inl (gate_empty tt r pub e)

theorem nonempty_local {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub)
    (he : ∀ r<tr.height tt, tr.cell tt r emptyCol=0) :
    TableLocal MerklePublic.table tr tt pub := by
  have hg : ∀ r, r<tr.height tt → ∀ e, (gate e).eval tr tt r pub=e.eval tr tt r pub := by
    intro r hr e
    simp [gate,active,Dsl.not,sub,k,c,Expr.eval,Expr.evalWith,rowEnv,he r hr]
    <;> grind
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e hem
    have hh := h.constr r hr (gate e) (List.mem_append_right _ (List.mem_map.mpr ⟨e,hem,rfl⟩))
    rwa [hg r hr e] at hh
  · intro r hr i hi e hem
    have hh := h.bits r hr (interaction i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
      (gate e) (List.mem_map.mpr ⟨e,hem,rfl⟩)
    rwa [hg r hr e] at hh

theorem count_zero (tt r : Nat) (pub : List Fp)
    (hn : ∀ i<4, pub.getD (PH_N+i) 0=0) :
    countE.eval emptyTrace tt r pub=0 := by
  have h0 := hn 0 (by omega)
  have h1 := hn 1 (by omega)
  have h2 := hn 2 (by omega)
  have h3 := hn 3 (by omega)
  change (Fp.ofNat 1 * pub.getD (PH_N+0) 0 +
    (Fp.ofNat 256 * pub.getD (PH_N+1) 0 +
    (Fp.ofNat 65536 * pub.getD (PH_N+2) 0 +
    (Fp.ofNat 16777216 * pub.getD (PH_N+3) 0 + Fp.ofNat 0))))=0
  rw [h0,h1,h2,h3]
  change (Fp.ofNat 1 * 0 + (Fp.ofNat 256 * 0 +
    (Fp.ofNat 65536 * 0 + (Fp.ofNat 16777216 * 0 + 0))))=0
  grind

/-- Honest completeness for the native empty root and zero receipt count. -/
theorem empty_public_local (tt : Nat) (pub : List Fp)
    (hn : ∀ i<4, pub.getD (PH_N+i) 0=0)
    (ho : ∀ i<32, pub.getD (PH_OUT+i) 0=0) :
    TableLocal table emptyTrace tt pub :=
  empty_local tt pub (fun r => count_zero tt r pub hn) ho

theorem empty_mult (tt r : Nat) (pub : List Fp) (es : List Expr) (k : Nat) :
    Interaction.multNat.go emptyTrace tt r pub (es.map gate) k=0 := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,Interaction.multNat.go,gate_empty]
    rw [ih]
    rfl

theorem empty_traffic (tt r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic table.interactions emptyTrace tt r pub b sd=[] := by
  simp only [table,rowTraffic,List.flatMap_map]
  apply List.flatMap_eq_nil_iff.mpr
  intro i hi
  change (if i.bus=b ∧ i.send=sd then
    List.replicate ((interaction i).multNat emptyTrace tt r pub)
      ((interaction i).msgVal emptyTrace tt r pub) else [])=[]
  have hm : (interaction i).multNat emptyTrace tt r pub=0 := empty_mult tt r pub i.mult 0
  rw [hm]
  split <;> rfl

theorem empty_public_root {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) {r : Nat} (hr : r<tr.height tt)
    (he : tr.cell tt r emptyCol=1) : ∀ i<32, pub.getD (PH_OUT+i) 0=0 := by
  intro i hi
  have hh := h.constr r hr (.mul (c emptyCol) (.pub (PH_OUT+i)))
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)))
  change tr.cell tt r emptyCol * pub.getD (PH_OUT+i) 0=0 at hh
  rw [he] at hh
  grind

set_option maxRecDepth 8192 in
theorem zero_count_flag {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) {r : Nat} (hr : r<tr.height tt)
    (hc : countE.eval tr tt r pub=0) : tr.cell tt r emptyCol=1 := by
  have hh := h.constr r hr (.mul active (sub (.mul countE (c inverseCol)) (k 1)))
    (List.mem_append_left _ (List.mem_append_left _ (by simp)))
  simp only [active,eval_mul,eval_sub,eval_k,eval_c,eval_not] at hh
  rw [hc] at hh
  grind

theorem zero_count_root {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) {r : Nat} (hr : r<tr.height tt)
    (hc : countE.eval tr tt r pub=0) : ∀ i<32, pub.getD (PH_OUT+i) 0=0 :=
  empty_public_root h hr (zero_count_flag h hr hc)

theorem nonzero_count_flag {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) {r : Nat} (hr : r<tr.height tt)
    (hc : countE.eval tr tt r pub≠0) : tr.cell tt r emptyCol=0 := by
  have hh := h.constr r hr (.mul (c emptyCol) countE)
    (List.mem_append_left _ (List.mem_append_left _ (by simp)))
  change tr.cell tt r emptyCol * countE.eval tr tt r pub=0 at hh
  rcases Lean.Grind.Field.of_mul_eq_zero hh with he | he
  · exact he
  · exact False.elim (hc he)

theorem nonzero_count_local {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub)
    (hc : ∀ r<tr.height tt, countE.eval tr tt r pub≠0) :
    TableLocal MerklePublic.table tr tt pub :=
  nonempty_local h (fun r hr => nonzero_count_flag h hr (hc r hr))

theorem native_empty_root : NearSpec.outcomeRoot []=NearSpec.zeroHash := rfl

end ZkFormal.NearV3.Candidates.MerkleEmpty
